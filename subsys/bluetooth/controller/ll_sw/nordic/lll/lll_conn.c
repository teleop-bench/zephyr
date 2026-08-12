/*
 * Copyright (c) 2018-2020 Nordic Semiconductor ASA
 *
 * SPDX-License-Identifier: Apache-2.0
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#include <zephyr/toolchain.h>
#include <soc.h>

#include <zephyr/sys/util.h>

#include "hal/cpu.h"
#include "hal/ccm.h"
#include "hal/radio.h"
#include "hal/radio_df.h"

#include "util/util.h"
#include "util/mem.h"
#include "util/memq.h"
#include "util/mfifo.h"
#include "util/dbuf.h"

#include "pdu_df.h"
#include "pdu_vendor.h"
#include "pdu.h"

#include "lll.h"
#include "lll_clock.h"
#include "lll_df_types.h"
#include "lll_df.h"
#include "lll_conn.h"

/* Q2 diagnostic (zephyr-patches/q2-print-conn-params.patch): per-data-channel
 * per-channel DENOMINATOR counter, ROLE-DEPENDENT meaning: central = actual TX
 * completion (isr_tx); peripheral = CRC-good response-opportunity (isr_rx). Per
 * channel. The app prints it so the observer has a NON-circular retention
 * denominator (events the observer never saw still count here). */
volatile uint32_t lll_conn_q2_evt[40];   /* SCHEDULED opportunities/chan */
volatile uint32_t lll_conn_q2_tx[40];    /* ACTUAL TX-completed pkts/chan */
volatile uint32_t lll_conn_q2_session;   /* controller-owned, ++ per connect setup */
volatile uint32_t lll_conn_q2_aa;        /* connection AA = shared id (both roles) */
volatile uint8_t  lll_conn_q2_curchan = 255; /* ACTUAL remapped chan this event */

#include "lll_internal.h"
#include "lll_df_internal.h"
#include "lll_tim_internal.h"
#include "lll_prof_internal.h"

#include <zephyr/bluetooth/hci_types.h>

#include "hal/debug.h"

static int init_reset(void);
static void isr_done(void *param);
static inline int isr_rx_pdu(struct lll_conn *lll, struct pdu_data *pdu_data_rx,
			     uint8_t *is_rx_enqueue,
			     struct node_tx **tx_release, uint8_t *is_done);

#if defined(CONFIG_BT_CTLR_TX_DEFER)
static void isr_tx_deferred_set(void *param);
#endif /* CONFIG_BT_CTLR_TX_DEFER */

static void empty_tx_init(void);

#if defined(CONFIG_BT_CTLR_INEVENT_ECHO)
/* In-event echo: a "pong" reply staged in the RX ISR and transmitted in the SAME
 * connection event's RX->TX turnaround, riding the empty-PDU accounting so it needs no
 * memq_tx node, no memq_link, and never enters the ULL/host tx-completion path (which for
 * a data PDU would signal the host a completion for a packet it never sent). Single static
 * slot => probe supports ONE connection; per-connection state is a TODO for upstream. */
#define ECHO_ATT_CID_LO    0x04U  /* L2CAP CID 0x0004 = ATT, little-endian */
#define ECHO_ATT_CID_HI    0x00U
#define ECHO_ATT_WRITE_CMD 0x52U  /* ping: ATT Write Command */
#define ECHO_ATT_NOTIFY    0x1BU  /* pong: ATT Handle Value Notification */
#define ECHO_LLDATA_MAX    40U    /* upper bound on echoed payload (buffer-overflow guard) */
static union {
	struct pdu_data pdu;
	uint8_t _pad[sizeof(struct pdu_data) + ECHO_LLDATA_MAX];
} echo_store;
#define echo_pdu (echo_store.pdu)
static bool echo_staged;
/* Ownership instrumentation (read via debugger / lll_conn_echo_stats). */
static uint32_t echo_rx_cnt;   /* pings matched + staged */
static uint32_t echo_tx_cnt;   /* pongs injected into the turnaround */
static uint32_t echo_inject_with_pending; /* echo rode empty while a REAL memq_tx PDU was queued */
static uint32_t echo_stale_cleared;       /* staged echo dropped at event/connection reset (never sent) */
void lll_conn_echo_stats(uint32_t *rx, uint32_t *tx, uint32_t *pending, uint32_t *stale)
{
	if (pending) { *pending = echo_inject_with_pending; }
	if (stale) { *stale = echo_stale_cleared; }
	if (rx) { *rx = echo_rx_cnt; }
	if (tx) { *tx = echo_tx_cnt; }
}
#endif /* CONFIG_BT_CTLR_INEVENT_ECHO */

#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_RX)
static inline bool create_iq_report(struct lll_conn *lll, uint8_t rssi_ready,
				    uint8_t packet_status);
#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_RX */

#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_TX)
static struct pdu_data *get_last_tx_pdu(struct lll_conn *lll);
#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_TX */

static uint8_t crc_expire;
static uint8_t crc_valid;
static uint8_t is_aborted;
static uint16_t tx_cnt;
static uint16_t trx_cnt;

#if defined(CONFIG_BT_CTLR_TIFS_CAPTURE_BENCH)
#include <stdio.h>
#include <zephyr/irq.h>
/* §6.1 BENCH-ONLY (M0), rev 3. Read the controller's SHARED EVENT_TIMER CC0
 * at the start of lll_conn_isr_tx. With SW_SWITCH_SINGLE_TIMER the RX PHYEND
 * clears the timebase, so CC0 (radio_tmr_ready_get()) IS the RX-PHYEND->
 * TX-READY interval of the switch that JUST completed (a hardware-event
 * timing PROXY, stops before the on-air TX bit; NOT on-air).
 *
 * PAIRING: CC0 is the switch that just completed; lll->tifs_tx_us read in
 * isr_tx programs the NEXT switch. The tifs that PRODUCED this CC0 is the
 * one latched at the PREVIOUS isr_tx -> `tifs_prog_prev`.
 *
 * AGGREGATION (rev 3): EXACT 1 us bins (CC0 0..255) so the preregistered
 * MEDIAN is exact at ~1 us resolution. Per (tifs, phy) bin. BOUNDED with
 * EXPLICIT LOSS ACCOUNTING (not "lossless"): a record with no free bin (all
 * TIFS_NBINS occupied) or CC0>255 increments a drop counter; acceptance
 * REQUIRES drop=0. bt_ctlr_tifs_clear() atomically resets after the 2 s
 * post-FSU settle so only post-settle transitions aggregate. The drain
 * snapshots under irq_lock() then formats after unlock. The FIRST record
 * after a fresh connection is skipped (tifs_prog_prev starts stale=150). */
#define TIFS_NBINS   4U
#define TIFS_NHIST   256U        /* exact 1 us bins: CC0 value 0..255 */
struct tifs_bin {
	uint16_t tifs;               /* programmed spacing that produced CC0 */
	uint8_t  phy;
	uint8_t  used;
	uint32_t n_total;
	uint32_t n_valid;            /* fresh CRC-valid RX preceded */
	uint32_t hist[TIFS_NHIST];   /* exact-us CC0 histogram over valid */
};
static struct tifs_bin tifs_bins[TIFS_NBINS];
static uint8_t  tifs_fresh;      /* set in isr_rx on CRC-valid RX */
static uint8_t  tifs_prime;      /* skip the first post-clear transition */
static uint8_t  tifs_capturing;  /* 1 = aggregate; 0 = frozen (drain-safe) */
static uint16_t tifs_prog_prev = EVENT_IFS_DEFAULT_US;  /* 150, stale at start */
static uint32_t tifs_dropped;    /* no free bin, or CC0 out of 0..255 range */
/* DIAGNOSTIC (rev 5): reconcile capture ATTEMPTS vs opportunities. NO timing-source or
 * hook-placement change (the CC0 read is untouched) -- but it DOES add counter writes
 * in the radio ISR, i.e. minor additional instrumentation with possible perturbation.
 * tifs_calls = tifs_on_tx entries while capturing; tifs_fresh_calls = those with a
 * CRC-good RX latched; tifs_role = last caller's role (0xFF = no call this run). A
 * near-zero tifs_calls => the hook is on the wrong path for this role (isr_tx installed
 * only when is_done==false; a normal one-pair event finishes through isr_done); a high
 * tifs_calls with low n_valid => a gating (fresh/prime/cc0-range) issue. */
static uint32_t tifs_calls, tifs_fresh_calls;
static uint8_t  tifs_role = 0xFFU;   /* sentinel: no tifs_on_tx call yet */

static inline void tifs_on_rx_crc_ok(void)
{
	tifs_fresh = 1U;
}

static inline void tifs_on_tx(struct lll_conn *lll)
{
	uint32_t cc0 = radio_tmr_ready_get();
	uint16_t tifs = tifs_prog_prev;   /* value that PRODUCED this CC0 */
	if (tifs_capturing) {
		tifs_calls++;
		tifs_role = lll->role;
		if (tifs_fresh) {
			tifs_fresh_calls++;
		}
	}
#if defined(CONFIG_BT_CTLR_PHY)
	uint8_t phy = lll->phy_tx;
#else
	uint8_t phy = 1U;
#endif
	struct tifs_bin *b = NULL;

	/* Frozen (drain in progress or run ended): keep the pairing latch
	 * current but do not touch the bins the thread is reading. */
	if (!tifs_capturing) {
		tifs_prog_prev = lll->tifs_tx_us;
		tifs_fresh = 0U;
		return;
	}

	/* Skip the FIRST post-clear transition: tifs_prog_prev is stale
	 * (from before the clear / a previous connection). NOTE: primed only
	 * by bt_ctlr_tifs_clear(); runs are reset-isolated (one connection),
	 * and a mid-run reconnect is rejected at analysis (disc must be 0). */
	if (tifs_prime) {
		tifs_prime = 0U;
		tifs_prog_prev = lll->tifs_tx_us;
		tifs_fresh = 0U;
		return;
	}

	for (uint8_t i = 0U; i < TIFS_NBINS; i++) {
		if (tifs_bins[i].used && tifs_bins[i].tifs == tifs &&
		    tifs_bins[i].phy == phy) {
			b = &tifs_bins[i];
			break;
		}
		if (!tifs_bins[i].used && b == NULL) {
			b = &tifs_bins[i];
		}
	}
	if (b == NULL || cc0 > (TIFS_NHIST - 1U)) {
		tifs_dropped++;
	} else {
		if (!b->used) {
			b->used = 1U;
			b->tifs = tifs;
			b->phy = phy;
		}
		b->n_total++;
		if (tifs_fresh) {
			b->hist[cc0]++;
			b->n_valid++;
		}
	}

	tifs_prog_prev = lll->tifs_tx_us;   /* programs the NEXT switch */
	tifs_fresh = 0U;
}

/* Start/restart capture after the post-FSU settle so only post-settle
 * transitions aggregate. Freeze-then-clear-then-enable: the 4 KB memset is
 * done OUTSIDE the lock (capture briefly off), so the lock is held only for
 * two tiny flag flips — never for a KB-scale copy on the radio path. */
void bt_ctlr_tifs_clear(void);
void bt_ctlr_tifs_clear(void)
{
	unsigned int key = irq_lock();

	tifs_capturing = 0U;             /* freeze (tiny) */
	irq_unlock(key);

	(void)memset(tifs_bins, 0, sizeof(tifs_bins));   /* outside lock */
	tifs_dropped = 0U;
	tifs_calls = 0U;
	tifs_fresh_calls = 0U;
	tifs_role = 0xFFU;   /* sentinel so calls=0 never reports a stale/default role */

	key = irq_lock();
	tifs_prime = 1U;
	tifs_capturing = 1U;             /* enable (tiny) */
	irq_unlock(key);
}

/* Freeze capture (tiny locked flag change). Call at run END before drain;
 * after this the ISR does not touch the bins, so the drain reads them
 * directly with NO lock and NO live copy. */
void bt_ctlr_tifs_freeze(void);
void bt_ctlr_tifs_freeze(void)
{
	unsigned int key = irq_lock();

	tifs_capturing = 0U;
	irq_unlock(key);
}

/* Format the FROZEN bins (call bt_ctlr_tifs_freeze() first). Emits per
 * active bin: programmed tifs, phy, totals, exact CC0 min / LOWER-median /
 * max, and drop count. drop MUST be 0 for acceptance. LOWER median = the
 * first value whose cumulative count reaches ceil(n_valid/2) (documented in
 * PREREG-TIMER.md; the ~1 us even/odd convention is immaterial vs a ~98 us
 * delta). */
uint32_t bt_ctlr_tifs_drain_fmt(char *buf, uint32_t buflen);
uint32_t bt_ctlr_tifs_drain_fmt(char *buf, uint32_t buflen)
{
	uint32_t drop = tifs_dropped;
	uint32_t used = 0U;

	for (uint8_t i = 0U; i < TIFS_NBINS; i++) {
		struct tifs_bin *b = &tifs_bins[i];
		uint32_t cum = 0U, mn = 0xFFFFU, mx = 0U, med = 0U;
		int w;

		if (!b->used || b->n_valid == 0U || (buflen - used) < 96U) {
			continue;
		}
		for (uint32_t v = 0U; v < TIFS_NHIST; v++) {
			if (b->hist[v] == 0U) {
				continue;
			}
			if (v < mn) {
				mn = v;
			}
			mx = v;
			cum += b->hist[v];
			if (med == 0U && (cum * 2U) >= b->n_valid) {
				med = v;
			}
		}
		w = snprintf(&buf[used], buflen - used,
			     "TIFSBIN tifs=%u phy=%u n=%u nv=%u min=%u med=%u "
			     "max=%u drop=%u\n",
			     b->tifs, b->phy, b->n_total, b->n_valid,
			     mn, med, mx, drop);
		if (w > 0) {
			used += (uint32_t)w;
		}
	}
	/* diagnostic reconciliation line (analyzer ignores it): how many times the hook
	 * ran vs how many had a fresh CRC-good RX, and the last caller's role. */
	if ((buflen - used) >= 64U) {
		int w = snprintf(&buf[used], buflen - used,
				 "TIFSDIAG calls=%u fresh=%u drop=%u role=%u\n",
				 tifs_calls, tifs_fresh_calls, drop, tifs_role);
		if (w > 0) {
			used += (uint32_t)w;
		}
	}
	return used;
}
#endif /* CONFIG_BT_CTLR_TIFS_CAPTURE_BENCH */
static uint8_t trx_busy_iteration;

#if defined(CONFIG_BT_CTLR_LE_ENC)
static uint8_t mic_state;
#endif /* CONFIG_BT_CTLR_LE_ENC */

#if defined(CONFIG_BT_CTLR_FORCE_MD_COUNT) && \
	(CONFIG_BT_CTLR_FORCE_MD_COUNT > 0)
#if defined(CONFIG_BT_CTLR_FORCE_MD_AUTO)
static uint8_t force_md_cnt_reload;
#define BT_CTLR_FORCE_MD_COUNT force_md_cnt_reload
#else
#define BT_CTLR_FORCE_MD_COUNT CONFIG_BT_CTLR_FORCE_MD_COUNT
#endif
static uint8_t force_md_cnt;

#define FORCE_MD_CNT_INIT() \
		{ \
			force_md_cnt = 0U; \
		}

#define FORCE_MD_CNT_DEC() \
		do { \
			if (force_md_cnt) { \
				force_md_cnt--; \
			} \
		} while (false)

#define FORCE_MD_CNT_GET() force_md_cnt

#define FORCE_MD_CNT_SET() \
		do { \
			if (force_md_cnt || \
			    (trx_cnt >= ((CONFIG_BT_BUF_ACL_TX_COUNT) - 1))) { \
				force_md_cnt = BT_CTLR_FORCE_MD_COUNT; \
			} \
		} while (false)

#else /* !CONFIG_BT_CTLR_FORCE_MD_COUNT */
#define FORCE_MD_CNT_INIT()
#define FORCE_MD_CNT_DEC()
#define FORCE_MD_CNT_GET() 0
#define FORCE_MD_CNT_SET()
#endif /* !CONFIG_BT_CTLR_FORCE_MD_COUNT */

int lll_conn_init(void)
{
	int err;

	err = init_reset();
	if (err) {
		return err;
	}

	empty_tx_init();

	return 0;
}

int lll_conn_reset(void)
{
	int err;

	err = init_reset();
	if (err) {
		return err;
	}

	FORCE_MD_CNT_INIT();

	return 0;
}

void lll_conn_flush(uint16_t handle, struct lll_conn *lll)
{
	/* Nothing to be flushed */
}

void lll_conn_prepare_reset(void)
{
	tx_cnt = 0U;
	trx_cnt = 0U;
	crc_valid = 0U;
	crc_expire = 0U;
	is_aborted = 0U;
	trx_busy_iteration = 0U;

#if defined(CONFIG_BT_CTLR_INEVENT_ECHO)
	/* Point 7: drop any echo staged in a prior event but never transmitted (e.g. the event was
	 * aborted, or the connection dropped) so a STALE pong can't cross into the next event/connection
	 * and corrupt startup accounting. The current event stages its echo AFTER this reset (in the RX
	 * ISR), so legitimate same-event echoes are unaffected. NOTE: file-global single-slot echo state
	 * still supports only ONE connection (per-connection state remains a TODO). */
	if (echo_staged) {
		echo_staged = false;
		echo_stale_cleared++;
	}
#endif /* CONFIG_BT_CTLR_INEVENT_ECHO */

#if defined(CONFIG_BT_CTLR_LE_ENC)
	mic_state = LLL_CONN_MIC_NONE;
#endif /* CONFIG_BT_CTLR_LE_ENC */
}

/* DIAGNOSTIC (assert-disabled fault-injection, 2026-08-01): counts how often the
 * trx_busy_iteration cap is hit — i.e. the path that used to LL_ASSERT_DBG and halt.
 * With CONFIG_BT_CTLR_ASSERT_DEBUG=n that assert is a no-op and the code falls through
 * to `return -ECANCELED` (cancels this one overrunning event instead of halting). NOTE: this
 * return path alone is not shown to *preserve* the connection — measurements (§13.15) show the
 * link can still fail/supervision-timeout; it only avoids the fatal assert. Non-static so the app
 * can read it. Increment condition == the pre-patch assert-fail condition exactly:
 * !(trx_busy_iteration < *_TRX_BUSY_ITERATION_MAX). */
uint32_t volatile lll_conn_trx_busy_cancels;

#if defined(CONFIG_BT_CENTRAL)
/* Number of times central event being aborted by same event instance be skipped */
/* NOTE: Coded PHY S8 coding of 251 byte PDU at 7.5 ms connection interval need up to 4 events
 *       to be skipped due to large connection event length.
 */
#define CENTRAL_TRX_BUSY_ITERATION_MAX MIN(4U, (EVENT_DEFER_MAX))

int lll_conn_central_is_abort_cb(void *next, void *curr,
				 lll_prepare_cb_t *resume_cb)
{
	struct lll_conn *lll = curr;

	if (next != curr) {
		/* Do not be aborted by a different event if near supervision timeout */
		if ((lll->forced == 1U) && (trx_cnt < 1U)) {
			return 0;
		}

	} else if ((next == curr) && (trx_cnt < 1U) &&
		   (trx_busy_iteration < CENTRAL_TRX_BUSY_ITERATION_MAX)) {
		trx_busy_iteration++;

		/* Do not be aborted by same event if a single central's Rx has not completed.
		 * Cases where single trx duration can be greater than connection interval.
		 */
		return -EBUSY;
	}

	if (trx_busy_iteration >= CENTRAL_TRX_BUSY_ITERATION_MAX) {
		lll_conn_trx_busy_cancels++;   /* diagnostic: cancel path taken (was: assert+halt) */
	}
	LL_ASSERT_DBG(trx_busy_iteration < CENTRAL_TRX_BUSY_ITERATION_MAX);

	return -ECANCELED;
}
#endif /* CONFIG_BT_CENTRAL */

#if defined(CONFIG_BT_PERIPHERAL)
/* Number of times peripheral event being aborted by same event instance be skipped */
/* NOTE: Coded PHY S8 coding of 251 byte PDU at 7.5 ms connection interval need up to 4 events
 *       to be skipped due to large connection event length.
 */
#define PERIPHERAL_TRX_BUSY_ITERATION_MAX MIN(4U, (EVENT_DEFER_MAX))

int lll_conn_peripheral_is_abort_cb(void *next, void *curr,
				    lll_prepare_cb_t *resume_cb)
{
	struct lll_conn *lll = curr;

	if (next != curr) {
		/* Do not be aborted by a different event if near supervision timeout */
		if ((lll->forced == 1U) && (tx_cnt < 1U)) {
			return 0;
		}

	} else if ((next == curr) && (tx_cnt < 1U) &&
		   (trx_busy_iteration < PERIPHERAL_TRX_BUSY_ITERATION_MAX)) {
		trx_busy_iteration++;

		/* Do not be aborted by same event if a single peripheral's Tx has not completed.
		 * Cases where single trx duration can be greater than connection interval.
		 */
		return -EBUSY;
	}

	if (trx_busy_iteration >= PERIPHERAL_TRX_BUSY_ITERATION_MAX) {
		lll_conn_trx_busy_cancels++;   /* diagnostic: cancel path taken (was: assert+halt) */
	}
	LL_ASSERT_DBG(trx_busy_iteration < PERIPHERAL_TRX_BUSY_ITERATION_MAX);

	return -ECANCELED;
}
#endif /* CONFIG_BT_PERIPHERAL */

void lll_conn_abort_cb(struct lll_prepare_param *prepare_param, void *param)
{
	struct event_done_extra *e;
	struct lll_conn *lll;
	int err;

	/* NOTE: This is not a prepare being cancelled */
	if (!prepare_param) {
		/* Get reference to LLL connection context */
		lll = param;

		/* For a peripheral role, ensure at least one PDU is tx-ed
		 * back to central, otherwise let the supervision timeout
		 * countdown be started.
		 */
		if ((lll->role == BT_HCI_ROLE_PERIPHERAL) && (tx_cnt < 1U)) {
			is_aborted = 1U;
		}

		/* Perform event abort here.
		 * After event has been cleanly aborted, clean up resources
		 * and dispatch event done.
		 */
		radio_isr_set(isr_done, param);
		radio_disable();

#if defined(CONFIG_BT_CTLR_LE_ENC)
		if (lll->enc_rx) {
			radio_ccm_disable();
		}
#endif /* CONFIG_BT_CTLR_LE_ENC */

		return;
	}

	/* NOTE: Else clean the top half preparations of the aborted event
	 * currently in preparation pipeline.
	 */
	err = lll_hfclock_off();
	LL_ASSERT_ERR(err >= 0);

	/* Get reference to LLL connection context */
	lll = prepare_param->param;

	/* Accumulate the latency as event is aborted while being in pipeline */
	lll->lazy_prepare = prepare_param->lazy;
	lll->latency_prepare += (lll->lazy_prepare + 1U);

#if defined(CONFIG_BT_PERIPHERAL)
	if (lll->role == BT_HCI_ROLE_PERIPHERAL) {
		/* Accumulate window widening */
		lll->periph.window_widening_prepare_us += lll->periph.window_widening_periodic_us *
							  (prepare_param->lazy + 1);
		if (lll->periph.window_widening_prepare_us > lll->periph.window_widening_max_us) {
			lll->periph.window_widening_prepare_us = lll->periph.window_widening_max_us;
		}
	}
#endif /* CONFIG_BT_PERIPHERAL */

	/* Extra done event, to check supervision timeout */
	e = ull_event_done_extra_get();
	LL_ASSERT_ERR(e);

	e->type = EVENT_DONE_EXTRA_TYPE_CONN;
	e->trx_cnt = 0U;
	e->crc_valid = 0U;
	e->is_aborted = 1U;

#if defined(CONFIG_BT_CTLR_LE_ENC)
	e->mic_state = LLL_CONN_MIC_NONE;
#endif /* CONFIG_BT_CTLR_LE_ENC */

	lll_done(param);
}

void lll_conn_isr_rx(void *param)
{
	uint8_t is_empty_pdu_tx_retry;
	struct pdu_data *pdu_data_rx;
	struct pdu_data *pdu_data_tx;
	struct node_rx_pdu *node_rx;
	struct node_tx *tx_release;
	uint8_t is_rx_enqueue;
	struct lll_conn *lll;
	uint8_t rssi_ready;
	bool is_iq_report;
	uint8_t is_ull_rx;
	uint8_t trx_done;
	uint8_t is_done;
	uint8_t cte_len;
	uint8_t crc_ok;
#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_RX)
	bool cte_ready;
#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_RX */

	if (IS_ENABLED(CONFIG_BT_CTLR_PROFILE_ISR)) {
		lll_prof_latency_capture();
	}

	/* Read radio status and events */
	trx_done = radio_is_done();
	if (trx_done) {
		crc_ok = radio_crc_is_valid();
		rssi_ready = radio_rssi_is_ready();
#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_RX)
		cte_ready = radio_df_cte_ready();

#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_RX */
	} else {
		crc_ok = rssi_ready = 0U;
#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_RX)
		cte_ready = 0U;
#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_RX */
	}

	/* Clear radio rx status and events */
	lll_isr_rx_status_reset();

	/* No Rx */
	if (!trx_done) {
		radio_isr_set(isr_done, param);
		radio_disable();

		return;
	}

	trx_cnt++;

	/* Q2: PERIPHERAL response-opportunity counter (a CONSERVATIVE periph-TX
	 * denominator, per review). Counted only on a CRC-GOOD reception -- the
	 * peripheral then transmits its response, so this is >= its actual TX
	 * (a rare post-CRC abort would not transmit). CENTRAL actual TX is counted
	 * in lll_conn_isr_tx. crc_ok is already computed above. */
	{ extern volatile uint32_t lll_conn_q2_tx[40];
	  extern volatile uint8_t lll_conn_q2_curchan;
	  struct lll_conn *ql = param;   /* 'lll' is not yet assigned here */
	  if (ql->role && crc_ok && (lll_conn_q2_curchan < 40U)) lll_conn_q2_tx[lll_conn_q2_curchan]++; }

	is_done = 0U;
	tx_release = NULL;
	is_rx_enqueue = 0U;

	lll = param;

	node_rx = ull_pdu_rx_alloc_peek(1);
	LL_ASSERT_DBG(node_rx);

	pdu_data_rx = (void *)node_rx->pdu;

	if (crc_ok) {
		uint32_t err;

#if defined(CONFIG_BT_CTLR_TIFS_CAPTURE_BENCH)
		tifs_on_rx_crc_ok();
#endif
		err = isr_rx_pdu(lll, pdu_data_rx, &is_rx_enqueue, &tx_release,
				 &is_done);
		if (err) {
			/* Disable radio trx switch on MIC failure for both
			 * central and peripheral, and close the radio event.
			 */
			radio_isr_set(isr_done, param);
			radio_disable();

			/* assert if radio started tx before being disabled */
			if (IS_ENABLED(CONFIG_BT_CTLR_PROFILE_ISR)) {
				LL_ASSERT_MSG(!radio_is_ready(), "%s: Radio ISR latency: %u",
					      __func__, lll_prof_latency_get());
			} else {
				LL_ASSERT_ERR(!radio_is_ready());
			}

			goto lll_conn_isr_rx_exit;
		}

		/* Reset CRC expiry counter */
		crc_expire = 0U;

		/* CRC valid flag used to detect supervision timeout */
		crc_valid = 1U;

#if defined(CONFIG_BT_CTLR_INEVENT_ECHO)
		/* In-event echo: if this RX is a "ping" (a complete, non-fragmented ATT
		 * Write Command on the ATT fixed channel), stage a "pong" (same PDU, opcode
		 * -> Handle Value Notification) to transmit in THIS event's turnaround.
		 * Near-zero work: a bounded, validated memcpy. Safe-matcher requirements:
		 * LLID=START (not a continuation fragment), 7 <= len <= ECHO_LLDATA_MAX
		 * (opcode+handle present, no overflow), and the L2CAP length field matches
		 * the PDU (a whole SDU, not a fragment). Handle is preserved from the ping.
		 * TODO(upstream): restrict to a single configured attribute handle. */
		if ((pdu_data_rx->ll_id == PDU_DATA_LLID_DATA_START) &&
		    (pdu_data_rx->len >= 7U) &&
		    (pdu_data_rx->len <= ECHO_LLDATA_MAX) &&
		    (((uint16_t)pdu_data_rx->lldata[0] |
		      ((uint16_t)pdu_data_rx->lldata[1] << 8)) ==
		     (uint16_t)(pdu_data_rx->len - 4U)) &&
		    (pdu_data_rx->lldata[2] == ECHO_ATT_CID_LO) &&
		    (pdu_data_rx->lldata[3] == ECHO_ATT_CID_HI) &&
		    (pdu_data_rx->lldata[4] == ECHO_ATT_WRITE_CMD)) {
			echo_pdu.ll_id = PDU_DATA_LLID_DATA_START;
			echo_pdu.md = 0U;
			echo_pdu.len = pdu_data_rx->len;
			memcpy(echo_pdu.lldata, pdu_data_rx->lldata, pdu_data_rx->len);
			echo_pdu.lldata[4] = ECHO_ATT_NOTIFY;
			echo_staged = true;
			echo_rx_cnt++;
		}
#endif /* CONFIG_BT_CTLR_INEVENT_ECHO */
	} else {
		/* Start CRC error countdown, if not already started */
		if (crc_expire == 0U) {
			crc_expire = 2U;
		}

		/* CRC error countdown */
		crc_expire--;
		is_done = (crc_expire == 0U);
	}

#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_RX) && defined(CONFIG_BT_CTLR_LE_ENC)
		if (lll->enc_rx) {
			struct pdu_data *pdu_scratch;

			pdu_scratch = (struct pdu_data *)radio_pkt_scratch_get();

			if (pdu_scratch->cp) {
				(void)memcpy((void *)&pdu_data_rx->octet3.cte_info,
					     (void *)&pdu_scratch->octet3.cte_info,
					     sizeof(pdu_data_rx->octet3.cte_info));
			}
		}
#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_RX && defined(CONFIG_BT_CTLR_LE_ENC) */

	/* prepare tx packet */
	is_empty_pdu_tx_retry = lll->empty;
	lll_conn_pdu_tx_prep(lll, &pdu_data_tx);

#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_TX)
	if (pdu_data_tx->cp) {
		cte_len = CTE_LEN_US(pdu_data_tx->octet3.cte_info.time);

		lll_df_cte_tx_configure(pdu_data_tx->octet3.cte_info.type,
					pdu_data_tx->octet3.cte_info.time,
					lll->df_tx_cfg.ant_sw_len,
					lll->df_tx_cfg.ant_ids);
	} else
#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_TX */
	{
		cte_len = 0U;
	}

#if defined(CONFIG_BT_PERIPHERAL)
	/* Lets close early so that drift compensation is calculated before this event overlaps
	 * with next interval.
	 * TODO: Optimize, to improve throughput, by removing this early close and using the drift
	 *       compensation value in the overlapping next interval, if under high throughput
	 *       scenarios.
	 */
	is_done = is_done || ((lll->role == BT_HCI_ROLE_PERIPHERAL) &&
			      (lll->periph.window_size_event_us != 0U));
#endif /* CONFIG_BT_PERIPHERAL */

	/* Decide on event continuation and hence Radio Shorts to use */
	is_done = is_done || ((crc_ok) &&
			      (pdu_data_rx->md == 0) &&
			      (pdu_data_tx->md == 0) &&
			      (pdu_data_tx->len == 0));
	/* Do not continue anymore if this event had continued despite an abort requested by same
	 * connection instance when overlapping due to connection event length being larger than
	 * the connection interval.
	 */
	is_done = is_done || (trx_busy_iteration != 0U);

	if (is_done) {
		radio_isr_set(isr_done, param);

		if (0) {
#if defined(CONFIG_BT_CENTRAL)
		/* Event done for central */
		} else if (!lll->role) {
			radio_disable();

			/* assert if radio started tx before being disabled */
			if (IS_ENABLED(CONFIG_BT_CTLR_PROFILE_ISR)) {
				LL_ASSERT_MSG(!radio_is_ready(), "%s: Radio ISR latency: %u",
					      __func__, lll_prof_latency_get());
			} else {
				LL_ASSERT_ERR(!radio_is_ready());
			}

			/* Restore state if last transmitted was empty PDU */
			lll->empty = is_empty_pdu_tx_retry;

			goto lll_conn_isr_rx_exit;
#endif /* CONFIG_BT_CENTRAL */
#if defined(CONFIG_BT_PERIPHERAL)
		/* Event done for peripheral */
		} else {
			radio_switch_complete_and_disable();
#endif /* CONFIG_BT_PERIPHERAL */
		}
	} else {
		radio_tmr_tifs_set(lll->tifs_rx_us);

#if defined(CONFIG_BT_CTLR_PHY)
		radio_switch_complete_and_rx(lll->phy_rx);
#else /* !CONFIG_BT_CTLR_PHY */
		radio_switch_complete_and_rx(0);
#endif /* !CONFIG_BT_CTLR_PHY */

		radio_isr_set(lll_conn_isr_tx, param);

		/* capture end of Tx-ed PDU, used to calculate HCTO. */
		radio_tmr_end_capture();
	}

	/* Fill sn and nesn */
	pdu_data_tx->sn = lll->sn;
	pdu_data_tx->nesn = lll->nesn;

	/* setup the radio tx packet buffer */
	lll_conn_tx_pkt_set(lll, pdu_data_tx);

#if defined(HAL_RADIO_GPIO_HAVE_PA_PIN)
	uint32_t pa_lna_enable_us;

#if defined(CONFIG_BT_CTLR_PROFILE_ISR)
	/* PA enable is overwriting packet end used in ISR profiling, hence
	 * back it up for later use.
	 */
	lll_prof_radio_end_backup();
#endif /* CONFIG_BT_CTLR_PROFILE_ISR */

	radio_gpio_pa_setup();

	pa_lna_enable_us =
		radio_tmr_tifs_base_get() + lll->tifs_tx_us - cte_len - HAL_RADIO_GPIO_PA_OFFSET;
#if defined(CONFIG_BT_CTLR_PHY)
	pa_lna_enable_us -= radio_rx_chain_delay_get(lll->phy_rx, PHY_FLAGS_S8);
#else /* !CONFIG_BT_CTLR_PHY */
	pa_lna_enable_us -= radio_rx_chain_delay_get(0, PHY_FLAGS_S2);
#endif /* !CONFIG_BT_CTLR_PHY */
	radio_gpio_pa_lna_enable(pa_lna_enable_us);
#endif /* HAL_RADIO_GPIO_HAVE_PA_PIN */

	/* assert if radio packet ptr is not set and radio started tx */
	if (IS_ENABLED(CONFIG_BT_CTLR_PROFILE_ISR)) {
		LL_ASSERT_MSG(!radio_is_ready(), "%s: Radio ISR latency: %u", __func__,
			      lll_prof_latency_get());
	} else {
		LL_ASSERT_ERR(!radio_is_ready());
	}

#if defined(CONFIG_BT_CTLR_TX_DEFER)
	if (!is_empty_pdu_tx_retry && (pdu_data_tx->len == 0U)) {
		uint32_t tx_defer_us;
		uint32_t defer_us;

		/* Restore state if transmission setup for empty PDU */
		lll->empty = 0U;

		/* Setup deferred tx packet set */
		tx_defer_us = radio_tmr_tifs_base_get() + lll->tifs_tx_us -
			      HAL_RADIO_TMR_DEFERRED_TX_DELAY_US;
		defer_us = radio_tmr_isr_set(tx_defer_us, isr_tx_deferred_set,
					     param);
	}
#endif /* CONFIG_BT_CTLR_TX_DEFER */

lll_conn_isr_rx_exit:
	/* Save the AA captured for the first Rx in connection event */
	if (!radio_tmr_aa_restore()) {
		radio_tmr_aa_save(radio_tmr_aa_get());
	}

#if defined(CONFIG_BT_CTLR_PROFILE_ISR)
	lll_prof_cputime_capture();
#endif /* CONFIG_BT_CTLR_PROFILE_ISR */

	is_ull_rx = 0U;

	if (tx_release) {
		LL_ASSERT_DBG(lll->handle != 0xFFFF);

		ull_conn_lll_ack_enqueue(lll->handle, tx_release);

		is_ull_rx = 1U;
	}

	if (is_rx_enqueue) {
#if defined(CONFIG_SOC_NRF52832) && \
	defined(CONFIG_BT_CTLR_LE_ENC) && \
	defined(HAL_RADIO_PDU_LEN_MAX) && \
	(!defined(CONFIG_BT_CTLR_DATA_LENGTH_MAX) || \
	 (CONFIG_BT_CTLR_DATA_LENGTH_MAX < (HAL_RADIO_PDU_LEN_MAX - 4)))
		if (lll->enc_rx) {
			uint8_t *pkt_decrypt_data;

			pkt_decrypt_data = (uint8_t *)radio_pkt_decrypt_get() +
					   offsetof(struct pdu_data, lldata);
			memcpy((void *)pdu_data_rx->lldata,
			       (void *)pkt_decrypt_data, pdu_data_rx->len);
		}
#elif !defined(HAL_RADIO_PDU_LEN_MAX)
#error "Undefined HAL_RADIO_PDU_LEN_MAX."
#endif
		ull_pdu_rx_alloc();

		node_rx->hdr.type = NODE_RX_TYPE_DC_PDU;
		node_rx->hdr.handle = lll->handle;

		ull_rx_put(node_rx->hdr.link, node_rx);
		is_ull_rx = 1U;
	}

#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_RX)
	if (cte_ready) {
		is_iq_report =
			create_iq_report(lll, rssi_ready,
					 (crc_ok == true ? BT_HCI_LE_CTE_CRC_OK :
							BT_HCI_LE_CTE_CRC_ERR_CTE_BASED_TIME));
	} else {
#else
	if (1) {
#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_RX */
		is_iq_report = false;
	}

	if (is_ull_rx || is_iq_report) {
		ull_rx_sched();
	}

#if defined(CONFIG_BT_CTLR_CONN_RSSI)
	/* Collect RSSI for connection */
	if (rssi_ready) {
		uint8_t rssi = radio_rssi_get();

		lll->rssi_latest = rssi;

#if defined(CONFIG_BT_CTLR_CONN_RSSI_EVENT)
		if (((lll->rssi_reported - rssi) & 0xFF) >
		    LLL_CONN_RSSI_THRESHOLD) {
			if (lll->rssi_sample_count) {
				lll->rssi_sample_count--;
			}
		} else {
			lll->rssi_sample_count = LLL_CONN_RSSI_SAMPLE_COUNT;
		}
#endif /* CONFIG_BT_CTLR_CONN_RSSI_EVENT */
	}
#else /* !CONFIG_BT_CTLR_CONN_RSSI */
	ARG_UNUSED(rssi_ready);
#endif /* !CONFIG_BT_CTLR_CONN_RSSI */

#if defined(CONFIG_BT_CTLR_PROFILE_ISR)
	lll_prof_send();
#endif /* CONFIG_BT_CTLR_PROFILE_ISR */
}

void lll_conn_isr_tx(void *param)
{
#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_TX)
	static struct pdu_data *pdu_tx;
	uint8_t cte_len;
#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_TX */
	struct lll_conn *lll;
	uint32_t hcto;

	if (IS_ENABLED(CONFIG_BT_CTLR_PROFILE_ISR)) {
		lll_prof_latency_capture();
	}

	/* Clear radio tx status and events */
	lll_isr_tx_status_reset();

	tx_cnt++;

	lll = param;
	{ extern volatile uint32_t lll_conn_q2_tx[40];
	  extern volatile uint8_t lll_conn_q2_curchan;
	  if (lll_conn_q2_curchan < 40U) lll_conn_q2_tx[lll_conn_q2_curchan]++; }

#if defined(CONFIG_BT_CTLR_TIFS_CAPTURE_BENCH)
	/* CC0 here = the preceding RX-PHYEND -> TX-READY interval (single-timer
	 * base was cleared at RX PHYEND). Read BEFORE anything reprograms the
	 * timer for the next tIFS. */
	tifs_on_tx(lll);
#endif

	/* setup tIFS switching */
	radio_tmr_tifs_set(lll->tifs_tx_us);

#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_RX)
#if defined(CONFIG_BT_CTLR_DF_PHYEND_OFFSET_COMPENSATION_ENABLE)
	enum radio_end_evt_delay_state end_evt_delay;
#endif /* CONFIG_BT_CTLR_DF_PHYEND_OFFSET_COMPENSATION_ENABLE */

#if defined(CONFIG_BT_CTLR_PHY)
	if (lll->phy_rx != PHY_CODED) {
#else
	if (1) {
#endif /* CONFIG_BT_CTLR_PHY */
		struct lll_df_conn_rx_params *df_rx_params;
		struct lll_df_conn_rx_cfg *df_rx_cfg;

		df_rx_cfg = &lll->df_rx_cfg;
		/* Get last swapped CTE RX configuration. Do not swap it again here.
		 * It should remain unchanged for connection event duration.
		 */
		df_rx_params = dbuf_curr_get(&df_rx_cfg->hdr);

		if (df_rx_params->is_enabled) {
			(void)lll_df_conf_cte_rx_enable(df_rx_params->slot_durations,
						  df_rx_params->ant_sw_len, df_rx_params->ant_ids,
						  df_rx_cfg->chan, CTE_INFO_IN_S1_BYTE,
						  lll->phy_rx);
		} else {
			lll_df_conf_cte_info_parsing_enable();
		}
#if defined(CONFIG_BT_CTLR_DF_PHYEND_OFFSET_COMPENSATION_ENABLE)
		end_evt_delay = END_EVT_DELAY_ENABLED;
	} else {
		end_evt_delay = END_EVT_DELAY_DISABLED;
#endif /* CONFIG_BT_CTLR_DF_PHYEND_OFFSET_COMPENSATION_ENABLE */
	}

#if defined(CONFIG_BT_CTLR_DF_PHYEND_OFFSET_COMPENSATION_ENABLE)
	/* Use special API for SOC that requires compensation for PHYEND event delay. */

#if defined(CONFIG_BT_CTLR_PHY)
	radio_switch_complete_with_delay_compensation_and_tx(lll->phy_rx, 0, lll->phy_tx,
							     lll->phy_flags, end_evt_delay);
#else /* !CONFIG_BT_CTLR_PHY */
	radio_switch_complete_with_delay_compensation_and_tx(0, 0, 0, 0, end_evt_delay);
#endif /* !CONFIG_BT_CTLR_PHY */

#endif /* CONFIG_BT_CTLR_DF_PHYEND_OFFSET_COMPENSATION_ENABLE */
#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_RX */

/* Use regular API for cases when:
 * - CTE RX is not enabled,
 * - SOC does not require compensation for PHYEND event delay.
 */
#if !defined(CONFIG_BT_CTLR_DF_PHYEND_OFFSET_COMPENSATION_ENABLE)
#if defined(CONFIG_BT_CTLR_PHY)
	radio_switch_complete_and_tx(lll->phy_rx, 0, lll->phy_tx, lll->phy_flags);
#else /* !CONFIG_BT_CTLR_PHY */
	radio_switch_complete_and_tx(0, 0, 0, 0);
#endif /* !CONFIG_BT_CTLR_PHY */
#endif /* !CONFIG_BT_CTLR_DF_PHYEND_OFFSET_COMPENSATION_ENABLE */

	lll_conn_rx_pkt_set(lll);

	/* assert if radio packet ptr is not set and radio started rx */
	if (IS_ENABLED(CONFIG_BT_CTLR_PROFILE_ISR)) {
		LL_ASSERT_MSG(!radio_is_ready(), "%s: Radio ISR latency: %u", __func__,
			      lll_prof_latency_get());
	} else {
		LL_ASSERT_ERR(!radio_is_ready());
	}

#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_TX)
	pdu_tx = get_last_tx_pdu(lll);
	LL_ASSERT_DBG(pdu_tx);

	if (pdu_tx->cp) {
		cte_len = CTE_LEN_US(pdu_tx->octet3.cte_info.time);
	} else {
		cte_len = 0U;
	}
#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_TX */

#if !defined(CONFIG_BOARD_NRF52_BSIM) && \
	!defined(CONFIG_BOARD_NRF5340BSIM_NRF5340_CPUNET) && \
	!defined(CONFIG_BOARD_NRF54L15BSIM_NRF54L15_CPUAPP)

	/* +/- 2us active clock jitter, +1 us PPI to timer start compensation */
	hcto = radio_tmr_tifs_base_get() + lll->tifs_hcto_us +
	       (EVENT_CLOCK_JITTER_US << 1) + RANGE_DELAY_US +
	       HAL_RADIO_TMR_START_DELAY_US;

#else /* FIXME: Why different for BabbleSIM? */
	/* HACK: Have exact 150 us */
	hcto = radio_tmr_tifs_base_get() + lll->tifs_hcto_us;

	/* HACK: Could wrong MODE register value (next in tIFS switching) being
	 *       use for Rx Chain Delay in BabbleSIM? or is there a bug in
	 *       target implementation?
	 */
	hcto += radio_rx_chain_delay_get(lll->phy_tx, PHY_FLAGS_S8);
#endif /* FIXME: Why different for BabbleSIM? */

#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_TX)
	hcto += cte_len;
#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_TX */
#if defined(CONFIG_BT_CTLR_PHY)
	hcto += radio_rx_chain_delay_get(lll->phy_rx, 1);
	hcto += addr_us_get(lll->phy_rx);
	hcto -= radio_tx_chain_delay_get(lll->phy_tx, lll->phy_flags);
#else /* !CONFIG_BT_CTLR_PHY */
	hcto += radio_rx_chain_delay_get(0, 0);
	hcto += addr_us_get(0);
	hcto -= radio_tx_chain_delay_get(0, 0);
#endif /* !CONFIG_BT_CTLR_PHY */

	radio_tmr_hcto_configure(hcto);

#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_RX)
	if (true) {
#elif defined(CONFIG_BT_CENTRAL) && defined(CONFIG_BT_CTLR_CONN_RSSI)
	if (!trx_cnt && !lll->role) {
#else
	if (false) {
#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_RX */

		radio_rssi_measure();
	}

#if defined(CONFIG_BT_CTLR_PROFILE_ISR) || \
	defined(CONFIG_BT_CTLR_TX_DEFER) || \
	defined(HAL_RADIO_GPIO_HAVE_PA_PIN)
	radio_tmr_end_capture();
#endif /* CONFIG_BT_CTLR_PROFILE_ISR ||
	* CONFIG_BT_CTLR_TX_DEFER ||
	* HAL_RADIO_GPIO_HAVE_PA_PIN
	*/

#if defined(HAL_RADIO_GPIO_HAVE_LNA_PIN)
	radio_gpio_lna_setup();
#if defined(CONFIG_BT_CTLR_PHY)
	radio_gpio_pa_lna_enable(radio_tmr_tifs_base_get() + lll->tifs_rx_us -
				 (EVENT_CLOCK_JITTER_US << 1) -
				 radio_tx_chain_delay_get(lll->phy_tx,
							  lll->phy_flags) -
				 HAL_RADIO_GPIO_LNA_OFFSET);
#else /* !CONFIG_BT_CTLR_PHY */
	radio_gpio_pa_lna_enable(radio_tmr_tifs_base_get() + lll->tifs_rx_us -
				 (EVENT_CLOCK_JITTER_US << 1) -
				 radio_tx_chain_delay_get(0U, 0U) -
				 HAL_RADIO_GPIO_LNA_OFFSET);
#endif /* !CONFIG_BT_CTLR_PHY */
#endif /* HAL_RADIO_GPIO_HAVE_LNA_PIN */

	radio_isr_set(lll_conn_isr_rx, param);

#if defined(CONFIG_BT_CTLR_LOW_LAT)
	ull_conn_lll_tx_demux_sched(lll);
#endif /* CONFIG_BT_CTLR_LOW_LAT */
}

void lll_conn_rx_pkt_set(struct lll_conn *lll)
{
	struct pdu_data *pdu_data_rx;
	struct node_rx_pdu *node_rx;
	uint16_t max_rx_octets;
	uint8_t phy;

	node_rx = ull_pdu_rx_alloc_peek(1);
	LL_ASSERT_DBG(node_rx);

	/* In case of ISR latencies, if packet pointer has not been set on time
	 * then we do not want to check uninitialized length in rx buffer that
	 * did not get used by Radio DMA. This would help us in detecting radio
	 * ready event being set? We can not detect radio ready if it happens
	 * twice before Radio ISR executes after latency.
	 */
	pdu_data_rx = (void *)node_rx->pdu;
	pdu_data_rx->len = 0U;

#if defined(CONFIG_BT_CTLR_DATA_LENGTH)
	max_rx_octets = lll->dle.eff.max_rx_octets;
#else /* !CONFIG_BT_CTLR_DATA_LENGTH */
	max_rx_octets = PDU_DC_PAYLOAD_SIZE_MIN;
#endif /* !CONFIG_BT_CTLR_DATA_LENGTH */

	if ((PDU_DC_CTRL_RX_SIZE_MAX > PDU_DC_PAYLOAD_SIZE_MIN) &&
	    (max_rx_octets < PDU_DC_CTRL_RX_SIZE_MAX)) {
		max_rx_octets = PDU_DC_CTRL_RX_SIZE_MAX;
	}

#if defined(CONFIG_BT_CTLR_PHY)
	phy = lll->phy_rx;
#else /* !CONFIG_BT_CTLR_PHY */
	phy = 0U;
#endif /* !CONFIG_BT_CTLR_PHY */

	radio_phy_set(phy, 0);

	if (0) {
#if defined(CONFIG_BT_CTLR_LE_ENC)
	} else if (lll->enc_rx) {
		radio_pkt_configure(RADIO_PKT_CONF_LENGTH_8BIT, (max_rx_octets + PDU_MIC_SIZE),
				    RADIO_PKT_CONF_FLAGS(RADIO_PKT_CONF_PDU_TYPE_DC, phy,
							 RADIO_PKT_CONF_CTE_DISABLED));

#if defined(CONFIG_SOC_NRF52832) && \
	defined(HAL_RADIO_PDU_LEN_MAX) && \
	(!defined(CONFIG_BT_CTLR_DATA_LENGTH_MAX) || \
	 (CONFIG_BT_CTLR_DATA_LENGTH_MAX < (HAL_RADIO_PDU_LEN_MAX - 4)))
		radio_pkt_rx_set(radio_ccm_rx_pkt_set(&lll->ccm_rx, phy,
						      radio_pkt_decrypt_get()));
#elif !defined(HAL_RADIO_PDU_LEN_MAX)
#error "Undefined HAL_RADIO_PDU_LEN_MAX."
#else
		radio_pkt_rx_set(radio_ccm_rx_pkt_set(&lll->ccm_rx, phy,
						      pdu_data_rx));
#endif
#endif /* CONFIG_BT_CTLR_LE_ENC */
	} else {
		radio_pkt_configure(RADIO_PKT_CONF_LENGTH_8BIT, max_rx_octets,
				    RADIO_PKT_CONF_FLAGS(RADIO_PKT_CONF_PDU_TYPE_DC, phy,
							 RADIO_PKT_CONF_CTE_DISABLED));

		radio_pkt_rx_set(pdu_data_rx);
	}
}

void lll_conn_tx_pkt_set(struct lll_conn *lll, struct pdu_data *pdu_data_tx)
{
	uint8_t phy, flags, pkt_flags;
	uint16_t max_tx_octets;

#if defined(CONFIG_BT_CTLR_DATA_LENGTH)
	max_tx_octets = lll->dle.eff.max_tx_octets;
#else /* !CONFIG_BT_CTLR_DATA_LENGTH */
	max_tx_octets = PDU_DC_PAYLOAD_SIZE_MIN;
#endif /* !CONFIG_BT_CTLR_DATA_LENGTH */

	if ((PDU_DC_CTRL_TX_SIZE_MAX > PDU_DC_PAYLOAD_SIZE_MIN) &&
	    (max_tx_octets < PDU_DC_CTRL_TX_SIZE_MAX)) {
		max_tx_octets = PDU_DC_CTRL_TX_SIZE_MAX;
	}

#if defined(CONFIG_BT_CTLR_PHY)
	phy = lll->phy_tx;
	flags = lll->phy_flags;
#else /* !CONFIG_BT_CTLR_PHY */
	phy = 0U;
	flags = 0U;
#endif /* !CONFIG_BT_CTLR_PHY */

	radio_phy_set(phy, flags);

#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_TX)
	if (pdu_data_tx->cp) {
		pkt_flags = RADIO_PKT_CONF_FLAGS(RADIO_PKT_CONF_PDU_TYPE_DC, phy,
						 RADIO_PKT_CONF_CTE_ENABLED);
	} else
#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_TX */
	{
		pkt_flags = RADIO_PKT_CONF_FLAGS(RADIO_PKT_CONF_PDU_TYPE_DC, phy,
						 RADIO_PKT_CONF_CTE_DISABLED);
	}

	if (0) {
#if defined(CONFIG_BT_CTLR_LE_ENC)
	} else if (lll->enc_tx) {
		radio_pkt_configure(RADIO_PKT_CONF_LENGTH_8BIT, (max_tx_octets + PDU_MIC_SIZE),
				    pkt_flags);

		radio_pkt_tx_set(radio_ccm_tx_pkt_set(&lll->ccm_tx, pdu_data_tx));
#endif /* CONFIG_BT_CTLR_LE_ENC */
	} else {
		radio_pkt_configure(RADIO_PKT_CONF_LENGTH_8BIT, max_tx_octets, pkt_flags);

		radio_pkt_tx_set(pdu_data_tx);
	}
}

void lll_conn_pdu_tx_prep(struct lll_conn *lll, struct pdu_data **pdu_data_tx)
{
	struct node_tx *tx;
	struct pdu_data *p;
	memq_link_t *link;

#if defined(CONFIG_BT_CTLR_INEVENT_ECHO)
	/* In-event echo: a ping was just received this event -> answer with the staged pong
	 * now, in the same turnaround. Ride the EMPTY-PDU accounting: set lll->empty so the
	 * peer's ACK next event takes the empty branch (no memq_tx dequeue/free, no ULL/host
	 * tx-completion) while the radio still transmits our data-bearing echo_pdu. sn/nesn are
	 * filled by the caller; sn advances on ACK exactly as for an empty PDU. */
	if (echo_staged) {
		struct node_tx *pend_tx;

		echo_staged = false;
		lll->empty = 1U;
		echo_tx_cnt++;
		/* DIAGNOSTIC (point 8): was a REAL tx PDU already queued when the echo rode empty?
		 * If so, that PDU (possibly an LL control PDU, e.g. the conn-param-update) is deferred
		 * this event -> a candidate cause of the startup wedge. */
		if (memq_peek(lll->memq_tx.head, lll->memq_tx.tail, (void **)&pend_tx)) {
			echo_inject_with_pending++;
		}
		*pdu_data_tx = &echo_pdu;
		return;
	}
#endif /* CONFIG_BT_CTLR_INEVENT_ECHO */

	link = memq_peek(lll->memq_tx.head, lll->memq_tx.tail, (void **)&tx);
	if (lll->empty || !link) {
		lll->empty = 1U;

		p = (void *)radio_pkt_empty_get();
		if (link || FORCE_MD_CNT_GET()) {
			p->md = 1U;
		} else {
			p->md = 0U;
		}
	} else {
		uint16_t max_tx_octets;

		p = (void *)(tx->pdu + lll->packet_tx_head_offset);

		if (!lll->packet_tx_head_len) {
			lll->packet_tx_head_len = p->len;
		}

		if (lll->packet_tx_head_offset) {
			p->ll_id = PDU_DATA_LLID_DATA_CONTINUE;

#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_TX) || defined(CONFIG_BT_CTLR_DF_CONN_CTE_RX)
			/* BT 5.3 Core Spec does not define handling of CP bit
			 * for PDUs fragmented by Controller, hence the CP bit
			 * is set to zero. The CTE should not be transmitted
			 * with CONTINUE PDUs if fragmentation is performed.
			 */
			p->cp = 0U;
			p->octet3.resv[0] = 0U;
#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_TX || CONFIG_BT_CTLR_DF_CONN_CTE_RX */
		}

		p->len = lll->packet_tx_head_len - lll->packet_tx_head_offset;

		max_tx_octets = ull_conn_lll_max_tx_octets_get(lll);

		if (((PDU_DC_CTRL_TX_SIZE_MAX <= PDU_DC_PAYLOAD_SIZE_MIN) ||
		     (p->ll_id != PDU_DATA_LLID_CTRL)) &&
		    (p->len > max_tx_octets)) {
			p->len = max_tx_octets;
			p->md = 1U;
		} else if ((link->next != lll->memq_tx.tail) ||
			   FORCE_MD_CNT_GET()) {
			p->md = 1U;
		} else {
			p->md = 0U;
		}

		p->rfu = 0U;

#if !defined(CONFIG_BT_CTLR_DATA_LENGTH_CLEAR)
#if !defined(CONFIG_BT_CTLR_DF_CONN_CTE_TX) && !defined(CONFIG_BT_CTLR_DF_CONN_CTE_RX)
		/* Initialize only if vendor PDU octet3 present */
		if (sizeof(p->octet3.resv)) {
			p->octet3.resv[0] = 0U;
		}
#endif /* !CONFIG_BT_CTLR_DF_CONN_CTE_TX && !CONFIG_BT_CTLR_DF_CONN_CTE_RX */
#endif /* CONFIG_BT_CTLR_DATA_LENGTH_CLEAR */
	}

	*pdu_data_tx = p;
}

#if defined(CONFIG_BT_CTLR_FORCE_MD_AUTO)
uint8_t lll_conn_force_md_cnt_set(uint8_t reload_cnt)
{
	uint8_t previous;

	previous = force_md_cnt_reload;
	force_md_cnt_reload = reload_cnt;

	return previous;
}
#endif /* CONFIG_BT_CTLR_FORCE_MD_AUTO */

static int init_reset(void)
{
	return 0;
}

static void isr_done(void *param)
{
	struct event_done_extra *e;

	lll_isr_status_reset();

	e = ull_event_done_extra_get();
	LL_ASSERT_ERR(e);

	e->type = EVENT_DONE_EXTRA_TYPE_CONN;
	e->trx_cnt = trx_cnt;
	e->crc_valid = crc_valid;
	e->is_aborted = is_aborted;

#if defined(CONFIG_BT_CTLR_LE_ENC)
	e->mic_state = mic_state;
#endif /* CONFIG_BT_CTLR_LE_ENC */

#if defined(CONFIG_BT_PERIPHERAL)
	if (trx_cnt) {
		struct lll_conn *lll = param;

		if (lll->role) {
			uint32_t preamble_to_addr_us;

#if defined(CONFIG_BT_CTLR_PHY)
			preamble_to_addr_us =
				addr_us_get(lll->periph.phy_rx_event);
#else /* !CONFIG_BT_CTLR_PHY */
			preamble_to_addr_us =
				addr_us_get(0);
#endif /* !CONFIG_BT_CTLR_PHY */

			e->drift.start_to_address_actual_us =
				radio_tmr_aa_restore() - radio_tmr_ready_get();
			e->drift.window_widening_event_us =
				lll->periph.window_widening_event_us;
			e->drift.preamble_to_addr_us = preamble_to_addr_us;

			/* Reset window widening, as anchor point sync-ed */
			lll->periph.window_widening_event_us = 0;
			lll->periph.window_size_event_us = 0;
		}
	}
#endif /* CONFIG_BT_PERIPHERAL */

	lll_isr_cleanup(param);
}

static inline bool ctrl_pdu_len_check(uint8_t len)
{
	return len <= (offsetof(struct pdu_data, llctrl) +
		       sizeof(struct pdu_data_llctrl));

}

static inline int isr_rx_pdu(struct lll_conn *lll, struct pdu_data *pdu_data_rx,
			     uint8_t *is_rx_enqueue,
			     struct node_tx **tx_release, uint8_t *is_done)
{
#if defined(CONFIG_SOC_NRF52832) && \
	defined(CONFIG_BT_CTLR_LE_ENC) && \
	defined(HAL_RADIO_PDU_LEN_MAX) && \
	(!defined(CONFIG_BT_CTLR_DATA_LENGTH_MAX) || \
	 (CONFIG_BT_CTLR_DATA_LENGTH_MAX < (HAL_RADIO_PDU_LEN_MAX - 4)))
	if (lll->enc_rx) {
		uint8_t *pkt_decrypt;

		pkt_decrypt = radio_pkt_decrypt_get();
		memcpy((void *)pdu_data_rx, (void *)pkt_decrypt,
		       offsetof(struct pdu_data, lldata));
	}
#elif !defined(HAL_RADIO_PDU_LEN_MAX)
#error "Undefined HAL_RADIO_PDU_LEN_MAX."
#endif

	/* Ack for tx-ed data */
	if (pdu_data_rx->nesn != lll->sn) {
		struct pdu_data *pdu_data_tx;
		struct node_tx *tx;
		memq_link_t *link;

		/* Increment sequence number */
		lll->sn++;

#if defined(CONFIG_BT_PERIPHERAL)
		/* First ack (and redundantly any other ack) enable use of
		 * peripheral latency.
		 */
		if (lll->role) {
			lll->periph.latency_enabled = 1;
		}
#endif /* CONFIG_BT_PERIPHERAL */

		FORCE_MD_CNT_DEC();

		if (!lll->empty) {
			link = memq_peek(lll->memq_tx.head, lll->memq_tx.tail,
					 (void **)&tx);
		} else {
			lll->empty = 0;

			pdu_data_tx = (void *)radio_pkt_empty_get();
			if (IS_ENABLED(CONFIG_BT_CENTRAL) && !lll->role &&
			    !pdu_data_rx->md) {
				*is_done = !pdu_data_tx->md;
			}

			link = NULL;
		}

		if (link) {
			uint8_t pdu_data_tx_len;
			uint8_t offset;

			pdu_data_tx = (void *)(tx->pdu +
					       lll->packet_tx_head_offset);

			pdu_data_tx_len = pdu_data_tx->len;
#if defined(CONFIG_BT_CTLR_LE_ENC)
			if (pdu_data_tx_len != 0U) {
				/* if encrypted increment tx counter */
				if (lll->enc_tx) {
					lll->ccm_tx.counter++;
				}
			}
#endif /* CONFIG_BT_CTLR_LE_ENC */

			offset = lll->packet_tx_head_offset + pdu_data_tx_len;
			if (offset < lll->packet_tx_head_len) {
				lll->packet_tx_head_offset = offset;
			} else if (offset == lll->packet_tx_head_len) {
				lll->packet_tx_head_len = 0;
				lll->packet_tx_head_offset = 0;

				memq_dequeue(lll->memq_tx.tail,
					     &lll->memq_tx.head, NULL);

				/* TX node UPSTREAM, i.e. Tx node ack path */
				link->next = tx->next; /* Indicates ctrl or data
							* pool.
							*/
				tx->next = link;

				*tx_release = tx;

				FORCE_MD_CNT_SET();
			} else {
				LL_ASSERT_DBG(0);
			}

			if (IS_ENABLED(CONFIG_BT_CENTRAL) && !lll->role &&
			    !pdu_data_rx->md) {
				*is_done = !pdu_data_tx->md;
			}
		}
	}

	/* process received data */
	if ((pdu_data_rx->sn == lll->nesn) &&
	    /* check so that we will NEVER use the rx buffer reserved for empty
	     * packet and internal control enqueue
	     */
	    (ull_pdu_rx_alloc_peek(3) != 0)) {
		/* Increment next expected serial number */
		lll->nesn++;

		if (pdu_data_rx->len != 0) {
#if defined(CONFIG_BT_CTLR_LE_ENC)
			/* If required, wait for CCM to finish
			 */
			if (lll->enc_rx) {
				uint32_t done;

				done = radio_ccm_is_done();
				LL_ASSERT_ERR(done);

				bool mic_failure = !radio_ccm_mic_is_valid();

				if (mic_failure &&
				    lll->ccm_rx.counter == 0 &&
				    (pdu_data_rx->ll_id ==
				     PDU_DATA_LLID_CTRL)) {
					/* Received an LL control packet in the
					 * middle of the LL encryption procedure
					 * with MIC failure.
					 * This could be an unencrypted packet
					 */
					struct pdu_data *scratch_pkt =
						radio_pkt_scratch_get();

					if (ctrl_pdu_len_check(
						scratch_pkt->len)) {
						memcpy(pdu_data_rx,
						       scratch_pkt,
						       scratch_pkt->len +
						       offsetof(struct pdu_data,
							llctrl));
						mic_failure = false;
						lll->ccm_rx.counter--;
					}
				}

				if (mic_failure) {
					/* Record MIC invalid */
					mic_state = LLL_CONN_MIC_FAIL;

					return -EINVAL;
				}

				/* Increment counter */
				lll->ccm_rx.counter++;

				/* Record MIC valid */
				mic_state = LLL_CONN_MIC_PASS;
			}
#endif /* CONFIG_BT_CTLR_LE_ENC */

			/* Enqueue non-empty PDU */
			*is_rx_enqueue = 1U;
		}
	}

	return 0;
}

#if defined(CONFIG_BT_CTLR_TX_DEFER)
static void isr_tx_deferred_set(void *param)
{
	struct pdu_data *pdu_data_tx;
	struct lll_conn *lll;

	/* Prepare Tx PDU, maybe we have non-empty PDU when we check here */
	lll = param;
	lll_conn_pdu_tx_prep(lll, &pdu_data_tx);

	/* Fill sn and nesn */
	pdu_data_tx->sn = lll->sn;
	pdu_data_tx->nesn = lll->nesn;

	/* setup the radio tx packet buffer */
	lll_conn_tx_pkt_set(lll, pdu_data_tx);
}
#endif /* CONFIG_BT_CTLR_TX_DEFER */

static void empty_tx_init(void)
{
	struct pdu_data *p;

	p = (void *)radio_pkt_empty_get();
	p->ll_id = PDU_DATA_LLID_DATA_CONTINUE;

	/* cp, rfu, and resv fields in the empty PDU buffer is statically
	 * zero initialized at power up and these values in this buffer are
	 * not modified at runtime.
	 */
}

#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_RX)
static inline bool create_iq_report(struct lll_conn *lll, uint8_t rssi_ready, uint8_t packet_status)
{
	struct lll_df_conn_rx_params *rx_params;
	struct lll_df_conn_rx_cfg *rx_cfg;

#if defined(CONFIG_BT_CTLR_PHY)
	if (lll->phy_rx == PHY_CODED) {
		return false;
	}
#endif /* CONFIG_BT_CTLR_PHY */

	rx_cfg = &lll->df_rx_cfg;

	rx_params = dbuf_curr_get(&rx_cfg->hdr);

	if (rx_params->is_enabled) {
		struct node_rx_iq_report *iq_report;
		struct node_rx_ftr *ftr;
		uint8_t cte_info;
		uint8_t ant;

		cte_info = radio_df_cte_status_get();
		ant = radio_df_pdu_antenna_switch_pattern_get();
		iq_report = ull_df_iq_report_alloc();

		iq_report->rx.hdr.type = NODE_RX_TYPE_CONN_IQ_SAMPLE_REPORT;
		iq_report->sample_count = radio_df_iq_samples_amount_get();
		iq_report->packet_status = packet_status;
		iq_report->rssi_ant_id = ant;
		iq_report->cte_info = *(struct pdu_cte_info *)&cte_info;
		iq_report->local_slot_durations = rx_params->slot_durations;
		/* Event counter is updated to next value during event preparation, hence
		 * it has to be subtracted to store actual event counter value.
		 */
		iq_report->event_counter = lll->event_counter - 1;

		ftr = &iq_report->rx.rx_ftr;
		ftr->param = lll;
		ftr->rssi = ((rssi_ready) ? radio_rssi_get() : BT_HCI_LE_RSSI_NOT_AVAILABLE);

		ull_rx_put(iq_report->rx.hdr.link, iq_report);

		return true;
	}

	return false;
}

#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_RX */

#if defined(CONFIG_BT_CTLR_DF_CONN_CTE_TX)
/**
 * @brief Get latest transmitted pdu_data instance
 *
 * @param lll Pointer to lll_conn object
 *
 * @return Return pointer to latest pdu_data instance
 */
static struct pdu_data *get_last_tx_pdu(struct lll_conn *lll)
{
	struct node_tx *tx;
	struct pdu_data *p;
	memq_link_t *link;

	link = memq_peek(lll->memq_tx.head, lll->memq_tx.tail, (void **)&tx);
	if (lll->empty || !link) {
		p = radio_pkt_empty_get();
	} else {
		p = (void *)(tx->pdu + lll->packet_tx_head_offset);
	}

	return p;
}
#endif /* CONFIG_BT_CTLR_DF_CONN_CTE_TX */
