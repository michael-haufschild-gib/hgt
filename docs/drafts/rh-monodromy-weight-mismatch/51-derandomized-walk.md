# 51 — The De-randomized Walk: Rotation, Drift, and the Hold-Phase Law

**Register: SEARCH** (task #152; the first-passage write-out of doc 49 §3(i) on
doc 48's exact dichotomy, with doc 50's collapse replacing all randomness).
No probabilistic language survives: every "probability" below is a
deterministic excursion bound or an explicitly open lemma.

## 1. The walk, exactly

A pair of depth η² at height t_B, swept by entries j = k+1, …, N. By the
dichotomy (doc 48 §2) each entry moves the depth by one real number; in the
top block (offset m = N − j ≪ N) the lattice (doc 49 §2 + doc 50 §1) gives

> c_m = a_m · Re(e^{iβ} w^m),  w = e^{−iπ(1+4p)},  a_m ≈ 2(N−m)^{−1/2}/‖g‖,

with β the pair's local frame phase (sign(g₀), birth phase). Partial pushes:
S_M = Σ_{m<M} c_m. Absorption (pair lands ON the line) at the first M with
η² + S_M ≤ 0. **Survival floor [PROVED, interface]:** survival through M
entries forces η² > −min_{M′≤M} S_{M′} — the maximal negative excursion.

## 2. The partial-sum geometry [PROVED HERE]

For constant envelope, S_M = a·Re(e^{iβ}(1 − w^M)/(1 − w)): the trajectory
lies on a circle through 0 of radius r = a/‖1−w‖ = a/(2|cos 2πp|), traversed
by the rotation m ↦ w^m. Exact facts:
1. |S_M| ≤ 2r for all M (doc 50 §3; antitone envelopes likewise).
2. One-wrap density: for ϑ = π(1+4p) mod 2π ≠ 0 and any target angle ψ, the
   orbit angle mϑ lands in [ψ, ψ+ϑ) at m = ⌈ψ/ϑ⌉ — the orbit is ϑ-dense in
   one wrap. Dips (negative excursions) of size up to
   (depending on β) 2r·(1 − O(ϑ)) are VISITED within ⌈2π/ϑ⌉ entries whenever
   the circle's lowest point is negative.

## 3. Frozen-alignment escape — why rotation alone cannot close [PROVED HERE]

The circle passes through 0; its position is set by β. If β puts the circle in
{Re ≥ 0} (kill direction downward), the walk NEVER dips: min_M S_M = 0 at
lattice order, and the pair survives every wrap. Rotation alone is therefore
insufficient for absorption — matching doc 47's frozen-phase escape and the
film's creation events. **De-randomization must come from elsewhere; it comes
from the drift.**

## 4. The drift dip [OPEN — elementary-shaped, exact inputs proved]

Doc 50 §4: the rotation number drifts, dp_eff/dm ≈ m/N, so the circle-plus-
alignment geometry rotates through ALL orientations as the sweep proceeds;
the frozen half-plane of §3 cannot persist beyond the block where the
accumulated drift phase 2πm³/(3N) stays ≪ 1.

> **(DRIFT-dip) [OPEN]:** for the drifting walk with envelope a_m and any
> alignment β, every entry-interval [M, M + L] with L ≥ C·N^{1/3} contains a
> negative excursion of size ≥ c·a_M/|cos 2πp_eff| evaluated at the interval's
> worst orientation — in particular a dip ≥ c·a_M once p_eff's orientation
> sweep crosses the down-alignment.

Shape of proof: blockwise exact geometric sums (doc 50 §3) + the one-wrap
density of §2 + the certified drift formula; no cancellation subtleties — the
open content is bookkeeping the orientation sweep against the envelope decay
a_M ~ 2(N−M)^{−1/2}. With (DRIFT-dip): a pair whose depth is below the
running dip scale is absorbed within O(N^{1/3}) entries of its birth — only
pairs born ABOVE the dip scale at a protected phase survive to the census.

## 5. The hold layer: the (HOLD-phase) law [OPEN CORE, typed]

The census (doc 50 §6) fixes the survival support at {d(p) ≤ 0.194} =
{2πd(p)² ≤ 0.236 rad}, refuting every ½-periodic tail-only law. The matching
mechanism, from the certified stationary value φ_res ≡ πn₀ − 2πd² + π/8:

- **In-phase (hold) component** ∝ cos(2πd² − π/8-offset): sustains the pair
  (the measured (REACH) ratios 1.10–2.11 are its census trace);
- **Quadrature component** ∝ sin(2πd²): feeds the kill direction as the
  frozen window unwinds — the resonant term's own misalignment absorbs the
  pair it created.

> **(HOLD-phase) [OPEN]:** a mid-band pair survives the completed tower only
> if the resonant stationary phase offset satisfies tan(2πd²) ≤ κ, with κ the
> dichotomy margin of the hold configuration; census: κ ≈ tan(0.236) ≈ 0.24.

This is the one place the surviving window's CONSTANT lives. Everything
½-periodic is proved; everything 1-periodic funnels through this single
tolerance. (B(p) = |cos(π/8 − 2πd²)| additionally caps birth depth: 2.4×
suppression at d = 1/2 — the second, amplitude-level reason p ≈ 1/2 is empty.)

## 6. Regime split [structure, from proved parts]

- **k ≪ N (early births):** step angles t/j ≫ lattice scale, varying by ≫ 2π
  per entry — no frozen geometry exists; dips at every scale; absorption
  within O(1) e-folds of birth. This is why the census's odd events all sit
  at the truncation edge of their own height (p-locality), and why doc 44's
  survivors were geometry-irreducible.
- **k ~ N (top block):** the lattice regime of §§2–5; all census survivors.

## 7. Assembly: (MID-central), fully typed

(MID-central) ⟸
1. collision dichotomy [PROVED, doc 48; Lean SweepDichotomy];
2. lattice collapse + master push bound [PROVED, doc 50; Lean #151];
3. (DRIFT-dip) [OPEN, elementary-shaped, §4];
4. (HOLD-phase) tolerance [OPEN CORE, §5] — the surviving window's constant;
5. creation-rate control [doc 52] — the population entering the walk.

The census then reads: survivors exist exactly in the (HOLD-phase) window and
nowhere else — (MID-central) in its final form says the window's pairs are
swept before matched level, EXCEPT possibly the resonance window itself, whose
pairs the deck relation counts as the (SWEEP-margin) boundary term.

## 8. What this opens

1. Prove (DRIFT-dip): pure bookkeeping over certified formulas — Lean-ready
   shape after the paper pass (the one-wrap lemma is `Int.ceil` arithmetic).
2. (HOLD-phase): derive κ from the dichotomy applied to the resonant term's
   own quadrature — a single-term self-interaction computation; numerically
   falsifiable against the 0.236 edge without new runs.
3. (DEEP-FATE) stays the one sanctioned computation, now sharper: track ONE
   wrong-sign pair with the drift dips on; prediction — absorbed within
   O(N^{1/3}) entries, no η ~ N^{−1/4} deepening (census bound: max η 0.178).
4. The B(p)-envelope prediction: birth depth ∝ B(p) — gradable if a future
   census stores birth-level depths, not just final ones.

## 9. Same-session sharpening: the slip identity and the reach coupling

(a) **Slip identity [PROVED — the lattice again]:** the resonant term's phase
slip between its stationary point and the entry at fractional offset d is
2πd² (θ″ = 1/2t against entry spacing 4πN: slip after k entries = 2πk²). So
the (HOLD-phase) window of §5 reads: **survival while the resonance's own
slip stays under the budget κ_slip ≈ 0.236 rad** — the window edge d* = 0.194
is the budget exhausted, not a new constant.

(b) **Reach coupling [ANALYSIS + testable]:** the dichotomy applied to the
holding term gives survival iff cos(slip)·R ≥ 1, R the (REACH) ratio. Census
consistency: at the edge cos(0.236) = 0.972 requires R ≥ 1.03 (all measured
R ≥ 1.10 ✓). The naive corollary — max-reach configurations (R ≈ 2.1) could
survive to slip ≈ 1.08, d ≈ 0.41 — is REFUTED by the census (0 events in
(0.194, 0.855)): reach and slip must be anti-correlated, as doc 46 §5 already
noted ("the (HOLD) phase window and the (REACH) amplitude window are one
object"). But the leading cosines are all ≈ 1 in the window
(cos(x)·|cos(π/8 − x)| ∈ [0.92, 0.97] on x ∈ [0, 0.236], nearly flat), so the
anti-correlation lives in the configurational factor |H| — the open kernel of
(HOLD-phase), now isolated to one object.

(c) **Edge shape [measured, undecided]:** the 19 survivor d-values are
near-uniform on [0, 0.194] with no thinning at the edge — favoring a HARD
slip-budget edge over a soft configurational tail; 19 points cannot settle
it. Discriminating measurement (when a census extension is next sanctioned):
the d-histogram shape near 0.19 and per-event (d, R) pairs — store both.
