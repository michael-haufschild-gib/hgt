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

## 10. The drift-birth fixed point: the window constant, mechanism-pinned [derived; frozen-dip closed form PROVED, constant numeric — 2026-07-04]

The §5 (HOLD-phase) tolerance `κ ≈ 0.24` was a FIT to the census edge. It is now
replaced by a mechanism-pinned, N-independent value.
Certification: `computations/mwm/drift_birth_frozen.py` (pre-registered Q1–Q4;
Q1 confirmed, Q3 confirmed) + `drift_birth_frozen.out` (pod, mpmath dps=40).
The naive full-tower first-passage was phase-fragile (scattered islands, edge
slides with birth depth — `drift_birth_fixed_point.py`, Q1/Q2 FAILED); the dip
lives in the FROZEN lattice geometry (§2–3), which is smooth.

**(i) The frozen dip, closed form [PROVED — two lines of algebra].** On the
frozen circle `S_M = a₀ e^{iβ}(1−w^M)/(1−w)`, write `e^{iβ}/(1−w) =
e^{iψ}/|1−w|`, `ψ = β − arg(1−w)`. Then `Re S_M = (a₀/|1−w|)(cos ψ − cos(ψ+Mϑ))`,
`ϑ = arg w`; the one-wrap density (§2) reaches the minimum within ⌈2π/ϑ⌉ ≤ 2
entries — inside the frozen block, before drift acts. Hence

> **frozen dip(d) = (a₀ / (2|cos 2πd|)) · (1 − cos ψ(d)),
> ψ(d) = β(d) − arg(1 − w),  β(d) = π/8 − 2πd²,  w = e^{−iπ(1+4d)}.**

Smooth and monotone increasing on `[0, ¼]`, → ∞ at the quarter-point `d = ¼`.
There is NO free birth-phase parameter: `β(d) = π/8 − 2πd²` is the certified
stationary value (doc 50 §5), the SAME object as the birth amplitude
`B(d) = cos β(d)`. The dip is fast (≤ 2 entries), matching doc 51 §6's O(1)-e-fold
absorption; drift's role is to move survivors OFF the circle on the slower N^{1/3}
scale, not to set the edge.

**(ii) The fixed point.** Birth depth `= ρ·a₀·B(d)` (ρ = birth-depth/envelope
ratio; doc 51 §8(4) birth depth ∝ B(d)). Survival ⟺ birth depth > frozen dip(d):

> **ρ·B(d) > (1/(2|cos 2πd|))(1 − cos ψ(d)).**

The edge d*(ρ) solves equality. Facts (certified):

1. **N-independent.** d*(ρ) is identical to 4 digits for N ∈ {100, 300, 1000,
   3000}: `ρ = 1.1832` gives `d* = 0.1935` at every N. The window is a genuine
   constant of the matched regime — this is WHY the census edge is N-stable.
2. **Parameter-free within 4%.** At the natural scale `ρ = 1` (birth depth =
   marginal envelope a₀, no fine-tuning): `d* = 0.1855`, `2πd*² = 0.216` — vs
   census `d* = 0.194`, `2πd*² = 0.236`. A 4%/9% match with ZERO free parameters.
3. **Exact edge = the reach ratio.** `d* = 0.194` is reproduced at `ρ = 1.183`,
   which sits at the low end of the independently-measured REACH ratio
   R ∈ [1.10, 2.11] (§9b, doc 46 §5). So the fit tolerance κ of §5 is replaced by
   a MEASURABLE physical ratio ρ = reach, with a matching independent value.

**(iii) Status.** The frozen-dip closed form is PROVED algebra. The constant
`2πd*² = 0.216` (parameter-free) → `0.236` (at ρ = min-reach) is a mechanism
derivation at numeric grade, N-independent — no longer a fit. Open to close it to
a theorem: (a) verify ρ = reach directly (compute `|P_N|/(η|Φ′|)` in the frozen
model and check it equals the birth-depth/envelope ratio at the edge); (b) the
growing envelope `a_m = 2(N−m)^{−1/2}` vs the constant-envelope circle shifts the
edge down slightly, needing ρ a touch above 1.18 — recompute the antitone-envelope
dip in closed form (doc 50 §3 master bound gives the same denominator, so the
correction is an explicit Abel factor); (c) the anti-correlation of reach and d
(§9b) is the sign that ρ is edge-selected, not per-event free — pin which config
saturates the edge.

**What this opens:** the window constant is now a computable output of the
lattice, not an input. Next: push (a)–(c) to a closed ρ; and run the SAME
frozen-dip fixed point at the p ≈ ½ suppression (B drops 2.4×, doc 50 §5) to
derive the SECOND measured fact — that the near-half-integer band is empty at the
amplitude level, not just the phase level — from one mechanism.

## 11. Half-band test: the two census facts are TWO mechanisms, not one [2026-07-04]

Pushed doc 51 §10's frozen fixed point to (b) the envelope correction and to the
full band `d ∈ [0, ½]`, to test whether ONE mechanism gives both the low edge
`d* = 0.194` AND the half-integer emptiness (p ≈ ½). Certification:
`computations/mwm/drift_birth_halfband.py` (pre-registered R1–R4) +
`drift_birth_halfband.out` (pod). Result: the one-mechanism hope is REFUTED, and
the refutation cleanly SEPARATES the two facts.

**(b) envelope correction — NOT negligible, ~10% [correcting §10's "4%"].**
The true exact-step antitone-envelope dip (walk the frozen block with
`a_m = 2(N−m)^{−1/2}` and the exact `Δ(m)`) differs from the constant-envelope
closed form by rel-gap 0.07–0.39 (non-monotone, ~10% at large N). So the closed
form is a leading-order model good to ~10%, and `ρ* ≈ 1.18` carries ~10% model
uncertainty. The §10 agreement is at the ~10% MECHANISM level, not 4%-precise; the
exact-value close of ρ needs the carrier-level birth normalization (still open,
= the doc 46 reach/(BVAL) object). (a)/(c) do NOT close from this model.

**The half-band test [R2, REFUTED — and this is the finding].** At `ρ = 1.18` the
frozen fixed point gives survival set `[0, 0.192] ∪ [0.310, 0.500]` — it RE-OPENS
near `d = ½`. Census has NOTHING above 0.194. The frozen SURVIVAL dip therefore
does NOT explain the half-emptiness; it favors it. Exact reason (table, R3): at
`d = ½`, `|cos 2πd| = 1` is maximal ⟹ collective dip is MINIMAL (`0.31 a₀`, the
p = ½ maximal-suppression of doc 50 §2), so even the 2.4×-reduced birth
`B(½) = 0.383` beats it. The dip amplification `1/|cos 2πd|` blows up only toward
the quarter-point `d = ¼`, which is what kills the low band's neighbourhood
`(0.194, 0.30)` — phase-limited, correct.

**Consequence — the census facts split by mechanism:**
- **Low edge `d* = 0.194`** ← SURVIVAL (frozen dip; §10). Robust: low edge moves
  0.184 → 0.204 as ρ: 1.0 → 1.5, census 0.194 at ρ = 1.18.
- **Half-integer emptiness (p ≈ ½)** ← CREATION, not survival. Pairs near p = ½
  are 3× less likely to be BORN (doc 50 §6's measured birth 1-periodicity) and
  born shallower (B suppression is a birth-DEPTH property, doc 51 §8(4)). The
  frozen dip favouring `d = ½` proves the emptiness there is UPSTREAM of the
  survival walk. This CORRECTS §5's parenthetical: the 2.4× B-suppression is real
  but acts on the creation side (shallow/rare births), NOT as a survival dip.

**What this opens:** the survival mechanism (frozen dip) owns exactly one census
fact; the other is doc 52's creation rate. Next: run the creation-rate reader
(`A′(t) = θ′ − 2 Im(F_N′/F_N)`, births = tangential crossings, doc 52) across
`p ∈ [0, ½]` and test whether the birth INTENSITY carries the `B(p)` = |cos(π/8 −
2πp²)| envelope — if births ∝ B(p)² (intensity), the 1-periodic birth suppression
and the 2.4× depth cap fall out of ONE creation object, and the full census
(low edge from survival, half from creation) is two clean mechanisms welded at
the same birth phase π/8. That weld — survival and creation sharing β(d) = π/8 −
2πd² — is the object to make precise.
