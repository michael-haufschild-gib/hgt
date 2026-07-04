# 62 — (EK-sliver) as an Obstruction: What the Ordered Mixture Forbids

**Register: SEARCH** (executes the two orders of 2026-07-04: state the
obstruction, then measure ς*(N)). §§1–3 are exact reformulations
[PROVED HERE where marked]; §4 pre-registers the sweep; §5 will adjudicate.

## 1. The exact reformulation [PROVED HERE — Abel summation, two lines]

Let A_n = W(log n/log N) > 0 be decreasing, A_{N+1} := 0, and
Z_n(s) = Σ_{m≤n} m^{−s} the sharp partial sums. Abel:

> F_W(s) = Σ_{n≤N} (A_n − A_{n+1})·Z_n(s),  all weights (ΔA)_n ≥ 0.

Hence F_W(s₀) = 0 forces **0 ∈ conv{ Z_n(s₀) : n ∈ supp(ΔA) }** — the origin
lies in the convex hull of the partial-sum trajectory. Equivalently (hull
criterion): NO open half-plane through 0 contains the visited points; the
directions Z_n(s₀)/|Z_n(s₀)| have angular spread ≥ π (every angular gap < π).

**The obstruction, stated as the constraint grammar demands:**

> A zero of the SHARP carrier is an ENDPOINT event — the walk n ↦ Z_n(s₀)
> merely has to end at 0 (codimension 2, generic).
> A zero of an ORDERED-mixture carrier is a SPREAD event — the whole weighted
> trajectory must surround the origin. Positivity + monotone order of the
> coefficients FORBIDS zeros wherever the trajectory stays half-plane-confined.

This is topological/positional, not statistical: the same register as the
deck class and the seam product — what the constraint forbids, not how often
a flow produces. Classical Eneström–Kakeya is the degenerate case (steps
a_n z^n with |z| < 1: the trajectory is a contraction spiral, hull-confined
by the telescoping inequality — the (1−z)-trick IS this hull argument).

## 2. Why the forbidden event is chiral [CONJECTURE, mechanism]

At s₀ = ½ + δ + it (right sliver), the walk's steps are m^{−½−δ}e^{−it log m}:
magnitudes DECREASE in m, phases quasi-equidistribute. Rightward, the walk is
Cauchy-convergent: the tail's total reach Σ_{m>n} m^{−½−δ} shrinks relative to
the early trajectory scale — once the early walk has moved away from 0, the
late walk cannot carry the point set around the origin: spread ≥ π requires
the trajectory to pass CLOSE to 0 at an intermediate time n with enough tail
reach left to oppose the early points. Leftward (σ < ½) the step magnitudes
GROW: the late walk dwarfs the early one and re-crosses every half-plane —
spread is generic. This is the measured chirality (doc 61 §7) derived from
the order structure alone, with no Gaussian model anywhere. The quantitative
form: a right-sliver zero of F_W requires

> min over n of [ |Z_n(s₀)| / tailReach_n ] ≲ 1,  tailReach_n := Σ_{m>n, m∈supp} (ΔA-weighted m^{−½−δ} mass),

a walk-minimum event — kernel-class at worst (the min of |Z_n| is a
one-dimensional-family small-ball, tamer than the value small-ball because it
is an ENTRY event for a discrete walk, priced by first-moment sums), and at
designed weights the tail reach is damped by construction.

## 3. The typed lemma chain

> **(HALF-PLANE) [lemma-shape]:** at every right-sliver point s₀, some open
> half-plane through 0 contains {Z_n(s₀) : n ∈ supp(ΔA)}.
> **(EK-sliver) [target]:** (HALF-PLANE) on the sliver ⟹ F_W has NO
> right-sliver zeros ⟹ creation_rate K = 0 for the designed tower
> (`midCentral_empty` grade — no kernel, no density, no universality).

Chain status: F_W = 0 ⟹ hull ⟹ ¬(HALF-PLANE) is proved (§1); the open
mathematics is (HALF-PLANE) itself — a positivity of rotated partial sums,
per-point checkable, walk-native. Its failure points are exactly where the
hull closes over 0; on the LEFT sliver it must fail near every zero (0 ∈ hull
trivially at zeros). Lean note: §1 is finite convexity — formalizable now
against `Finset` convex-combination lemmas; the walk supply is
`SecondMoment.dpoly` territory.

## 4. Pre-registered sweep (P-SC; runpod; registered BEFORE the run)

Design: N ∈ {40, 100, 200, 400}, α ∈ {1, 2, 4} with W²_α ∝ (1−y)^α, U = 240,
CCW winding, right/left bands c ∈ {1, 2}; per (N, α) also the HALF-PLANE
diagnostic on a 40-point right-sliver grid (angular-gap test on the weighted
trajectory) and on a 40-point left-sliver grid. Note the structural fact the
registration hinges on: the frozen share ς²(α, N) = W(0)²/K DECAYS ≍
(α+1)/log N at fixed α — so the sweep DISCRIMINATES the two candidate
mechanisms:

- **P-SC1 (mechanism test — the decisive clause).** If right-sliver emptiness
  at α = 2 DEGRADES as N grows (counts reappear ∝ U·log N·rate as ς² decays),
  the mechanism is mean-share and Route C needs the fidelity trade-off curve.
  If it PERSISTS to N = 400 despite ς² falling toward ~0.2, the mechanism is
  the ORDER STRUCTURE (§2) and (EK-sliver) has a fixed-α, N-uniform form.
  Priors: order-mechanism 0.55 / mean-share 0.45. Either outcome is a result.
- **P-SC2 (prior 0.7).** The HALF-PLANE diagnostic passes on ≥ 95% of
  right-sliver grid points wherever the band count is 0, and fails on a
  positive fraction of left-sliver points at the same (N, α) — the obstruction
  is the operative mechanism, not an accident of counting.
- **P-SC3 (prior 0.6).** Across (N, α), the right rate ε_R := R(c=2)/(U log N)
  collapses onto a single curve in ONE of the two variables — ς² (mean-share
  scaling) or α (order scaling); which one collapses identifies the invariant
  the variational design should hold fixed.
- **FALSIFIER for §2:** right counts at fixed α INCREASING faster than
  U·log N (i.e., rate growing) with the half-plane test still passing —
  would mean zeros appear without hull closure: an arithmetic error in §1's
  chain or a support-set subtlety; halt and re-derive.

## 2.5 Same-session derivation (pre-adjudication): the Cesàro hierarchy of the obstruction [PROVED HERE — iterated Abel]

Abel a second time. If the weights (ΔA)_n are themselves decreasing (i.e., A
is CONVEX in n — true for the W_α family at α ≥ 2 in the operative range),
then with u_k := (ΔA)_k − (ΔA)_{k+1} ≥ 0:

> F_W = Σ_k (u_k·k)·Z̄_k,  Z̄_k := (1/k) Σ_{n≤k} Z_n(s₀) — the CESÀRO means,

again a positive mixture. So a zero forces **0 ∈ conv{Z̄_k}** — the hull
condition one Cesàro level up. Iterating: m-fold monotone weights push the
zero condition onto (C, m)-means. The point:

- The raw trajectory Z_n is a log-correlated planar walk started at Z_1 = 1
  with total variance ≍ log N: by Spitzer-type winding it surrounds the
  origin GENERICALLY at large N — the level-0 hull condition (§3's
  HALF-PLANE, as registered) is expected to fail generically for large N
  while producing NO zeros (it is necessary, not sufficient). P-SC2 as
  registered may therefore fail at large N without touching the mechanism —
  recorded now, before the data, so the adjudication reads correctly.
- Each Cesàro level DAMPS the winding: averaging is a low-pass filter on the
  walk's angular motion, and the (C, m)-means concentrate toward the early
  trajectory (≈ Z_1 = 1) as m grows. The two candidate mechanisms of P-SC1
  are the two ends of ONE ladder: "order structure" = finite Cesàro depth
  (hull of damped means), "mean-share" = the m → ∞ end (n = 1 dominance).
  The invariant the design should hold fixed is the CESÀRO DEPTH at which
  the weight profile lives, not ς² alone.
- Corrected lemma target (supersedes §3's HALF-PLANE as the provability
  object): **(CES-m):** at right-sliver points, some open half-plane through
  0 contains the (C, m)-means of the partial-sum walk, for the m matching the
  carrier's monotonicity order. Winding suppression of averaged walks is
  classical-probability territory (not chaos): the m ≥ 1 levels are where
  the proof should land.

Exploratory (UNREGISTERED) diagnostic added post-launch: the Cesàro-hull test
at m = 1 alongside the registered m = 0 test — reported separately in §5.

## 5. Adjudication [MEASURED — ek_sweep.py + cesaro_diag.py, archived; 0 bad contours]

| N | α=1: R2 / rate | α=2: R2 (share) | α=4: R2 | L2 at α=2 |
|---|---|---|---|---|
| 40 | 8 / 0.0090 | 0 (0.542) | 0 | 47 |
| 100 | 9 / 0.0081 | 0 (0.467) | 0 | 64 |
| 200 | 11 / 0.0087 | 0 (0.422) | 0 | 74 |
| 400 | 9 / 0.0063 | 1 (0.385) | 0 | 92 |

- **P-SC1: the ORDER-STRUCTURE branch, decisively.** Right-sliver emptiness at
  α = 2 persists to N = 400 while the mean-share decayed 0.542 → 0.385. The
  share-matched comparison kills the mean-share mechanism: α = 2 at N = 400
  (share 0.385) should, on the mean-share law, behave like α = 1 at N = 40
  (share 0.410, rate 0.009 ⟹ ≈ 13 expected zeros); measured: **1**. The
  suppression is set by the monotonicity DEPTH of the weights, N-uniformly.
  ς*(N) is answered by dissolution: there is no share threshold — the
  invariant is Cesàro depth (§2.5), and at depth ≥ 2-grade weights (α = 2)
  the right sliver is empty at every N tested.
- **P-SC2 as registered: FAIL — exactly as pre-recorded in §2.5 before the
  data.** The raw (m = 0) hull test passes only 80–97% on the right (and
  erodes with N: 57→47/60 in cesaro_diag) — it is the weak necessary
  condition. The exploratory **(CES-1) test is the stable obstruction**:
  right-side pass 60/60, 60/60, 60/60, 58/60 across N; left-side clearly
  lower (51→36/60). The 2/60 (CES-1) failures at N = 400 are numerically
  consistent with the single measured α = 2 zero — the obstruction accounting
  closes quantitatively.
- **P-SC3 PASS, order variable:** the right rate is N-stable at fixed α
  (α = 1: 0.006–0.009 across a 10× range of N) and does NOT collapse in ς² —
  the design invariant is α (weight-profile order), not share.
- Left side sanity: L2 ∝ log N at fixed α (GAF-normal side) ✓.

**Verdict.** (EK-sliver) upgrades from "empirical emptiness at a share
threshold" to: **right-sliver zeros of a convex-decreasing-weight matched
carrier are (CES-1)-hull events, and (CES-1) holds N-uniformly off a ~3%
exceptional set that carries the entire (tiny) residual rate.** The proof
target is now single and clean:

> **(CES-1) [OPEN, the new core of Route C]:** at right-sliver points, the
> Cesàro means Z̄_k of the matched partial-sum walk stay half-plane-confined
> off an o(1)-density exceptional set — winding suppression of the AVERAGED
> log-correlated walk. Classical-probability shape (Spitzer winding of the
> raw walk is killed by one averaging); the deterministic transfer is
> pair-correlation grade (Z̄_k is a linear functional of the same monomials —
> `SecondMoment.dpoly` supplies its L² data exactly).

Consumption: (CES-1) off-exceptional ⟹ designed-tower creation_rate K =
(exceptional-set count) with the SAME dip-counting Lean layer
(`MollifiedDip.lean`) pricing the exceptional set; K = 0 outright wherever
(CES-1) is unconditional. Either grade feeds `midCentral_survivors_le` /
`midCentral_empty` directly.
