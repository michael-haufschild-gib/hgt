# Moving-Hermite supercritical-slope no-go

Status: Stage 3 — formalized in Lean 4

## Exact claim

[LEAN-PROVED] Let `depth : ℕ → ℕ` and `alpha : ℝ`. If

`5/11 < alpha`

and eventually

`alpha * N ≤ depth N`,

then the canonical point-Hermite counterterm

`N ↦ boundaryHermiteJetCounterterm N (depth N)`

is not `SquarefreeHalfCountertermAdmissible`.

This is an unconditional no-go for every eventual linear depth slope strictly above `5/11`.

## Frontier audit

[CORPUS] `boundaryHermiteJet_correctedSource_euler_eq_modeSum` in
`SquarefreeConvolutionHalfMovingHermiteArithmeticHighDepthNoGo.lean` gives the exact
exponential-mode/Poisson-tail decomposition at one fixed Euler point.

[CORPUS] `realPoissonUpperTail_le_chernoff` in the same module proves

`P(Poisson(x) ≥ M) ≤ exp(-t M + x (exp t - 1))`

for `x,t ≥ 0`.

[CORPUS] `Real.exp_bound_div_one_sub_of_interval` in Mathlib proves

`exp t ≤ 1/(1-t)`

for `0 ≤ t < 1`.

[LOCAL-RESEARCH] The low-depth theorem
`no_cofinal_locallyBounded_boundaryHermiteJetCounterterm_of_eventually_depth_le_slope_lt_five_div_eleven`
already excludes every eventual upper slope below `5/11` by an interior pole witness.

[LITERATURE] Exponential tilting is the classical Chernoff mechanism; the local application here
is a deterministic exponential-series tail identity, not a novelty claim. Primary provenance:
H. Chernoff, *A Measure of Asymptotic Efficiency for Tests of a Hypothesis Based on the Sum of
Observations*, Ann. Math. Statist. 23 (1952), 493–507,
<https://www.jstor.org/stable/2236576>. Direct Poisson-tail literature includes P. W. Glynn,
*Upper Bounds for Poisson Tail Probabilities*, Operations Research Letters 6 (1987), 9–14,
<https://web.stanford.edu/~glynn/papers/1987/G87b.html>.

Verdict: [BRIDGE]. The tail bound is classical. New local content is exact parameter matching to
the arithmetic moving-Hermite source; no scientific-priority claim is made.

## Complete proof

Write

`b = 6/11`, `c = 5/11`,

and choose

`d = (alpha + c)/2`,

`sigma = b + d`,

`t = (alpha - d)/(2 alpha)`.

Since `c < alpha`, one has

`c < d < alpha`, `1 < sigma`, and `0 < t < 1`.

Put

`q = t/(1-t)`

and

`gamma = t * (alpha - d/(1-t))`.

The elementary exponential bound gives

`exp t - 1 ≤ 1/(1-t) - 1 = q`.

Moreover,

`1-t = (alpha+d)/(2 alpha)`

and therefore

`d/(1-t) = 2 alpha d/(alpha+d) < alpha`,

where the strict inequality is exactly `d < alpha`. Thus `gamma > 0`.

At the fixed Euler point `sigma`, the exact mode decomposition is

`S_N(sigma) + C_{N,K}(sigma)`

`= Σ_{n<N} LSeries.term a sigma n ·`

`  (1 - exp(-x_{N,n}) Σ_{j<K+1} x_{N,n}^j/j!)`,

with

`x_{N,n} = (N - log n)d`.

For every `n<N`, `log n ≤ n ≤ N` and `0 ≤ log n`; hence

`0 ≤ x_{N,n} ≤ dN`.

The `n=0` Dirichlet term is zero. For every other `n`, `sigma ≥ 0` and the squarefree-half
coefficient has norm at most one, so

`‖LSeries.term a sigma n‖ ≤ 1`.

The Poisson Chernoff estimate and `exp t - 1 ≤ q` give, termwise,

`‖term_n‖ ≤ exp(-t(K+1) + dN q)`.

There are at most `N` terms. Therefore

`‖S_N(sigma) + C_{N,K}(sigma)‖`

`≤ N exp(-t(K+1) + dN q)`.

On the eventual set where `alpha N ≤ K`, use `K+1 ≥ K` to obtain

`-t(K+1) + dNq ≤ -t alpha N + dNq = -gamma N`.

Consequently

`‖S_N(sigma) + C_{N,depth N}(sigma)‖ ≤ N exp(-gamma N) → 0`.

Assume the counterterm were admissible. Since `sigma>1`, source fidelity gives

`C_{N,depth N}(sigma) → 0`,

while ordinary Euler-chamber convergence gives

`S_N(sigma) → LSeries squarefreeConvolutionHalf sigma`.

Thus the corrected source tends simultaneously to that L-series value and to zero. Hence

`LSeries squarefreeConvolutionHalf sigma = 0`.

But the exact square identity in the Euler chamber says

`LSeries squarefreeConvolutionHalf sigma ^ 2 = zeta(sigma)/zeta(2 sigma)`.

Both zeta factors are nonzero because `Re(sigma)>1` and `Re(2 sigma)>1`. The quotient is
nonzero, contradiction. This proves the claim.

## Hostile audit

- Point `sigma` depends only on fixed `alpha`, not on `N`; admissibility applies at it.
- No unproved asymptotic or probability theorem remains: the mode identity and Chernoff estimate
  already exist in Lean, and `N exp(-gamma N) → 0` is in Mathlib.
- `n=0` is harmless because its L-series term is definitionally zero.
- Arbitrarily large `alpha` causes no domain issue: `sigma>1` is enough for source convergence and
  zeta nonvanishing.
- Strictness is essential. At `alpha=5/11`, every Euler point has gap `d>5/11`, so this argument
  cannot make `d<alpha`.

## Positive survivor and open core

[PAPER-PROVED] The constant `5/11` is the exact phase boundary shared by the two independent
point-Hermite obstructions: it is the distance from the Hermite anchor `6/11` to the Euler boundary
`1`. Interior pole witnesses close every strict lower slope; fixed Euler witnesses close every
strict upper slope.

[OPEN CORE] Exact critical schedules at slope `5/11`, schedules without eventual one-sided linear
bounds, and distributed/nonlocal transition schemes are not decided by this theorem.

## Lean verification

- Module:
  `formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfMovingHermiteSupercriticalSlopeNoGo.lean`
- Capstone:
  `not_squarefreeHalfCountertermAdmissible_boundaryHermiteJetCounterterm_of_eventually_slope_le_depth_gt_five_div_eleven`
- Direct check:
  `lake env lean GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfMovingHermiteSupercriticalSlopeNoGo.lean`
- Targeted build:
  `lake build GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingHermiteSupercriticalSlopeNoGo`
  — passed, `13306/13306` jobs.
- Axiom audit for mode identity, Chernoff envelope, convergence theorem, and capstone:
  `[propext, Classical.choice, Quot.sound]` only.
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean` imports the module.
