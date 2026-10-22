# LA critical-ray half-unit shift

- **ID:** LA-C6-20260929
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / PAPER-PROOF DRAFT
- **Source:** C5 exact moving-shell coordinate and full-tail jet limit; `la-frontier-conjecture-loop-2026-09-29.md`.
- **Completion:** Intermediate research only. User's goal ends only with an unconditional Lean RH proof/falsification.
- **Novelty:** No indexed hit from the exact or broadened lexical searches recorded in the loop log. Universal literature/training-data absence is unverified. No numerical experiment.

## Statement

Let `a=(N+1)^2` and let `F_N` be the literal canonical theta-prefix cosine transform. For every fixed real `s`, conjecture

`a exp(2pi a) (F_N'^2-F_N F_N'')(2pi a+s) -> (1-2s)/(16pi)`.

The leading C5 limit is zero on this ray. This refinement predicts eventual positivity at `s=0`, negativity at `s=1`, and a first-Laguerre boundary at `2pi (N+1)^2+1/2+o(1)`. The last phrasing requires an additional existence/localization argument for actual roots of the margin; the displayed limit alone proves signs at fixed offsets, not uniqueness of a transition.

## Exact first-order source calculation

Use the verified C5 coordinate

`q_a(u)=a log(1+u/a)/2`,
`A_a(u)=pi (1+u/a)^(1/4) (2pi(1+u/a)-3/a) exp(-pi u)`.

For every fixed `u>=0`, the proposed first-order limits are

`a(q_a-u/2) -> -u^2/4`,
`a(A_a-2pi^2 exp(-pi u)) -> pi((5pi/2)u-3) exp(-pi u)`.

The phase limit follows from the actual mathlib theorem `Real.abs_log_sub_add_sum_range_le` with `x=-u/a`, `n=2`, after `a>2u`. Its error, multiplied by `a^2`, tends to zero. The amplitude limit follows by differentiating `(1+epsilon*u)^(1/4)` at `epsilon=0` and expanding the explicit affine factor. These are symbolic analytic limits, not computed samples.

For the complex zeroth jet, writing `c=pi-i lambda/2`, the correction is

`B_C(lambda)=(9pi^2/2)/c^2-3pi/c-2pi^3/c^3`.

Indeed the amplitude correction integrates to `(5pi^2/2)/c^2-3pi/c`. The phase correction integrates to `-i lambda pi^2/c^3`; substituting `i lambda=2(pi-c)` gives the displayed expression. Set `B=Re B_C` and `H=8pi^3/(4pi^2+lambda^2)`.

For a fixed jet order `k`, differentiating the same integrands in `lambda` predicts correction `B^(k)`. At `lambda_a=2pi+s/a`, the total correction is `B^(k)(2pi)+s H^(k+1)(2pi)`.

The exact candidate complex correction at every fixed order is, with `z=i/2`,

`B_k(lambda)=z^k[(9pi^2/2)(k+1)!/c^(k+2)
                -3pi k!/c^(k+1)-pi^3(k+2)!/c^(k+3)]`.

Before substituting `i lambda=2(pi-c)`, the corrected integrand is
`z^k exp(-c u)[pi^2(5/2-k)u^(k+1)-3pi u^k
               -i lambda pi^2 u^(k+2)/2]`.
This derives the coefficient directly from amplitude, jet power, and phase,
without exchanging an unproved asymptotic derivative. The shifted correction
is `B_k(lambda)+s Z_(k+1)(lambda)`, where `Z_k` is C5's verified complex limit.

## Domination that must be checked

1. For all `a>=1,u>=0`, prove `0<=a(u/2-q_a)<=u^2/4`. The lower estimate uses `log(1+z)<=z`; the upper uses `log(1+z)>=z-z^2/2`, obtained from derivative `z^2/(1+z)>=0` of `log(1+z)-z+z^2/2` on `z>=0`.
2. Concavity of `r^(1/4)` on `r>=1` gives `0<=a((1+u/a)^(1/4)-1)<=u/4`. Expand the exact amplitude to bound `a|A_a-A_0|` by a fixed polynomial of degree two in `1+u`, times `exp(-pi u)`.
3. The unit-circle phase is Lipschitz: `|exp(i lambda q)-exp(i lambda r)|<=|lambda| |q-r|`. For powers, factor `q^k-r^k` as a finite sum and use `0<=q<=r=u/2`. Thus every first-order jet difference is bounded by a polynomial in `1+u` times `exp(-pi u)`, uniformly on the bounded sequence `lambda_a`. Gamma integrability gives dominated convergence for `k=0,1,2` (and every fixed `k`).
4. Retain all later omitted shells. The verified bound is `B_k (j+1)^2 exp(-pi(2(N+1)j+j^2))`. For `j>=1`, use `exp(x)>=x^2/2` with `x=pi(N+1)j` to get
   `a exp(-2pi(N+1)j)<=2/(pi^2 j^2)`.
   Hence `a` times the later-shell jet is bounded by `8 B_k/pi^2 * exp(-pi j^2)`, a summable majorant. Each fixed later shell tends to zero at this scale. Tannery removes the entire later tail.
5. The existing Cauchy estimate gives full Xi jets bounded by a polynomial times `exp(-pi t/4)`. At `t=2pi a+s`, an additional factor `a` still leaves exponential decay since `pi/2>1`. Thus full Xi contributes zero to every fixed first-order normalized jet.

For step 3 a completely explicit majorant is available. Write `r=u/2` and
split the jet difference into amplitude, power, and exponential differences.
Finite-power factorization gives
`a|q_a^k-r^k|<=k(1+u)^(k+1)/4` (including `k=0`, whose difference is zero).
Consequently at the shifted critical frequency the scaled full integrand
difference is bounded by

`[pi(3pi+3)+pi^2 k/2+pi^3+pi^2|s|]
 (1+u)^(k+2) exp(-pi u)`.

This fixed polynomial majorant is integrable for every fixed `k,s`.

These steps are the remaining formal/paper audit targets. No first-order dominated-convergence theorem is yet in Lean.

### Formalization simplifications found from current sources

- `Real.le_log_one_add_of_nonneg` already proves `2z/(z+2)<=log(1+z)`. For `z>=0`, the rational lower bound is at least `z-z^2/2`. This supplies the sharp global phase-error bound without a new monotonicity proof.
- Let `r=exp(log(1+u/a)/4)`. Exact identities give `r^4=1+u/a`, `r>=1`, and `(r-1)(r^3+r^2+r+1)=u/a`. Consequently `a(r-1)=u/(r^3+r^2+r+1)<=u/4`. Since `r->1`, the same identity gives the pointwise limit `a(r-1)->u/4`. This removes the need for fractional-power derivative machinery.
- `Complex.norm_exp_sub_one_sub_id_le` supplies the local quadratic exponential remainder. With `a` times the phase difference bounded and the phase difference tending to zero, its scaled remainder tends to zero. A real-parameter unit-circle derivative estimate supplies the global Lipschitz majorant.
- Exact amplitude difference, with `r=exp(log(1+u/a)/4)`, is
  `a(A_a-A_0)=pi exp(-pi u)[2pi a(r-1)+r(2pi u-3)]`.
  This identity and `r<=1+u`, `0<=a(r-1)<=u/4` give the global bound
  `a|A_a-A_0|<=pi(3pi+3)(1+u)^2 exp(-pi u)`.
- For the shifted critical frequency, put `delta_a=(2pi+s/a)q_a-pi u`.
  Then `a delta_a -> -pi u^2/2+s u/2`, with global bound
  `|a delta_a|<=pi u^2/2+|s|u/2`. `HasDerivAt.continuousAt_div` for the
  complex exponential supplies the pointwise scaled exponential difference
  even when `delta_a=0`, avoiding a punctured-limit assumption. The actual
  mean-value API `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` supplies
  the unit-circle bound with derivative norm one.

## Continued novelty audit

- Deep corpus search for literal-shell critical Laguerre transition and half
  shift completed with `partial=true`: semantic retrieval hit its local
  deadline; semantic coverage was not measured. All returned candidate
  statements, source arguments and proposed ingredient steps were inspected;
  none matches the correction law. Exhaustive text search found only this card
  and the parent log for the proposed shift. No exhaustive semantic claim.
- `ThetaTailScalingAsymptotics.tendsto_integral_kernel` gives a fixed-kernel
  endpoint Laplace limit for large spatial shifts; `ThetaTailGermExpansion`
  gives spatial-tail expansions of zero-division deformations. Their actual
  statements concern fixed frequency kernels/spatial-tail germs, not the
  growing frequency and integer-shell cutoff in C6. Reuse their method where
  applicable; do not claim generic Watson/Laplace asymptotics as new.
- https://www.preprints.org/manuscript/202606.1957 (posted 2026-06-26) concerns
  paired phase-interval growth-derivative blocks and a spatial curvature
  transition. Its accessible statement and definitions do not state C6's
  integer-shell cutoff limit. Numerical sections are not proof inputs here.
- https://www.preprints.org/manuscript/202608.1692 (posted 2026-08-25) concerns
  phase-aligned block cancellation. These are relevant related work, not
  evidence of a full-source sign producer or proof of C6 priority.

## Critical algebra

At `lambda=2pi`, the symbolic values are

`H=pi`, `H'=-1/2`, `H''=1/(4pi)`,
`B=-1`, `B'=-3/(8pi)`, `B''=9/(16pi^2)`.

Therefore the coefficient in `H'^2-H H''` is

`2H'B'-B H''-H B''=1/(16pi)`.

The derivative of C5's leading Laguerre profile at `2pi` is `-1/(8pi)`. Adding the height offset gives `(1-2s)/(16pi)`.

## Status and next actions

- C5 final prefix/sign/name/axiom audits and import wiring complete; card is in
  `3-formalized/la-moving-theta-cutoff-laguerre-transition.md`. Global formal
  lint still reports the unrelated reachability failures in the parent log.
- Verify the critical algebra in Lean, audit first-order domination and novelty, then formalize the exact first-order tail and prefix limit.
- `ThetaMovingShellFirstOrderCoordinate.lean` now contains the phase and root
  bounds/limits, exact amplitude correction and its global majorant, and the
  shifted critical-phase correction. Initial checks exposed local namespace,
  composition, cast, positivity and absolute-value parser issues. Corrected;
  final direct check passed without errors or linter warnings. Coordinate
  targeted leaf build running; phase/exponential transfer module written but
  not checked. No first-order integral or C6 sign theorem claimed.
- Do not infer RH from either sign of the finite prefix. Full source cancellation remains essential; the all-height full-source low-order sign producer is still open.
