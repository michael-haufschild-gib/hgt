# Hedenmalm center-mixed asymmetric near three-point chamber

- **ID:** `hedenmalm-center-mixed-asymmetric-near-three-point-chamber`
- **Stage:** 3-formalized
- **Type:** SOURCE THEOREM / ORDER-THREE POSITIVITY
- **Date:** 2026-07-20
- **Status:** `[DEPENDENCY-CLOSED PAPER PROOF] [LEAN COMPILER-CHECKED] [NO COMPUTATION] [NOT RH]`

## Exact target

For `0 < a < 1/2`, write

`M_a(t) = integral r in (0,infinity), r sinh(a r) k(r/2+t) k(r/2-t) dr`,

where `k = thetaCuspFullSource`.  Prove that there is a tail threshold `Y` such that, for every
`y >= Y`, there is `epsilon_y > 0` for which every `0 < x < epsilon_y` satisfies both

1. the ordered three-point correlation matrix at `0,x,x+y` is positive definite, and
2. `M_a(x)^2 + M_a(y)^2 > M_a(0)^2`.

The second clause places this chamber strictly inside the named near-center region not covered by
`thetaCuspCenterMixedThreePointMatrix_posSemidef_of_far_chamber`.

## Determinant reduction

For an even `C^2` function `f`, put

`D_y(x) = f(0)^3 + 2 f(x) f(y) f(x+y)
          - f(0) (f(x)^2 + f(y)^2 + f(x+y)^2)`.

Then `D_y(0) = D_y'(0) = 0`, and direct differentiation gives

`D_y''(0) = 2 ((-f''(0)) (f(0)^2 - f(y)^2) - f(0) f'(y)^2)`.

Consequently, if `f(0) > 0`, `f''(0) < 0`, and `f(y),f'(y) -> 0`, then the displayed bracket is
strictly positive for every sufficiently large `y`.  Continuity of `D_y''` gives `D_y(x) > 0`
for all sufficiently small positive `x`.

For fixed `y` with `f(y) > 0`, continuity at zero gives
`f(x)^2 + f(y)^2 > f(0)^2` for all sufficiently small `x`, proving genuine near-center overlap.
The positive diagonal and positive `2 x 2` principal minors are already available from strict
radial decrease, so the positive determinant upgrades the matrix to positive definiteness.

## Source obligations

- [x] `M_a` is twice continuously differentiable.
- [x] Differentiation under the integral gives the first and second derivatives.
- [x] `M_a''(0) < 0`, using
  `d^2/dt^2 [k(u+t)k(u-t)] at 0 = 2 k(u)^2 (log k)''(u) < 0`.
- [x] `M_a(t) -> 0` and `M_a'(t) -> 0` as `t -> +infinity`, by the existing exponential source
  derivative bounds and dominated convergence.
- [x] The generic determinant Taylor lemma is formalized without a certificate wrapper.
- [x] The resulting source theorem is connected to the named near-center cubic wall.

## Dependency-closed paper proof

Let `k_j = d^j k/dx^j`.  The existing source estimates give constants `C_j` with
`|k_j(u)| <= C_j exp(-|u|)`.  For `r > 0`,

`r/2 + |t| <= |r/2+t| + |r/2-t|`.

After multiplying by `r sinh(a r)`, every term in the first two `t`-derivatives of the radial
integrand is therefore bounded by a constant times

`r exp(-(1/2-a)r) exp(-|t|)`.

This function is integrable in `r` because `a < 1/2`, and its `r`-integral is an integrable
majorant in `t`.  Differentiation under the integral is valid twice, both derivative integrals are
continuous by the same domination, and `M_a`, `M_a'`, and `M_a''` are the corresponding integral
jets.  Since `M_a` is integrable already, while `M_a'` and `M_a''` have the displayed exponential
majorants, the half-line fundamental theorem for an integrable function and integrable derivative
gives `M_a(t) -> 0` and `M_a'(t) -> 0`.

At the center, evenness gives `k_1(-u) = -k_1(u)` and `k_2(-u)=k_2(u)`, hence

`M_a''(0) = 2 integral_(0,infinity) r sinh(a r)
                 (k_2(r/2) k(r/2) - k_1(r/2)^2) dr`.

The parenthesis is the strictly negative global log-concavity numerator.  The remaining factors
are strictly positive for `r > 0` and `a > 0`; integrability was proved above.  Negating the
integrand and using positivity of its nonempty open support proves `M_a''(0) < 0`.

Now set `d=M_a(0)`, `q=M_a(y)`, and

`B(y)=(-M_a''(0))(d^2-q^2)-d M_a'(y)^2`.

The two tail limits imply `B(y) -> (-M_a''(0))d^2 > 0`, so `B(y)>0` for every sufficiently large
`y`.  The determinant path has value and first derivative zero at `x=0`, and second derivative
`2B(y)>0` there.  Continuity of its second derivative makes it strictly convex on a small interval
to the right of zero; it is therefore strictly positive there.  Continuity at zero and `M_a(y)>0`
simultaneously give the strict near-center inequality.  Strict radial decrease supplies the two
positive leading principal minors, so the matrix is positive definite.

## Novelty and hostile audit

The local determinant calculus is classical analysis and is not claimed as new mathematics.  The
source specialization is a new project theorem only if every derivative and tail statement is
proved for the actual theta source.  A theorem merely assuming those properties is infrastructure,
not completion.  The result closes a nonempty asymmetric subset of the open order-three chamber;
it does not imply all-node positive definiteness or RH.

## Lean realization

`HilbertMetric.exists_threePointCorrelationDeterminantPath_pos_right` proves the generic local
second-jet determinant theorem, while
`RHTower.eventually_exists_thetaCuspCenterMixed_nearCenter_posDef` discharges every analytic
hypothesis for the actual theta source.  Its supporting source declarations include
`thetaCuspCenterMixedDensitySecondJet_zero_neg`, the two tail limits, and the twice-differentiated
integral identities.

## Successor and exact remaining open core

The successor theorem `exists_thetaCuspCenterMixedThreePointMatrix_posSemidef_of_large_gap` closes
the whole cofinal region containing this asymmetric chamber.  The remaining order-three wall is
now a bounded two-gap core at each aperture.  All-node positive definiteness remains RH-equivalent.
No conjectural positivity, finite zero data, interval arithmetic, or RH assumption is used.
