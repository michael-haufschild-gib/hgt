# Theta-cusp all-order cumulant recurrence

- **ID:** theta-cusp-all-order-cumulant-recurrence
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every normalized continued prime--Gamma moment is recursively determined by finitely many raw moments of the positive theta-cusp source and the preceding normalized moments; countable Hankel positivity of this sequence is exactly RH.

## Goal

Replace the separate order-one, order-three, and order-five expansions of the prime--Gamma source
identity by a single all-order theorem.  This makes the full theta-source obligation visible before
any zero data or Gram factorization is introduced.

## Theorem

Write

\[
X_k=\Xi_C^{(k)}(0),
\qquad
H_k=\left.\frac{d^k}{dz^k}\bigl(zG(z)\bigr)\right|_{z=0},
\]

where

\[
G(z)=-\operatorname{dslope}
  \bigl(\operatorname{continuedPrimeArchSourceRelativeTrace},0,z\bigr).
\]

Lean proves the parity formulas

\[
X_{2j}=(-1)^j r_j,\qquad X_{2j+1}=0,
\]

and

\[
H_{2j+1}=(2j+1)!M_j,\qquad H_{2j}=0,
\]

where `r_j = thetaCuspRawEvenMoment j` and
`M_j = normalizedPrimeArchMoment j`.  Differentiating

\[
\Xi_C'(z)+zG(z)\Xi_C(z)=0
\]

to arbitrary order gives

\[
X_{N+1}+\sum_{i=0}^{N}\binom Ni H_iX_{N-i}=0.                 \tag{R_N}
\]

At `N=2n+1`, the final summand is

\[
(2n+1)!\,r_0M_n.
\]

The raw zeroth moment is strictly positive.  Therefore `(R_{2n+1})` recursively determines `M_n`
from `r_0,\ldots,r_{n+1}` and `M_0,\ldots,M_{n-1}`.  The previously formalized first Hankel minor
is the `n<=2` floor of this hierarchy, not an isolated calculation.

## Top-down chain

```text
all integer-polynomial Hankel inequalities for the recursively theta-determined M_n
  -> prime--Gamma source trace-Hankel positivity
  -> Xi central reciprocal-moment positivity
  -> RH.
```

The last three implications and the reverse implication are unconditional in Lean.  The open
scientific problem is positive: prove that the explicit theta-cusp source forces every finite
Hankel matrix of its logarithmic-cumulant sequence to be positive semidefinite.  Positivity of the
raw density or ordinary Stieltjes log-convexity is insufficient; the proof must use additional
theta-specific shape or total-positivity structure.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/PrimeArchThetaAllOrderCumulant.lean`.

Principal declarations:

- `thetaCuspXiJet`
- `iteratedDeriv_XiC_zero_eq_thetaCuspXiJet`
- `thetaCuspPrimeArchProductJet`
- `iteratedDeriv_id_mul_normalizedPrimeArchMomentGerm_zero`
- `thetaCusp_allOrderCumulantRecurrence`
- `normalizedPrimeArchMoment_recursive`
- `primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis`

Validation:

- `lake build GaloisForLFunctions.RHTower.PrimeArchThetaAllOrderCumulant` passes.
- The public capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 → 1: source-pure theta formulation and exact recurrence identified
- [x] 1 → 2: complete all-order proof from the analytic differential identity
- [x] 2 → 3: Lean theorem builds and public axioms are standard
- [ ] 3 → 4: prove the all-degree theta-cumulant Hankel positivity theorem
