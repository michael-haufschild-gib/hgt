# Explicit shift thresholds for fixed-support collars

- **ID:** shifted-collars-have-explicit-payment-thresholds
- **Stage:** 3-formalized
- **Target:** Replace eventual collar concentration by a closed sufficient shift
  threshold, then specialize to every integer atom outside `{2,3,4,5,7}`.

## Quantitative statement and proof

Suppose `L,m,B,δ>0`, `δ≤L/4`, `g≥m` on the midpoint `δ`-interval and
`g≥−B` on `[0,L]`. Put `Δ=cosh(2δ)−cosh δ>0`,
`U=1+5L+4πL+|log(4LB/(δm))|`. A sufficient shift is the maximum of

`L+log(3)/2`, `L+log(2)/2`,
`L+log(2log(2)/(πL))/2`, and `[L+log(U/(2πΔ))]/2`.

The first three bounds admit the existing pointwise collar estimates.
The fourth gives `2πexp(2a−L)Δ≥U>5L+4πL+log(4LB/(δm))`.
Consequently the outside negative mass is strictly below the central positive
mass. The five-interval decomposition in the existing proof gives a strictly
positive full collar integral. No limiting argument remains.

For atom `n`, put `L=log n`, `v=Λ(n)/√n`, and
`b=cosh(L/2)−1−v`. Outside the five exceptional moduli the proved midpoint
law gives `b>0`. Choose `m=b/2`, `B=1+v`,
`δ=min(L/4,log(1+b/2))`. Since `cosh u≤exp(|u|)`, the midpoint lower
bound follows. The polar weight is nonnegative throughout `[0,L]`, giving
the global lower bound. Substitution supplies a closed threshold for each
actual atom; a finite family uses the maximum of its thresholds.

## Verification

`ArithmeticIncidencePositivity/ShiftedCollarsHaveExplicitPaymentThresholds.lean`:
`collarAtomMass_lt_collarPolarMass_at_explicit_shift` and
`finite_collarAtomMass_lt_collarPolarMass_at_explicit_shift` passed a direct
`lake --old env lean` check. Both transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
