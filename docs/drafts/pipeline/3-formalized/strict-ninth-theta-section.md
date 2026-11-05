# Strict ninth theta section

- **Stage:** 3-formalized
- **Wall:** Σ6
- **Statement:** The literal center-mixed signed Hankel matrix of rank
  nine is positive definite for every `0<a<1/2`.

The fifth even block is the integral of the complete fifth native tail
against `W_a(r)=sinh(ar)+ar cosh(ar)`. Every tail matrix is positive
definite for `r≥0`, and `W_a(r)>0` for `a,r>0`. Entrywise integrability
allows finite quadratic forms to pass through the integral. For every
nonzero vector the integrand is strictly positive on `(1,2)`, a set of
positive measure. Thus the fifth even mixed block is positive definite.

Odd center jets vanish. Splitting indices `0,…,8` by parity gives this
fifth even block and the proved fourth odd mixed block. Their orthogonal
sum is positive definite. The exact successor Schur identity then makes
the eighth native successor integral strictly positive.

Namespace `GaloisForLFunctions.ThetaCuspSections`:
`thetaCuspCenterMixedEvenFive_posDef`,
`thetaCuspCenterMixedSignedHankel_nine_posDef`,
`thetaCuspNativeSuccessorIntegral_eight_pos`.

Modules: `ThetaCuspSections/FifthEvenCompleteTail.lean`,
`ThetaCuspSections/StrictNinthSection.lean`.
The capstones use only `propext`, `Classical.choice`, and `Quot.sound`.

The theorem settles rank nine. Uniformity in all ranks remains open.
