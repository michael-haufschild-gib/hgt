# Theta-cusp cumulant minor reduction

- **ID:** theta-cusp-cumulant-minor-reduction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The first linear-polynomial prime--Gamma source Hankel block is nonnegative exactly when an explicit normalized sixth-moment inequality holds for the positive theta-cusp density.

## Theorem

Let
\[
r_{2j}=\frac{2\int_0^\infty x^{2j}\Phi(x)\,dx}
              {2\int_0^\infty\Phi(x)\,dx},
\qquad \Phi=\thetaCuspFullSource,
\]
and let `M₀,M₁,M₂` be the first three Taylor moments of the normalized continued prime--Gamma source germ.
Then
\[
M_0=r_2,
\qquad
M_1=\frac{r_2^2}{2}-\frac{r_4}{6},
\qquad
M_2=\frac{r_6}{120}-\frac{r_2r_4}{8}+\frac{r_2^3}{4},
\]
and
\[
360(M_0M_2-M_1^2)=3r_2r_6+15r_2^2r_4-10r_4^2.
\]
Consequently,
\[
\forall a,b\in\mathbb R,\quad
Q(a+bX)\ge 0
\quad\Longleftrightarrow\quad
3r_2r_6+15r_2^2r_4-10r_4^2\ge0,
\]
where `Q` is `primeArchSourceTraceHankel`.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor`
- General derivative identity: `iteratedDeriv_Xi_zero_eq_rawEvenMoment`
- Cumulant formulas:
  - `normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment`
  - `normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment`
  - `normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment`
- Determinant identity: `normalizedPrimeArch_firstHankelMinor_scaled_eq_thetaCuspMoments`
- Exact positivity interface: `forall_primeArchSourceTraceHankel_linear_nonneg_iff_thetaCuspSixthMomentHankelInequality`

## Scope

This theorem does not prove the sixth-moment inequality and does not prove RH. It removes every formal
power-series, derivative, normalization, and finite Hankel ambiguity from the first nonconstant block. The
remaining input is a source-shape theorem about the explicit positive theta-cusp density, with no Xi-zero or
RH hypothesis.
