# Archimedean Gamma factors in Hecke Mellin unfolding

- **ID:** hecke-archimedean-mellin-integrals
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Hecke theta Mellin unfolding](hecke-theta-mellin-continuation-and-unit-unfolding.md)
- **Statement:** Evaluate the actual whole-log-space Hecke kernel Mellin integrals, with absolute convergence and the standard real and complex Gamma factors.

## Dependency-closed calculation to formalize

For a nonzero algebraic integer `a`, put `a_v=|v(a)|`, place multiplicity
`m_v`, and real-place parity `epsilon_v` (zero at complex places).
Write `n=[K:Q]`, `k=sum epsilon_v`, `t=exp(2q)`, and
`u_v=q-P(l)_v+log(a_v)`, where `P` is the existing weighted-zero profile.
The product formula gives `sum m_v*u_v=n*q+log(|Norm(a)|)`.

At Mellin argument `(n*s+k)/2`, the radial power and parity monomial combine
exactly into the actual real sign character, `|Norm(a)|^(-s)`, and

`prod_v exp((m_v*s+epsilon_v)*u_v) * exp(-pi*m_v*exp(2*u_v))`.

The radial/unit-log measure contributes `2^(r2+1)/n`. Each real-place
integral is `GammaR(s+epsilon_v)/2`; each complex-place integral is
`GammaC(s)/4`, with Mathlib's `GammaC(s)=2*(2*pi)^(-s)*Gamma(s)`.
Thus the total coefficient is `1/(n*2^(Units.rank K))` times the sign,
norm power, and standard Gamma product. Actual unit unfolding contributes
the additional torsion order.

All one-dimensional integrals converge absolutely for `Re s>0`.
Finite-product Fubini proves absolute convergence of the product integral;
the exact measure change transfers it back to radial/unit-log coordinates.
This handles one nonzero element. Summing over class ideals still needs the
existing absolute ideal-norm series on `Re s>1`, and the finite weight/sign
must be identified with the principal-ideal Hecke value, including zeros at
noncoprime elements. Those later steps must not be replaced by assumptions.

## Source-checked inputs

- `HTGeometry/GaussianMellinMoments.lean`: `mellin_exp_neg`,
  `mellin_exp_neg_pi_mul`, `mellin_gaussianKernel`, and its convergence theorem.
- `RHTower/RiemannKernelWeilRadical.lean`: `mellin_eq_integral_exp_two`, an
  unconditional logarithmic change of variables for complex Mellin integrals.
- `RHTower/BurnolCoPoissonBerezinFaithful.lean`:
  `integrableOn_Ioi_iff_integrable_exp_smul` and
  `integral_Ioi_eq_integral_exp_smul`.
- `HTGeometry/CoordinateProductFourier.lean` source identifies the Mathlib
  mechanisms `Integrable.fintype_prod` and
  `integral_fintype_prod_volume_eq_prod`; use the ordinary Pi-coordinate
  forms directly, since these logarithmic coordinates are not EuclideanSpace.
- The exact radial Jacobian is under formalization on its own card.

No Gamma-factor bridge or actual kernel evaluation is yet claimed in Lean.

Further corpus search found the exact scaled exponential Mellin convergence
and evaluation in `RHTower/FiniteExponentialSumMellin.lean`:
`mellinConvergent_exp_neg_mul` and
`mellin_exp_neg_mul_finiteExponentialSumMellin`. Reuse both directly.
Their source reduces convergence to `Complex.GammaIntegral_convergent` and
positive real scaling. All relevant existing oleans are present.

`/tmp/HeckeLogGaussianMellinScratch.lean` now contains the proposed scalar
logarithmic kernel, absolute integrability, exact Gamma integral, real and
complex specializations, and finite-product convergence/evaluation. It has
not compiled yet; the radial-Jacobian scratch currently owns the one Lean
process. The logarithmic convergence proof uses the existing exponential
change of variables and `Integrable.comp_mul_left'` for real dilation.

The principal-ideal coefficient bridge has also been source-checked:
`idealUnit_span_eq`, `mk0_mem_primeToUnits`, `rayHom_algebraMap`,
`character_rayClassOfElt_eq`, and `infiniteSignCharacter_eq_prod` supply the
coprime branch. In the nonunit-residue branch, `integralHeckeWeight_eq_zero`
and the equivalence between prime-to ideal membership and ideal coprimality
must prove both sides zero. This bridge is not yet formalized.
