# Degree-zero structure theorem and convolution mobility (four-way refutation)

- **ID:** degree-zero-structure-and-mobility
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Members of the exact degree-zero class (integral, multiplicative, everywhere-valid L-representation, `f s = Q^{1−2s} f(1−s)`) are Dirichlet polynomials in finitely many prime columns or identically zero; the gamma-widened cell `GammaFECell` contains ζ, absorbs convolution by the degree-zero counterexample `dzo`, and its member ζ·dzo has a simple zero at `Re = 1/3` with charge −1.
- **Lean:** `IntegralFEPolynomial.lean` (`integralMultiplicativeFEClass_finite_or_zero`, `finiteSupport_multiplicative_columnForm`, `integralMultiplicativeFEClass_zero_periodic`), `GammaCellMobility.lean` (`zeta_mem_gammaFECell`, `gammaFECell_mul_dzo`, `gammaFECell_not_forcesRHParity`), `ZetaRealStrip.lean` (`riemannZeta_real_strip_neg`, `zetaMulDzo_order_one`, `zetaMulDzo_charge_neg_one`), `UnboundedGearCount.lean` (`integralMultiplicativeFEClass_gear_count_unbounded`). All axiom-clean.
- **Dual gate:** structure theorem NOVEL (variant of Kaczorowski–Perelli degree-0 with integrality replacing the finite-order axiom — not in literature in this form) × SIGNIFICANT (the degree-zero HT fiber is provably empty; the four-way rigidity headline dies vacuously at degree 0 and by the ζ·dzo witness at the widened FE — mobility principle: no convolution-stable class can force "divisor ⊆ line"). ZetaRealStrip is execution register (mathlib gap: ζ < 0 on the real strip segment).

## Log
- 2026-07-09 — formalized; refutation machine-checked; card `goldilocks-divisor-rigidity.md` updated.
