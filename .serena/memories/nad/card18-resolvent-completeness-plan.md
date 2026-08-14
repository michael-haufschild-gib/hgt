# Card 18 (moment-polynomial-blind) — state and next steps (2026-08-14)

## Done (all axiom-clean, wired into `GaloisForLFunctions.HTGeometry`)
`HTGeometry/BoundaryConditionalExpectation.lean`
- `leafKernel`, `leafAverage`, `markovAverage`, `ae_projectiveLabel_eq`,
  `integral_measureBarycenter`, `hasHamburgerMoments_measureBarycenter`.
- (4) `integral_comp_projectiveLabel_mul_barycenter`; (5) `markovAverage_ae_eq_condExp`
  (σ-algebra `labelSigmaAlgebra = comap projectiveLabel`).
- (6)-(8) `integral_comp_projectiveLabel_mul_eq_parameter`,
  `forall_integral_comp_projectiveLabel_mul_eq_zero_iff` (vertical kernel = leaf averages vanish).
- (10)-(13) `leafAverage_eval`, `leafAverage_eval_sub_const`,
  `integral_eval_mul_comp_projectiveLabel`.

`HTGeometry/CauchyTransformOpenUniqueness.lean`
- `analyticOnNhd_resolventTransform_upper`, `eqOn_upper_of_eqOn_open`,
  `tendsto_mul_im_resolventTransform` (mass = lim y·Im S(iy)), `measure_univ_eq_of_eqOn_upper`,
  **`measure_eq_of_resolventTransform_eqOn_open`**.

`HTGeometry/CauchyKernelDensityVanishing.lean`
- `lowerHalfPlaneSet` + preconnectedness, `analyticOnNhd_resolventTransform_offReal`,
  `densityCauchyTransform`, `norm_cauchyKernel_le`, `integrable_density_mul_cauchyKernel`,
  `resolventTransform_withDensity_ofReal`, `densityCauchyTransform_eq_combination`,
  `analyticOnNhd_densityCauchyTransform`, `densityCauchyTransform_conj`,
  `real_density_eq_zero_of_transform_eq_zero_upper`,
  **`density_eq_zero_of_transform_eq_zero_both`**.

## Remaining for the card
1. **(14)-(15)** `Φ_z(τ) = m_τ(z)` and `P_s r_z = Φ_z ∘ π`.  Needs a complex-valued leaf average
   (`leafAverageC`), then (15) is definitional.  The corpus has the closed form
   `NevLeafCauchyMoebius.cauchyTransform_nevLeaf_eq_moebius` and
   `NevLeafInfinityCauchyMoebius` for the constructed family.
2. **(16)-(20)** density of `span({1} ∪ {Φ_z})` in `L²(T,η)`.  Assembly:
   - Möbius identity (18): `NevanlinnaMatrixData.mobius_difference` gives
     `(aτ+b)/(cτ+d) = a/c + (−1/c²)/(τ − q)`, so annihilating `1` and `Φ_z` leaves
     `∫ ḡ(τ)/(τ − q(z)) dη|_ℝ = 0`.
   - `q` maps the lower half-plane into the upper (`analyticNevCarrierFamily_lowerMap`) and the
     upper into the lower (`NevanlinnaWeylDiscPole`), hence is nonconstant; use mathlib's
     `AnalyticOnNhd.is_constant_or_isOpen` to get an open image in each half-plane.
   - Then `density_eq_zero_of_transform_eq_zero_both` gives `g = 0` η-a.e.
   - Note: the ∞ atom of η is handled by the annihilation of the constant `1`.
3. **(21)** `H_hor` = closed span of `{1} ∪ {P_s r_z}` — combine 2 with the pullback isometry.
4. **(21a)-(21i)** the three-layer Pick–Gram splitting and exact ranks.

## Traps hit
- `V₊`/`z₊` are NOT valid Lean identifiers (subscript plus/minus); use `Vup`/`Vlow`.
- `ring` cannot cancel `(2*I)⁻¹ * I`; state constants as `-(2:ℂ)⁻¹ * Complex.I` and feed
  `Complex.I_sq` to `linear_combination`.
- `analyticOnNhd_const` names its value argument `v`, not `c`.
- `Integrable.conj` does not exist; use `Integrable.mono' hint.norm …`.
- Vanishing of a Cauchy transform on ONE half-plane does not force the density to vanish.
