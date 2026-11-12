import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheChargedNullModesAreTheCrossingsOfThePolarLagrangian
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheIndexIsTheNumberOfCrossingsOfTheApertureConormalsWithTheGraphOfWeilsOperator

/-!
# Below the ground energy the polar Lagrangians are positive and increase

Fix an energy `E`. At an aperture `a` whose ground energy is above `E`, Weil's form shifted by
`E` is positive definite, and the polar Lagrangian is the graph of a positive definite Hermitian
form on the forcings:

* every forcing `y` has exactly one charge `x` with `(x, y)` in the polar Lagrangian
  (`exists_mem_polarLagrangian_of_lt_ground`, `eq_of_mem_polarLagrangian_of_lt_ground`);
* `⟨y, x⟩` is the value at the solution `ξ` of `T ξ = d† y` of the functional
  `u ↦ 2 Re ⟨y, d u⟩ − ⟨T u, u⟩`, which is its maximum (`forced_variational`); it is positive
  for `y ≠ 0` (`re_inner_forcing_charge_pos`);
* it increases with the aperture (`re_inner_forcing_charge_mono`): the solution at the smaller
  aperture is a competitor at the larger one, with the same charges and the same form.

So before the first conjugate aperture the path of polar Lagrangians is monotone: the form of
the forcings grows until, at a conjugate aperture with a charged null mode, it has a pole.
-/

open Module
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower _root_.RHTower.PaperRestrictedWeil
open ArithmeticContinuationAndCriticalEnergy HTGeometry

section Abstract

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- **The variational form of a forced equation.** If `T` is positive and `T ξ = d† y`, the
functional `u ↦ 2 Re ⟨y, d u⟩ − ⟨T u, u⟩` is at most its value `⟨y, d ξ⟩` at `ξ`. -/
theorem forced_variational {T : H →L[ℂ] H} (hT : T.IsPositive) {d : H →L[ℂ] V} {ξ : H} {y : V}
    (h : T ξ = ContinuousLinearMap.adjoint d y) (u : H) :
    2 * (⟪y, d u⟫_ℂ).re - (⟪T u, u⟫_ℂ).re ≤ (⟪y, d ξ⟫_ℂ).re := by
  have h0 : 0 ≤ (⟪T (u - ξ), u - ξ⟫_ℂ).re := hT.re_inner_nonneg_left (u - ξ)
  have h1 : ⟪T ξ, u⟫_ℂ = ⟪y, d u⟫_ℂ := by rw [h, ContinuousLinearMap.adjoint_inner_left]
  have h2 : ⟪T ξ, ξ⟫_ℂ = ⟪y, d ξ⟫_ℂ := by rw [h, ContinuousLinearMap.adjoint_inner_left]
  have hsym : (⟪u, T ξ⟫_ℂ).re = (⟪T ξ, u⟫_ℂ).re := inner_re_symm (𝕜 := ℂ) u (T ξ)
  have h3 : (⟪T u, ξ⟫_ℂ).re = (⟪y, d u⟫_ℂ).re := by
    rw [hT.inner_left_eq_inner_right u ξ, hsym, h1]
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, Complex.sub_re, Complex.sub_re,
    Complex.sub_re, h3, h1, h2] at h0
  linarith

end Abstract

variable {a b : SuzukiPositiveAperture} {E : ℝ}

/-- The charges of a vector do not change when the aperture grows. -/
theorem polarCharge_apertureExt (hab : a.1 ≤ b.1) (u : Space a) :
    polarCharge b (apertureExt hab u) = polarCharge a u := by
  ext i
  fin_cases i
  · exact inner_ccmPolarApertureVector_eq_of_val_eq hab (1 / 2) (apertureExt_val hab u)
  · exact inner_ccmPolarApertureVector_eq_of_val_eq hab (-1 / 2) (apertureExt_val hab u)

/-- Below the ground energy Weil's operator has no null mode. -/
theorem eq_zero_of_operator_eq_zero_of_lt_ground (hE : E < ccmRestrictedWeilGroundEnergy a)
    {k : Space a} (hk : operator a E k = 0) : k = 0 := by
  by_contra hk0
  have hJ : ccmArchimedeanFormToAperture a k ≠ 0 := fun hz =>
    hk0 (ccmArchimedeanFormToAperture_injective a (by rw [hz, map_zero]))
  have hpos : 0 < ‖ccmArchimedeanFormToAperture a k‖ ^ 2 := by
    have := norm_pos_iff.mpr hJ
    positivity
  have hq : (inner ℂ (operator a E k) k).re = 0 := by
    rw [hk, inner_zero_left, Complex.zero_re]
  rw [operator_quadratic] at hq
  have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a k
  nlinarith [mul_pos (sub_pos.mpr hE) hpos]

/-- **Below the ground energy every forcing has a solution**: the polar Lagrangian projects onto
the forcing axis. -/
theorem exists_mem_polarLagrangian_of_lt_ground (hE : E < ccmRestrictedWeilGroundEnergy a)
    (y : ChargeSpace) : ∃ x : ChargeSpace, (x, y) ∈ polarLagrangian a E := by
  obtain ⟨ξ, hξ⟩ := exists_apply_eq_of_mem_orthogonal_ker (operator_selfAdjoint a E)
    (one_sub_operator_compact a E) (η := ContinuousLinearMap.adjoint (polarCharge a) y) (by
      rw [Submodule.mem_orthogonal]
      intro k hk
      rw [eq_zero_of_operator_eq_zero_of_lt_ground hE hk, inner_zero_left])
  exact ⟨polarCharge a ξ, ξ, rfl, hξ⟩

/-- **Below the ground energy the charge is determined by the forcing.** -/
theorem eq_of_mem_polarLagrangian_of_lt_ground (hE : E < ccmRestrictedWeilGroundEnergy a)
    {x x' y : ChargeSpace} (h : (x, y) ∈ polarLagrangian a E)
    (h' : (x', y) ∈ polarLagrangian a E) : x = x' := by
  have hsub := (polarLagrangian a E).sub_mem h h'
  rw [Prod.mk_sub_mk, sub_self] at hsub
  obtain ⟨ξ, hξ, hx⟩ := mem_polarRelation_zero_right.mp hsub
  rw [eq_zero_of_operator_eq_zero_of_lt_ground hE hξ, map_zero] at hx
  exact sub_eq_zero.mp hx.symm

/-- **Up to the ground energy the pairing of a forcing with its charge is nonnegative.** -/
theorem re_inner_forcing_charge_nonneg (hE : E ≤ ccmRestrictedWeilGroundEnergy a)
    {x y : ChargeSpace} (h : (x, y) ∈ polarLagrangian a E) : 0 ≤ (⟪y, x⟫_ℂ).re := by
  obtain ⟨ξ, h1, h2⟩ := h
  have h1' : polarCharge a ξ = x := h1
  have h2' : operator a E ξ = ContinuousLinearMap.adjoint (polarCharge a) y := h2
  have hval : ⟪y, x⟫_ℂ = ⟪operator a E ξ, ξ⟫_ℂ := by
    rw [h2', ContinuousLinearMap.adjoint_inner_left, h1']
  rw [hval]
  exact ((operator_positive_iff_ground a E).mpr hE).re_inner_nonneg_left ξ

/-- **Below the ground energy the pairing of a nonzero forcing with its charge is positive.** -/
theorem re_inner_forcing_charge_pos (hE : E < ccmRestrictedWeilGroundEnergy a)
    {x y : ChargeSpace} (h : (x, y) ∈ polarLagrangian a E) (hy : y ≠ 0) : 0 < (⟪y, x⟫_ℂ).re := by
  obtain ⟨ξ, h1, h2⟩ := h
  have h1' : polarCharge a ξ = x := h1
  have h2' : operator a E ξ = ContinuousLinearMap.adjoint (polarCharge a) y := h2
  have hval : ⟪y, x⟫_ℂ = ⟪operator a E ξ, ξ⟫_ℂ := by
    rw [h2', ContinuousLinearMap.adjoint_inner_left, h1']
  -- the solution is not zero: the adjoint of the charge map is injective
  have hξ0 : ξ ≠ 0 := by
    intro hz
    rw [hz, map_zero] at h2'
    obtain ⟨w, hw⟩ := polarCharge_surjective a y
    have h3 : ⟪ContinuousLinearMap.adjoint (polarCharge a) y, w⟫_ℂ = ⟪y, y⟫_ℂ := by
      rw [ContinuousLinearMap.adjoint_inner_left, hw]
    rw [← h2', inner_zero_left] at h3
    exact hy (inner_self_eq_zero.mp h3.symm)
  have hJ : ccmArchimedeanFormToAperture a ξ ≠ 0 := fun hz =>
    hξ0 (ccmArchimedeanFormToAperture_injective a (by rw [hz, map_zero]))
  have hpos : 0 < ‖ccmArchimedeanFormToAperture a ξ‖ ^ 2 := by
    have := norm_pos_iff.mpr hJ
    positivity
  rw [hval, operator_quadratic]
  have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a ξ
  nlinarith [mul_pos (sub_pos.mpr hE) hpos]

/-- **Up to the ground energy the polar Lagrangians increase with the aperture**: for one
forcing, the pairing with the charge at a smaller aperture is at most the pairing at a larger
one. -/
theorem re_inner_forcing_charge_mono (hab : a.1 ≤ b.1) (hE : E ≤ ccmRestrictedWeilGroundEnergy b)
    {x x' y : ChargeSpace} (ha : (x, y) ∈ polarLagrangian a E)
    (hb : (x', y) ∈ polarLagrangian b E) : (⟪y, x⟫_ℂ).re ≤ (⟪y, x'⟫_ℂ).re := by
  obtain ⟨ξ, h1, h2⟩ := ha
  obtain ⟨η, h3, h4⟩ := hb
  have h1' : polarCharge a ξ = x := h1
  have h2' : operator a E ξ = ContinuousLinearMap.adjoint (polarCharge a) y := h2
  have h3' : polarCharge b η = x' := h3
  have h4' : operator b E η = ContinuousLinearMap.adjoint (polarCharge b) y := h4
  have hvar := forced_variational ((operator_positive_iff_ground b E).mpr hE) h4'
    (apertureExt hab ξ)
  rw [polarCharge_apertureExt, inner_operator_apertureExt, h2',
    ContinuousLinearMap.adjoint_inner_left, h1', h3'] at hvar
  linarith

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
