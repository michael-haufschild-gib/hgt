import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilActualBirmanSchwinger
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGammaSlepianStrictSource

/-! # The full signed restricted-Weil source at every real energy

The bounded form-domain operator represents every mixed pair of the native form.
Its scalar, polar and prime channels remain exactly those of the actual source.
-/

noncomputable section

namespace RHTower.PaperRestrictedWeil

abbrev Space (a : SuzukiPositiveAperture) := CCMArchimedeanFormDomain a

def operator (a : SuzukiPositiveAperture) (E : ℝ) : Space a →L[ℂ] Space a :=
  1 - ccmRestrictedWeilFormBirmanSchwinger a E

theorem operator_selfAdjoint (a : SuzukiPositiveAperture) (E : ℝ) :
    IsSelfAdjoint (operator a E) := by
  unfold operator
  rw [ContinuousLinearMap.isSelfAdjoint_iff', ContinuousLinearMap.adjoint.map_sub,
    ContinuousLinearMap.adjoint_one,
    (ccmRestrictedWeilFormBirmanSchwinger_isSelfAdjoint a E).adjoint_eq]

theorem one_sub_operator_compact (a : SuzukiPositiveAperture) (E : ℝ) :
    IsCompactOperator (1 - operator a E : Space a →L[ℂ] Space a) := by
  simpa only [operator, sub_sub_cancel] using
    isCompactOperator_ccmRestrictedWeilFormBirmanSchwinger a E

theorem operator_mixed (a : SuzukiPositiveAperture) (E : ℝ) (u v : Space a) :
    inner ℂ (operator a E u) v = ccmRestrictedWeilForm a u v -
      (E : ℂ) * inner ℂ (ccmArchimedeanFormToAperture a u)
        (ccmArchimedeanFormToAperture a v) := by
  change inner ℂ (u - (ccmArchimedeanFormToAperture a).adjoint
    ((E : ℂ) • ccmArchimedeanFormToAperture a u -
      ccmRestrictedWeilBoundedRemainder a (ccmArchimedeanFormToAperture a u))) v = _
  rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left, inner_sub_left,
    inner_smul_left (ccmArchimedeanFormToAperture a u)
      (ccmArchimedeanFormToAperture a v) (E : ℂ),
    Complex.conj_ofReal, ccmRestrictedWeilForm]
  ring

theorem operator_quadratic (a : SuzukiPositiveAperture) (E : ℝ) (u : Space a) :
    (inner ℂ (operator a E u) u).re = ccmRestrictedWeilSourceQuadratic a u -
      E * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  have hr : (inner ℂ (ccmArchimedeanFormToAperture a u)
      (ccmArchimedeanFormToAperture a u)).re =
      ‖ccmArchimedeanFormToAperture a u‖ ^ 2 :=
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)
      (ccmArchimedeanFormToAperture a u)).symm
  rw [operator_mixed, Complex.sub_re, ccmRestrictedWeilForm_self_re_eq_source,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hr]

theorem operator_energy_sub (a : SuzukiPositiveAperture) (E₂ E₁ : ℝ) :
    operator a E₂ - operator a E₁ = -((E₂ - E₁ : ℝ) : ℂ) •
      ((ccmArchimedeanFormToAperture a).adjoint ∘L ccmArchimedeanFormToAperture a) := by
  unfold operator
  have h := ccmRestrictedWeilFormBirmanSchwinger_sub a E₂ E₁
  calc
    _ = -(ccmRestrictedWeilFormBirmanSchwinger a E₂ -
      ccmRestrictedWeilFormBirmanSchwinger a E₁) := by abel
    _ = _ := by
      rw [h]
      exact (neg_smul ((E₂ - E₁ : ℝ) : ℂ)
        ((ccmArchimedeanFormToAperture a).adjoint ∘L ccmArchimedeanFormToAperture a)).symm

theorem operator_norm_le (a : SuzukiPositiveAperture) (E : ℝ) :
    ‖operator a E‖ ≤ 1 + |E| + ‖ccmRestrictedWeilBoundedRemainder a‖ := by
  let J := ccmArchimedeanFormToAperture a
  let B := ccmRestrictedWeilBoundedRemainder a
  have hJ : ‖J‖ ≤ 1 := norm_ccmArchimedeanFormToAperture_le_one a
  have hJa : ‖J.adjoint‖ ≤ 1 := by rwa [ContinuousLinearMap.adjoint.norm_map]
  have hf : ‖ccmRestrictedWeilBirmanSchwingerForcing a E‖ ≤ |E| + ‖B‖ := by
    unfold ccmRestrictedWeilBirmanSchwingerForcing
    calc
      _ ≤ ‖(E : ℂ) • (1 : suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a)‖ + ‖B‖ :=
        norm_sub_le ((E : ℂ) • (1 : suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a)) B
      _ ≤ |E| + ‖B‖ := by
        have hs := @NormedSpace.norm_smul_le ℂ
          (suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a)
          inferInstance inferInstance inferInstance (E : ℂ)
          (1 : suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a)
        simp only [Complex.norm_real, Real.norm_eq_abs] at hs
        have hi : ‖(1 : suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a)‖ ≤ 1 :=
          ContinuousLinearMap.norm_id_le
        nlinarith [abs_nonneg E]
  have hmid : ‖ccmRestrictedWeilBirmanSchwingerForcing a E ∘L J‖ ≤
      ‖ccmRestrictedWeilBirmanSchwingerForcing a E‖ := by
    have h := ContinuousLinearMap.opNorm_comp_le (ccmRestrictedWeilBirmanSchwingerForcing a E) J
    nlinarith [norm_nonneg (ccmRestrictedWeilBirmanSchwingerForcing a E)]
  have hK : ‖ccmRestrictedWeilFormBirmanSchwinger a E‖ ≤ |E| + ‖B‖ := by
    change ‖J.adjoint ∘L (ccmRestrictedWeilBirmanSchwingerForcing a E ∘L J)‖ ≤ _
    have h := ContinuousLinearMap.opNorm_comp_le J.adjoint
      (ccmRestrictedWeilBirmanSchwingerForcing a E ∘L J)
    nlinarith [norm_nonneg (ccmRestrictedWeilBirmanSchwingerForcing a E ∘L J)]
  calc
    _ ≤ ‖(1 : Space a →L[ℂ] Space a)‖ + ‖ccmRestrictedWeilFormBirmanSchwinger a E‖ :=
      norm_sub_le (1 : Space a →L[ℂ] Space a) (ccmRestrictedWeilFormBirmanSchwinger a E)
    _ ≤ 1 + (|E| + ‖B‖) := add_le_add ContinuousLinearMap.norm_id_le hK
    _ = _ := by ring

end RHTower.PaperRestrictedWeil
