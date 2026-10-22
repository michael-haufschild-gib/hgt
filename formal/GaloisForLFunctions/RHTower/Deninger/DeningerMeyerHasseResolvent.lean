import GaloisForLFunctions.RHTower.Deninger.DeningerHasseHilbertShift
import GaloisForLFunctions.RHTower.XiDivisorDiagonalTraceClass
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import Mathlib.Analysis.SpecificLimits.Normed

/-! # A compact inverse of the actual full-Jordan Meyer generator

The original source inverse extends to a Hilbert–Schmidt operator on its
faithful Hasse completion. The geometric series pays every Jordan order at
once; no simplicity or spectral positivity assumption is used.
-/

noncomputable section
open Complex ContinuousLinearMap Set Topology

namespace RHTower

private theorem hasse_inv_bound (q : XiZeroCopy) :
    ‖(xiSpectralPoint q)⁻¹‖ ≤ (1 / 4 : ℝ) := by
  have hg : 4 < ‖xiSpectralPoint q‖ := by
    by_contra h
    exact XiC_ne_zero_of_abs_re_le_four
      ((Complex.abs_re_le_norm _).trans (le_of_not_gt h))
      (XiC_xiSpectralPoint_eq_zero q)
  rw [norm_inv, inv_eq_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hg.le

def deningerHasseDiagonalInverse :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert :=
  xiDivisorDiagonal (fun q => (xiSpectralPoint q)⁻¹) (by norm_num) hasse_inv_bound

@[simp] theorem deningerHasseDiagonalInverse_apply
    (x : DeningerArithmeticJetHilbert) (q : DeningerArithmeticJetCoordinate) :
    deningerHasseDiagonalInverse x q = (xiSpectralPoint q)⁻¹ * x q := rfl

theorem norm_deningerHasseDiagonalInverse_le :
    ‖deningerHasseDiagonalInverse‖ ≤ (1 / 4 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have h : ‖deningerHasseDiagonalInverse x‖ ≤ ‖(1 / 4 : ℂ) • x‖ := by
    apply lp.norm_mono (by norm_num)
    intro q
    change ‖(xiSpectralPoint q)⁻¹ * x q‖ ≤ ‖(1 / 4 : ℂ) * x q‖
    rw [norm_mul, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa using hasse_inv_bound q
  simpa only [norm_smul, norm_div, norm_one, norm_ofNat] using h

theorem deningerHasseDiagonalInverse_isHilbertSchmidt :
    IsHilbertSchmidt deningerHasseDiagonalInverse :=
  xiDivisorDiagonal_isHilbertSchmidt _ _ _ summable_norm_inv_xiSpectralPoint_sq

theorem deningerHasseDiagonalInverse_injective :
    Function.Injective deningerHasseDiagonalInverse := by
  intro x y h
  apply lp.ext
  funext q
  have he := congrArg (fun a : DeningerArithmeticJetHilbert => a q) h
  change (xiSpectralPoint q)⁻¹ * x q = (xiSpectralPoint q)⁻¹ * y q at he
  exact mul_left_cancel₀ (inv_ne_zero (xiSpectralPoint_ne_zero q)) he

def deningerHasseResolventFactor :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert :=
  1 - I • (deningerHasseDiagonalInverse.comp deningerHasseHilbertShift)

theorem deningerHasseResolventFactor_isUnit : IsUnit deningerHasseResolventFactor := by
  apply isUnit_one_sub_of_norm_lt_one
  have h : ‖I • (deningerHasseDiagonalInverse.comp deningerHasseHilbertShift)‖ ≤ 1 / 4 := by
    rw [norm_smul, Complex.norm_I, one_mul]
    calc
      _ ≤ ‖deningerHasseDiagonalInverse‖ * ‖deningerHasseHilbertShift‖ := opNorm_comp_le _ _
      _ ≤ (1 / 4 : ℝ) * 1 := mul_le_mul norm_deningerHasseDiagonalInverse_le
        norm_deningerHasseHilbertShift_le (norm_nonneg _) (by norm_num)
      _ = _ := mul_one _
  linarith

/-- The inverse of the full centered source generator, including its nilpotent parts. -/
def deningerMeyerHasseResolvent :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert :=
  (Ring.inverse deningerHasseResolventFactor).comp deningerHasseDiagonalInverse

theorem deningerMeyerHasseResolvent_factor (x : DeningerArithmeticJetHilbert) :
    deningerHasseResolventFactor (deningerMeyerHasseResolvent x) =
      deningerHasseDiagonalInverse x := by
  have h := congrArg (fun T : DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert =>
    T (deningerHasseDiagonalInverse x))
    (Ring.mul_inverse_cancel _ deningerHasseResolventFactor_isUnit)
  exact h

theorem deningerMeyerHasseResolvent_equation (x : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) :
    xiSpectralPoint q * deningerMeyerHasseResolvent x q -
      I * deningerHasseHilbertShift (deningerMeyerHasseResolvent x) q = x q := by
  have h := congrArg (fun a : DeningerArithmeticJetHilbert => a q)
    (deningerMeyerHasseResolvent_factor x)
  change deningerMeyerHasseResolvent x q -
    I * ((xiSpectralPoint q)⁻¹ * deningerHasseHilbertShift (deningerMeyerHasseResolvent x) q) =
      (xiSpectralPoint q)⁻¹ * x q at h
  calc
    _ = xiSpectralPoint q * (deningerMeyerHasseResolvent x q -
      I * ((xiSpectralPoint q)⁻¹ * deningerHasseHilbertShift (deningerMeyerHasseResolvent x) q)) := by
        field_simp [xiSpectralPoint_ne_zero q]
    _ = xiSpectralPoint q * ((xiSpectralPoint q)⁻¹ * x q) := congrArg (fun z => xiSpectralPoint q * z) h
    _ = x q := by rw [← mul_assoc, mul_inv_cancel₀ (xiSpectralPoint_ne_zero q), one_mul]

theorem deningerMeyerHasseResolvent_isHilbertSchmidt :
    IsHilbertSchmidt deningerMeyerHasseResolvent :=
  deningerHasseDiagonalInverse_isHilbertSchmidt.comp_left _

theorem deningerMeyerHasseResolvent_isCompact : IsCompactOperator deningerMeyerHasseResolvent :=
  deningerMeyerHasseResolvent_isHilbertSchmidt.isCompactOperator

theorem deningerMeyerHasseResolvent_injective : Function.Injective deningerMeyerHasseResolvent := by
  intro x y h
  apply deningerHasseDiagonalInverse_injective
  rw [← deningerMeyerHasseResolvent_factor x, ← deningerMeyerHasseResolvent_factor y, h]

theorem deningerMeyerHasseResolvent_source_left (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerHasseResolvent (deningerMeyerHasseHilbertLM (deningerMeyerCenteredGenerator u)) =
      deningerMeyerHasseHilbertLM u := by
  have he : deningerHasseResolventFactor (deningerMeyerHasseHilbertLM u) =
      deningerHasseDiagonalInverse (deningerMeyerHasseHilbertLM (deningerMeyerCenteredGenerator u)) := by
    apply lp.ext
    funext q
    change deningerMeyerHasseHilbertLM u q -
      I * ((xiSpectralPoint q)⁻¹ * deningerHasseHilbertShift (deningerMeyerHasseHilbertLM u) q) =
        (xiSpectralPoint q)⁻¹ * deningerMeyerHasseHilbertLM (deningerMeyerCenteredGenerator u) q
    rw [deningerMeyerHasseHilbert_centeredGenerator]
    field_simp [xiSpectralPoint_ne_zero q]
  change Ring.inverse deningerHasseResolventFactor
    (deningerHasseDiagonalInverse (deningerMeyerHasseHilbertLM (deningerMeyerCenteredGenerator u))) = _
  rw [← he]
  exact congrArg (fun T : DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert =>
    T (deningerMeyerHasseHilbertLM u))
    (Ring.inverse_mul_cancel _ deningerHasseResolventFactor_isUnit)

theorem deningerMeyerCenteredGenerator_bijective : Function.Bijective deningerMeyerCenteredGenerator := by
  constructor
  · intro u v h
    apply deningerMeyerHasseHilbertLM_injective
    rw [← deningerMeyerHasseResolvent_source_left u, ← deningerMeyerHasseResolvent_source_left v, h]
  · intro u
    obtain ⟨v, hv⟩ := deningerMeyerCohomologyShift_surjective_of_xi_ne_zero (1 / 2)
      (xi_ne_zero_of_abs_im_le_four (by norm_num)) (I • u)
    refine ⟨v, ?_⟩
    change -I • deningerMeyerCohomologyShift (1 / 2) v = u
    rw [hv, smul_smul]
    simp

/-- Exact original-source inverse; its Hilbert extension is the operator above. -/
def deningerMeyerCenteredGeneratorEquiv :
    DeningerMeyerStrongLogCohomology ≃ₗ[ℂ] DeningerMeyerStrongLogCohomology :=
  LinearEquiv.ofBijective deningerMeyerCenteredGenerator deningerMeyerCenteredGenerator_bijective

theorem deningerMeyerHasseResolvent_source (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerHasseResolvent (deningerMeyerHasseHilbertLM u) =
      deningerMeyerHasseHilbertLM (deningerMeyerCenteredGeneratorEquiv.symm u) := by
  have h := deningerMeyerHasseResolvent_source_left (deningerMeyerCenteredGeneratorEquiv.symm u)
  have he : deningerMeyerCenteredGenerator (deningerMeyerCenteredGeneratorEquiv.symm u) = u :=
    deningerMeyerCenteredGeneratorEquiv.apply_symm_apply u
  rw [he] at h
  exact h

theorem deningerMeyerHasseResolvent_dense : DenseRange deningerMeyerHasseResolvent := by
  apply Dense.mono _ deningerMeyerHasseHilbertLM_dense
  rintro _ ⟨u, rfl⟩
  exact ⟨deningerMeyerHasseHilbertLM (deningerMeyerCenteredGenerator u),
    deningerMeyerHasseResolvent_source_left u⟩

end RHTower
