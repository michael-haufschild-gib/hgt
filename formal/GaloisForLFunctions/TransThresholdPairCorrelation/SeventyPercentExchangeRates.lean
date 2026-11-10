import GaloisForLFunctions.TransThresholdPairCorrelation.FormFactorThresholdAndShiftInequality

/-!
# Exact exchange rates for a seventy-percent certificate

A form-factor ceiling of four has optimal bandwidth `10/9` and certifies
`7/10`. At bandwidth `4/3`, the same proportion requires Frobenius constant
`13/10`, equivalently trans-threshold integral at most `7/45`.
-/

open MeasureTheory Real Set intervalIntegral RHTower

noncomputable section
namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-- The optimal certificate at form-factor ceiling four is exactly seventy percent. -/
theorem certOpt_four : certOpt 4 = 7 / 10 := by
  norm_num [certOpt]

/-- Bandwidth `10/9` attains the optimum for ceiling four. -/
theorem certValue_ten_ninths_four : certValue (10 / 9) 4 = 7 / 10 := by
  have h := certValue_at_opt (B := 4) (by norm_num)
  norm_num [certOpt] at h
  exact h

/-- No nonzero bandwidth improves on seventy percent with the same ceiling four. -/
theorem certValue_four_le_seven_tenths {lam : ℝ} (hlam : lam ≠ 0) :
    certValue lam 4 ≤ 7 / 10 := by
  simpa only [certOpt_four] using certValue_le_opt (B := 4) (by norm_num) hlam

/-- A bounded-form-factor certificate reaches seventy percent exactly when its ceiling is at most four. -/
theorem seven_tenths_le_certOpt_iff {B : ℝ} (hB : 2 / 3 < B) :
    7 / 10 ≤ certOpt B ↔ B ≤ 4 := by
  have hden : 0 < 3 * B - 2 := by linarith only [hB]
  unfold certOpt
  rw [le_div_iff₀ hden]
  constructor <;> intro h <;> linarith only [h]

/-- A bound on the open trans-threshold interval controls its triangular weighted integral. -/
theorem transThresholdIntegral_le_const {F : ℝ → ℝ} {lam B : ℝ} (hlam : 1 ≤ lam)
    (hF : Continuous F) (hbound : ∀ α ∈ Ioo (1 : ℝ) lam, F α ≤ B) :
    transThresholdIntegral F lam ≤ B * (lam - 1) ^ 2 / 2 := by
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) hlam
    ((by fun_prop : Continuous fun α => (lam - α) * F α).intervalIntegrable 1 lam)
    ((by fun_prop : Continuous fun α : ℝ => (lam - α) * B).intervalIntegrable 1 lam)
    (fun α hα => mul_le_mul_of_nonneg_left (hbound α hα) (sub_nonneg.mpr hα.2.le))
  have heq : (∫ α in (1 : ℝ)..lam, (lam - α) * B) = B * (lam - 1) ^ 2 / 2 := by
    have he : (fun α : ℝ => (lam - α) * B) = fun α => B * lam - B * α := by
      funext α
      ring
    rw [he, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun _ : ℝ => B * lam).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun α : ℝ => B * α).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    simp only [smul_eq_mul]
    ring
  exact hmono.trans_eq heq

/-- Ceiling four on `(1,10/9)` gives a seventy-percent form-factor certificate. -/
theorem seventy_percent_certificate_of_formFactor_le_four {F : ℝ → ℝ}
    (hF : Continuous F) (hsub : ∀ α ∈ Icc (0 : ℝ) 1, F α = α)
    (hbound : ∀ α ∈ Ioo (1 : ℝ) (10 / 9), F α ≤ 4) :
    7 / 10 ≤ 2 - frobeniusFormFactor F (10 / 9) := by
  have hi := transThresholdIntegral_le_const (by norm_num : (1 : ℝ) ≤ 10 / 9) hF hbound
  have hf := frobeniusFormFactor_eq_split (by norm_num : (10 / 9 : ℝ) ≠ 0) hF hsub
  norm_num at hi hf
  linarith only [hi, hf]

/-- At bandwidth `4/3`, Frobenius constant `13/10` means weighted integral `7/45`. -/
theorem frobeniusFormFactor_four_thirds_le_thirteen_tenths_iff {F : ℝ → ℝ}
    (hF : Continuous F) (hsub : ∀ α ∈ Icc (0 : ℝ) 1, F α = α) :
    frobeniusFormFactor F (4 / 3) ≤ 13 / 10 ↔
      transThresholdIntegral F (4 / 3) ≤ 7 / 45 := by
  rw [frobeniusFormFactor_four_thirds hF hsub]
  constructor <;> intro h <;> linarith only [h]

/-- The seventy-percent certificate at bandwidth `4/3` has exact Frobenius ceiling `13/10`. -/
theorem seventy_percent_certificate_four_thirds_iff {F : ℝ → ℝ}
    (hF : Continuous F) (hsub : ∀ α ∈ Icc (0 : ℝ) 1, F α = α) :
    (7 / 10 ≤ 2 - frobeniusFormFactor F (4 / 3) ↔
      frobeniusFormFactor F (4 / 3) ≤ 13 / 10) ∧
    (7 / 10 ≤ 2 - frobeniusFormFactor F (4 / 3) ↔
      transThresholdIntegral F (4 / 3) ≤ 7 / 45) := by
  have hcal : 7 / 10 ≤ 2 - frobeniusFormFactor F (4 / 3) ↔
      frobeniusFormFactor F (4 / 3) ≤ 13 / 10 := by
    constructor <;> intro h <;> linarith only [h]
  exact ⟨hcal, hcal.trans (frobeniusFormFactor_four_thirds_le_thirteen_tenths_iff hF hsub)⟩

#print axioms certOpt_four
#print axioms certValue_ten_ninths_four
#print axioms certValue_four_le_seven_tenths
#print axioms seven_tenths_le_certOpt_iff
#print axioms seventy_percent_certificate_of_formFactor_le_four
#print axioms seventy_percent_certificate_four_thirds_iff

end GaloisForLFunctions.TransThresholdPairCorrelation
