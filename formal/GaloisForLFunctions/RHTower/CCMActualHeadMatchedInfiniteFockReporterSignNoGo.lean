import GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseProjectiveFockCocycle
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseProjectiveGaugeComplexDiracTwoShear

/-!
# Sign obstruction for the actual matched infinite-Fock reporter

The actual matched CCM source already has one infinite positive-semidefinite coherent-Fock
carrier.  Its exact source reporter is nevertheless not positive: every literal prime-power atom
has a positive reporter at outer phase `2π` and a negative reporter at outer phase `π`.  Equivalently,
the positive/negative probe ratio crosses from above one to below one while the global kernel is
positive semidefinite at both frequencies.

This kills pointwise positivity extraction from the assembled Fock carrier.  Any surviving
source-to-Ward mechanism must use nonlocal cross-frequency coupling or an independent
source-specific phase law; positivity of the carrier alone cannot supply the missing sign.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate ComplexOrder RealInnerProductSpace

noncomputable section
namespace RHTower

/-- Frequency at which one arithmetic atom has outer phase `2π`. -/
def ccmActualHeadMatchedPhasePositiveReporterFrequency (n : ℕ) : ℝ :=
  1 / Real.log n

/-- Frequency at which one arithmetic atom has antipodal outer phase `π`. -/
def ccmActualHeadMatchedPhaseNegativeReporterFrequency (n : ℕ) : ℝ :=
  1 / (2 * Real.log n)

theorem ccmActualHeadMatchedPhasePositiveReporterFrequency_ne_zero
    {n : ℕ} (hn : 1 < n) :
    ccmActualHeadMatchedPhasePositiveReporterFrequency n ≠ 0 := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  exact one_div_ne_zero hlog.ne'

theorem ccmActualHeadMatchedPhaseNegativeReporterFrequency_ne_zero
    {n : ℕ} (hn : 1 < n) :
    ccmActualHeadMatchedPhaseNegativeReporterFrequency n ≠ 0 := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  exact one_div_ne_zero (mul_ne_zero (by norm_num) hlog.ne')

theorem ccmActualHeadMatchedPhasePositiveReporterFrequency_phase
    {n : ℕ} (hn : 1 < n) :
    2 * Real.pi * Real.log n *
        ccmActualHeadMatchedPhasePositiveReporterFrequency n =
      2 * Real.pi := by
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  unfold ccmActualHeadMatchedPhasePositiveReporterFrequency
  field_simp

theorem ccmActualHeadMatchedPhaseNegativeReporterFrequency_phase
    {n : ℕ} (hn : 1 < n) :
    2 * Real.pi * Real.log n *
        ccmActualHeadMatchedPhaseNegativeReporterFrequency n =
      Real.pi := by
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  unfold ccmActualHeadMatchedPhaseNegativeReporterFrequency
  field_simp

theorem ccmActualHeadMatchedOrientedPhaseSymbol_re_pos_at_positiveReporterFrequency
    {n : ℕ} (hn : 1 < n) (hw : 0 < criticalMellinAtomWeight n) :
    0 < (ccmActualHeadMatchedOrientedPhaseSymbol n
      (ccmActualHeadMatchedPhasePositiveReporterFrequency n)).re := by
  rw [ccmActualHeadMatchedOrientedPhaseSymbol_re,
    ccmActualHeadMatchedPhasePositiveReporterFrequency_phase hn]
  simp only [Real.cos_two_pi, Real.sin_two_pi, one_mul, zero_mul, add_zero]
  exact ccmActualHeadMatchedCosinePhaseProfile_pos_of_weight_pos_of_ne_zero hw
    (ccmActualHeadMatchedPhasePositiveReporterFrequency_ne_zero hn)

theorem ccmActualHeadMatchedOrientedPhaseSymbol_re_neg_at_negativeReporterFrequency
    {n : ℕ} (hn : 1 < n) (hw : 0 < criticalMellinAtomWeight n) :
    (ccmActualHeadMatchedOrientedPhaseSymbol n
      (ccmActualHeadMatchedPhaseNegativeReporterFrequency n)).re < 0 := by
  rw [ccmActualHeadMatchedOrientedPhaseSymbol_re,
    ccmActualHeadMatchedPhaseNegativeReporterFrequency_phase hn]
  simp only [Real.cos_pi, Real.sin_pi, neg_one_mul, zero_mul, add_zero]
  exact neg_lt_zero.mpr <|
    ccmActualHeadMatchedCosinePhaseProfile_pos_of_weight_pos_of_ne_zero hw
      (ccmActualHeadMatchedPhaseNegativeReporterFrequency_ne_zero hn)

theorem ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio_gt_one_at_positiveReporterFrequency
    {n : ℕ} (hn : 1 < n) (hw : 0 < criticalMellinAtomWeight n) :
    1 < ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio
      (ccmActualHeadMatchedPhasePositiveReporterFrequency n) n := by
  rw [ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio,
    ccmActualHeadMatchedPhaseProjectiveFockRatio_eq_exp, Real.one_lt_exp_iff]
  exact mul_pos (by norm_num) <|
    ccmActualHeadMatchedOrientedPhaseSymbol_re_pos_at_positiveReporterFrequency hn hw

theorem ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio_lt_one_at_negativeReporterFrequency
    {n : ℕ} (hn : 1 < n) (hw : 0 < criticalMellinAtomWeight n) :
    ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio
        (ccmActualHeadMatchedPhaseNegativeReporterFrequency n) n < 1 := by
  rw [ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio,
    ccmActualHeadMatchedPhaseProjectiveFockRatio_eq_exp, Real.exp_lt_one_iff]
  exact mul_neg_of_pos_of_neg (by norm_num) <|
    ccmActualHeadMatchedOrientedPhaseSymbol_re_neg_at_negativeReporterFrequency hn hw

/-- Exact sign straddle for every literal prime-power atom, inside PSD kernels at both points. -/
theorem ccmActualHeadMatchedPhaseGlobalProjectiveFockPrimePowerReporterSignStraddle
    (p : Nat.Primes) (e : ℕ) :
    let n := xiGammaEulerValuationNat (p, e)
    GaloisForLFunctions.HTGeometry.IsPSDKernel
        (ccmActualHeadMatchedPhaseGlobalProjectiveFockKernel
          (ccmActualHeadMatchedPhasePositiveReporterFrequency n)) ∧
      1 < ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio
        (ccmActualHeadMatchedPhasePositiveReporterFrequency n) n ∧
      GaloisForLFunctions.HTGeometry.IsPSDKernel
        (ccmActualHeadMatchedPhaseGlobalProjectiveFockKernel
          (ccmActualHeadMatchedPhaseNegativeReporterFrequency n)) ∧
      ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio
        (ccmActualHeadMatchedPhaseNegativeReporterFrequency n) n < 1 := by
  dsimp only
  have hn : 1 < xiGammaEulerValuationNat (p, e) :=
    one_lt_xiGammaEulerValuationNat p e
  have hw : 0 < criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) := by
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  exact ⟨ccmActualHeadMatchedPhaseGlobalProjectiveFockKernel_isPSDKernel _,
    ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio_gt_one_at_positiveReporterFrequency hn hw,
    ccmActualHeadMatchedPhaseGlobalProjectiveFockKernel_isPSDKernel _,
    ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio_lt_one_at_negativeReporterFrequency hn hw⟩

theorem ccmActualHeadMatchedPhaseGlobalProjectiveFockPointwiseRatioLowerBoundRouteKilled :
    ¬ ∀ (xi : ℝ) (n : ℕ),
      GaloisForLFunctions.HTGeometry.IsPSDKernel
          (ccmActualHeadMatchedPhaseGlobalProjectiveFockKernel xi) →
        1 ≤ ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio xi n := by
  intro h
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  let n := xiGammaEulerValuationNat (p, 0)
  have hn : 1 < n := one_lt_xiGammaEulerValuationNat p 0
  have hw : 0 < criticalMellinAtomWeight n := by
    dsimp only [n]
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p 0)
  have hle := h (ccmActualHeadMatchedPhaseNegativeReporterFrequency n) n
    (ccmActualHeadMatchedPhaseGlobalProjectiveFockKernel_isPSDKernel _)
  exact (not_le_of_gt <|
    ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio_lt_one_at_negativeReporterFrequency
      hn hw) hle

/--
Positive semidefiniteness of the assembled actual-source Fock kernel cannot imply nonnegativity of
its exact logarithmic source reporter, even pointwise on the literal prime-power family.
-/
theorem ccmActualHeadMatchedPhaseGlobalProjectiveFockPointwiseReporterPositivityRouteKilled :
    ¬ ∀ (xi : ℝ) (n : ℕ),
      GaloisForLFunctions.HTGeometry.IsPSDKernel
          (ccmActualHeadMatchedPhaseGlobalProjectiveFockKernel xi) →
        0 ≤ (1 / 2 : ℝ) * Real.log
          (ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio xi n) := by
  intro h
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  let n := xiGammaEulerValuationNat (p, 0)
  have hn : 1 < n := one_lt_xiGammaEulerValuationNat p 0
  have hw : 0 < criticalMellinAtomWeight n := by
    dsimp only [n]
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p 0)
  have hnonneg := h (ccmActualHeadMatchedPhaseNegativeReporterFrequency n) n
    (ccmActualHeadMatchedPhaseGlobalProjectiveFockKernel_isPSDKernel _)
  have heq :
      (1 / 2 : ℝ) * Real.log
          (ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio
            (ccmActualHeadMatchedPhaseNegativeReporterFrequency n) n) =
        (ccmActualHeadMatchedOrientedPhaseSymbol n
          (ccmActualHeadMatchedPhaseNegativeReporterFrequency n)).re := by
    simpa [ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio] using
      (half_log_ccmActualHeadMatchedPhaseProjectiveFockRatio id
        (ccmActualHeadMatchedPhaseNegativeReporterFrequency n) n)
  rw [heq] at hnonneg
  exact (not_le_of_gt <|
    ccmActualHeadMatchedOrientedPhaseSymbol_re_neg_at_negativeReporterFrequency hn hw) hnonneg

end RHTower
