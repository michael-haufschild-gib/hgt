import GaloisForLFunctions.ArithmeticDefectRigidity.TheRenormalizedCofactorIsAntipodalOnEscape

/-!
# Every bounded moving localization retains the signed density

The total-variation budget pays an arbitrary cell multiplier in `[-1,1]`. The same bound
holds for a different multiplier at each horizon, so normalization on an escaping receiver
preserves the antipodal density without a fixed-support assumption.
-/

open Finset Filter Topology RHTower
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- Cell multipliers with unit absolute bound, including moving cutoffs and signed windows. -/
abbrev BoundedCellMultiplier := ℕ → Set.Icc (-1 : ℝ) 1

/-- The localized difference between cofactor work and negative receiver energy. -/
def localizedCofactorDensityError (ε : ℝ) (T : ℕ) (φ : BoundedCellMultiplier) : ℝ :=
  ∑ n ∈ Icc 1 T, (φ n : ℝ) *
    (pmPowerDampedCenteredDivisorPrefix ε n ^ 2 +
      pmPowerDampedCenteredDivisorPrefix ε n * renormalizedCofactor ε n) /
        ((n : ℝ) * ((n : ℝ) + 1))

/-- One total-variation estimate pays every bounded localization. -/
theorem abs_localizedCofactorDensityError_le_variation (ε : ℝ) (T : ℕ)
    (φ : BoundedCellMultiplier) :
    |localizedCofactorDensityError ε T φ| ≤ renormalizedCofactorVariation ε T := by
  unfold localizedCofactorDensityError renormalizedCofactorVariation
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
  have hφ : |(φ n : ℝ)| ≤ 1 := abs_le.mpr (φ n).property
  rw [abs_div, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) by positivity)]
  exact div_le_div_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hφ (abs_nonneg _)) (by positivity)

/-- The actual source controls every localized error with the same paid remainder. -/
theorem localizedCofactorDensityError_sq_le (ε : SubcriticalDamping) (T : ℕ)
    (φ : BoundedCellMultiplier) :
    localizedCofactorDensityError ε T φ ^ 2 ≤
      dampedMobiusEnergy ε T * forcingRemainderBudget ε ^ 2 := by
  have h := pow_le_pow_left₀ (abs_nonneg _)
    (abs_localizedCofactorDensityError_le_variation ε T φ) 2
  rw [sq_abs] at h
  exact h.trans (renormalizedCofactorVariation_sq_le ε T)

/-- The normalized error bound is uniform over the complete class of cell multipliers. -/
theorem normalized_localizedCofactorDensityError_sq_le (ε : SubcriticalDamping) (T : ℕ)
    (φ : BoundedCellMultiplier) :
    (localizedCofactorDensityError ε (T + 1) φ / dampedMobiusEnergy ε (T + 1)) ^ 2 ≤
      forcingRemainderBudget ε ^ 2 / dampedMobiusEnergy ε (T + 1) := by
  have hE := receiverEnergy_succ_pos ε T
  rw [div_pow]
  calc
    _ ≤ (dampedMobiusEnergy ε (T + 1) * forcingRemainderBudget ε ^ 2) /
        dampedMobiusEnergy ε (T + 1) ^ 2 :=
      div_le_div_of_nonneg_right (localizedCofactorDensityError_sq_le ε (T + 1) φ) (sq_nonneg _)
    _ = _ := by field_simp [hE.ne']

/-- All horizon-dependent bounded localizations retain the signed density on escape. -/
theorem admits_or_all_moving_localizations_retain_density (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ φ : ℕ → BoundedCellMultiplier,
      Tendsto (fun T => (localizedCofactorDensityError ε (T + 1) (φ T) /
        dampedMobiusEnergy ε (T + 1)) ^ 2) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · have hB : Tendsto (fun T => forcingRemainderBudget ε ^ 2 /
        dampedMobiusEnergy ε (T + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hE.comp (tendsto_add_atTop_nat 1))
    exact Or.inr fun φ => squeeze_zero (fun T => sq_nonneg _)
      (fun T => normalized_localizedCofactorDensityError_sq_le ε T (φ T)) hB

end GaloisForLFunctions.ArithmeticDefectRigidity
