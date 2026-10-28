import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheMeanZeroCenterRowsAreUniformlyBounded
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCenterCorrectionHasBoundedPoleResidual
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPoleProfilesAreAsymptoticallyOrthonormal

/-!
# The complete center correction selects conductor one

The arithmetic point is the constant periodic mode. Every other Ramanujan mode
has zero complete-period mean and hence bounded interval sums. The harmonic row
identities therefore give a bounded unnormalized residual with a charge shift
only at conductor one.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open RenormalizedBiarithmeticGeometry HTGeometry

private theorem normalized_mode_one (n : ℕ) : normalizedRamanujanMode 1 n = 1 := by
  simp only [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one,
    Nat.cast_one, Real.sqrt_one, div_one]

private theorem normalized_mode_period_sum_zero {m : ℕ} (hm : 0 < m) (hm1 : m ≠ 1) :
    ∑ j ∈ range m, normalizedRamanujanMode m j = 0 := by
  have h := periodMean_normalizedRamanujanMode_mul hm zero_lt_one dvd_rfl (one_dvd m) hm
  simp only [normalized_mode_one, mul_one, if_neg hm1, periodMean] at h
  rcases div_eq_zero_iff.mp h with h | h
  · exact h
  · exact False.elim ((by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0) h)

/-- Every fixed Ramanujan mode has bounded square residual under the complete center correction. -/
theorem exists_uniform_centerCorrection_ramanujan_residual_bound {m : ℕ}
    (hm : 0 < m) (α : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    (∑ n ∈ Icc 1 N,
      ((α / N) * (∑ j ∈ Icc 1 N,
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n - archimedeanCenterKernel n j) *
          ramanujanPoleProfile m j) -
        (if m = 1 then α else 0) * ramanujanPoleProfile m n) ^ 2) ≤ C := by
  by_cases hm1 : m = 1
  · subst m
    refine ⟨6 * α ^ 2, by positivity, fun N => ?_⟩
    simpa only [ramanujanPoleProfile, normalized_mode_one, if_pos rfl, ite_true,
      mul_one_div, mul_div_assoc, mul_one] using sum_sq_centerCorrection_pole_residual_le α N
  · let A : ℝ := ∑ j ∈ range m, |normalizedRamanujanMode m j|
    have hA : 0 ≤ A := sum_nonneg fun j _ => abs_nonneg _
    have hB : ∀ l k : ℕ, l ≤ k →
        |∑ j ∈ Ico l k, normalizedRamanujanMode m j| ≤ 2 * A :=
      abs_sum_Ico_le_of_periodic hm (normalizedRamanujanMode_periodic hm)
        (normalized_mode_period_sum_zero hm hm1)
    refine ⟨α ^ 2 * (4 * (2 * A) + A) ^ 2, by positivity, fun N => ?_⟩
    simpa only [if_neg hm1, zero_mul, sub_zero, ramanujanPoleProfile] using
      sum_sq_centerCorrection_poleProfile_le hA (abs_normalizedRamanujanMode_le hm) hB α N

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
