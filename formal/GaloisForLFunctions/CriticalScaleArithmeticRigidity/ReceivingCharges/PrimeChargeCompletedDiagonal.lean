import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeSmallPacketEnergy

/-!
# The full completed diagonal of a neutral prime charge

Conductor one has the same nonnegative Fourier representation and uniform
overlap bound as every other conductor. Exact harmonic centering makes its
coefficient cost quadratic in the inverse horizon logarithm.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  CompletedArithmeticForms

private theorem sum_Icc_split_one {Q : ℕ} (hQ : 1 ≤ Q) (f : ℕ → ℝ) :
    (∑ m ∈ Icc 1 Q, f m) = f 1 + ∑ m ∈ (Icc 1 Q).filter (fun m => m ≠ 1), f m := by
  have he (m : ℕ) : f m =
      (if m = 1 then f 1 else 0) + (if m ≠ 1 then f m else 0) := by
    by_cases hm : m = 1 <;> simp only [hm, if_true, if_false, not_true_eq_false, Ne,
      add_zero, zero_add]
  calc
    _ = (∑ m ∈ Icc 1 Q, if m = 1 then f 1 else 0) +
        ∑ m ∈ Icc 1 Q, if m ≠ 1 then f m else 0 := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun m _ => he m
    _ = _ := by rw [sum_ite_eq', if_pos (mem_Icc.mpr ⟨le_rfl, hQ⟩), sum_filter]

/-- The entire completed diagonal is nonnegative, including its polar coefficient. -/
theorem harmonicPrimeCharge_completed_diagonal_nonneg {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) (Q N : ℕ) (t : ℝ) :
    0 ≤ ∑ m ∈ Icc 1 Q,
      completedConductorEnergy φ c m * harmonicPrimeChargeCoefficients Q N t m ^ 2 := by
  exact sum_nonneg fun m hm => mul_nonneg
    (completedConductorEnergy_nonneg hφ hsupp hM hc (mem_Icc.mp hm).1) (sq_nonneg _)

/-- The full coefficient square keeps the reciprocal-prime gain and the exact polar cost. -/
theorem harmonicPrimeCharge_coefficient_square_le {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q ≤ N) (t : ℝ) :
    (∑ m ∈ Icc 1 Q, harmonicPrimeChargeCoefficients Q N t m ^ 2) ≤
      ((|t| + 8 * |t| / primePoleScale Q) / Real.log N) ^ 2 +
        (t / primePoleScale Q) ^ 2 *
          ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ) := by
  have hpole := harmonicPrimeCharge_pole_abs_le hQ hQN t
  have hpolar := mul_le_mul hpole hpole (abs_nonneg _) ((abs_nonneg _).trans hpole)
  simp only [← sq, sq_abs] at hpolar
  have hrest := harmonicPrimeCharge_nonpolar_weighted_sq_le Q N t
    (fun _ => 1) (fun _ _ => zero_le_one)
  simp only [one_mul] at hrest
  rw [sum_Icc_split_one (by omega : 1 ≤ Q)]
  exact add_le_add hpolar hrest

/-- Completed energy has a uniform diagonal bound at every overlap at least one. -/
theorem harmonicPrimeCharge_completed_diagonal_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 1 ≤ c) {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q ≤ N) (t : ℝ) :
    (∑ m ∈ Icc 1 Q,
      completedConductorEnergy φ c m * harmonicPrimeChargeCoefficients Q N t m ^ 2) ≤
      (|completeWeilSelfFinitePart φ 1| + 3) *
        (((|t| + 8 * |t| / primePoleScale Q) / Real.log N) ^ 2 +
          (t / primePoleScale Q) ^ 2 *
            ((∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) + primePoleScale Q)) := by
  have hE := completedConductorEnergy_le_logarithmic_uniform hφ hsupp hM hc
    (by norm_num : 0 < (1 : ℕ))
  simp only [Nat.cast_one, Real.log_one, mul_zero, add_zero] at hE
  have hpole := harmonicPrimeCharge_pole_abs_le hQ hQN t
  have hpolar := mul_le_mul hpole hpole (abs_nonneg _) ((abs_nonneg _).trans hpole)
  simp only [← sq, sq_abs] at hpolar
  have hD : 0 ≤ |completeWeilSelfFinitePart φ 1| + 3 := by positivity
  have hfirst := (mul_le_mul_of_nonneg_right hE
    (sq_nonneg (harmonicPrimeChargeCoefficients Q N t 1))).trans
      (mul_le_mul_of_nonneg_left hpolar hD)
  rw [sum_Icc_split_one (by omega : 1 ≤ Q)]
  exact (add_le_add hfirst
    (harmonicPrimeCharge_nonpolar_completedEnergy_le hφ hsupp hM hc Q N t)).trans_eq (by ring)

#print axioms harmonicPrimeCharge_completed_diagonal_nonneg
#print axioms harmonicPrimeCharge_coefficient_square_le
#print axioms harmonicPrimeCharge_completed_diagonal_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
