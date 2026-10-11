import GaloisForLFunctions.RHTower.WeilLogShiftParityMixture

/-! The parity-conditioned binomial model is a probability segment with the exact fiber metric. -/

open scoped BigOperators
noncomputable section
namespace RHTower

def finiteWeilBinomialMixture (r : ℕ) (a : ℝ) (i : Fin (r + 2)) : ℝ :=
  (((r + 1).choose (i : ℕ) : ℝ) + (2 * a - 1) * finiteWeilBinomialDual r i) /
    (2 : ℝ) ^ (r + 1)

theorem finiteWeilBinomialProbability_sum (r : ℕ) :
    (∑ i : Fin (r + 2), ((r + 1).choose (i : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)) = 1 := by
  have hG : 0 < finiteWeilArithmeticMass r :=
    lt_of_lt_of_le (by norm_num) (finiteWeilArithmeticMass_ge_two r)
  simp only [← finiteWeilArithmeticAbsProfile_normalized]
  rw [← Finset.sum_div, finiteWeilArithmeticAbsProfile_sum, div_self hG.ne']

theorem finiteWeilBinomialProbability_parity (r : ℕ) :
    (∑ i : Fin (r + 2), finiteWeilBinomialParity r i *
      (((r + 1).choose (i : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1))) = 0 := by
  have hb : ∑ i, finiteWeilBinomialDual r i = 0 := by
    simpa only [pow_zero, mul_one] using finiteWeilBinomialDual_moment r 0 (Nat.zero_le r)
  simp only [← mul_div_assoc, ← finiteWeilBinomialDual_eq_parity, ← Finset.sum_div, hb, zero_div]

theorem finiteWeilBinomialMixture_parity_factor (r : ℕ) (a : ℝ) (i : Fin (r + 2)) :
    finiteWeilBinomialMixture r a i =
      (1 + (2 * a - 1) * finiteWeilBinomialParity r i) *
        (((r + 1).choose (i : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)) := by
  rw [finiteWeilBinomialMixture, finiteWeilBinomialDual_eq_parity]
  ring

theorem finiteWeilBinomialMixture_sum (r : ℕ) (a : ℝ) :
    ∑ i, finiteWeilBinomialMixture r a i = 1 := by
  simp only [finiteWeilBinomialMixture_parity_factor, add_mul, one_mul, mul_assoc,
    Finset.sum_add_distrib, ← Finset.mul_sum, finiteWeilBinomialProbability_sum,
    finiteWeilBinomialProbability_parity, mul_zero, add_zero]

theorem finiteWeilBinomialMixture_nonneg (r : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (i : Fin (r + 2)) : 0 ≤ finiteWeilBinomialMixture r a i := by
  rw [finiteWeilBinomialMixture_parity_factor]
  exact mul_nonneg (finiteWeilBinomialParity_multiplier_bounds r a ha ha1 i).1 (by positivity)

theorem finiteWeilBinomialMixture_parity_reading (r : ℕ) (a : ℝ) :
    (∑ i, finiteWeilBinomialParity r i * finiteWeilBinomialMixture r a i) = 2 * a - 1 := by
  simpa only [finiteWeilBinomialMixture_parity_factor] using
    finiteWeil_parity_tilt_reading
      (fun i : Fin (r + 2) => ((r + 1).choose (i : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1))
      (finiteWeilBinomialParity r) a (finiteWeilBinomialParity_sq r)
      (finiteWeilBinomialProbability_sum r) (finiteWeilBinomialProbability_parity r)

/-- The binomial model retains the canonical fiber's exact l1 distance at every order. -/
theorem finiteWeilBinomialMixture_abs_distance (r : ℕ) (a b : ℝ) :
    (∑ i, |finiteWeilBinomialMixture r a i - finiteWeilBinomialMixture r b i|) =
      2 * |a - b| := by
  have hi (i : Fin (r + 2)) :
      |finiteWeilBinomialMixture r a i - finiteWeilBinomialMixture r b i| =
        (2 * |a - b|) * (((r + 1).choose (i : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)) := by
    have heq : finiteWeilBinomialMixture r a i - finiteWeilBinomialMixture r b i =
        2 * (a - b) * finiteWeilBinomialParity r i *
          (((r + 1).choose (i : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)) := by
      rw [finiteWeilBinomialMixture_parity_factor, finiteWeilBinomialMixture_parity_factor]
      ring
    rw [heq]
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), finiteWeilBinomialParity_abs,
      abs_of_nonneg (by positivity :
        0 ≤ ((r + 1).choose (i : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)), mul_one]
  simp only [hi, ← Finset.mul_sum, finiteWeilBinomialProbability_sum, mul_one]

end RHTower
