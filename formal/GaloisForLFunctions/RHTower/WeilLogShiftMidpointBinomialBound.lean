import GaloisForLFunctions.RHTower.WeilLogShiftProfileNormalization
import GaloisForLFunctions.RHTower.WeilLogShiftMidpointProfile

/-! A finite l1 bound compares the actual midpoint probability with the binomial law. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem finiteWeilCanonicalMassProfile_l1_error (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    (∑ i, |finiteWeilCanonicalMassProfile r k i - finiteWeilArithmeticAbsProfile r i|) ≤
      finiteWeilArithmeticMass r *
        (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  calc
    _ ≤ ∑ i, (finiteWeilArithmeticAbsProfile r i *
        |((i : ℕ) : ℝ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)|) /
          ((r + 1 : ℕ) : ℝ) :=
      Finset.sum_le_sum fun i _ => finiteWeilCanonicalMassProfile_error r k hwidth i
    _ ≤ _ := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      simpa only [div_eq_mul_inv, mul_assoc] using mul_le_mul_of_nonneg_right
        (finiteWeilArithmeticAbsProfile_center_first_moment r) (by positivity :
          0 ≤ (((r + 1 : ℕ) : ℝ))⁻¹)

/-- The full l1 distance is controlled without estimating the largest logarithmic weight. -/
theorem finiteWeilCanonicalMixture_midpoint_binomial_bound (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    (∑ i, |finiteWeilCanonicalMixture r k (1 / 2) i -
      ((r + 1).choose (i : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)|) ≤
      2 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  have hF : 0 < ∑ i, finiteWeilCanonicalMassProfile r k i := by
    have hc := Finset.single_le_sum (s := Finset.univ)
      (f := finiteWeilCanonicalMassProfile r k)
      (fun i _ => (finiteWeilCanonicalMassProfile_pos r k i).le)
      (Finset.mem_univ (finiteWeilArithmeticCenter r))
    rw [finiteWeilCanonicalMassProfile_center] at hc
    linarith only [hc]
  have hG : 0 < finiteWeilArithmeticMass r :=
    lt_of_lt_of_le (by norm_num) (finiteWeilArithmeticMass_ge_two r)
  have hnorm := finiteWeil_profile_normalization_l1 (finiteWeilCanonicalMassProfile r k)
    (finiteWeilArithmeticAbsProfile r) (fun i => (finiteWeilCanonicalMassProfile_pos r k i).le)
    hF (by rwa [finiteWeilArithmeticAbsProfile_sum])
  simp only [finiteWeilArithmeticAbsProfile_sum] at hnorm
  simp only [finiteWeilCanonicalMixture_midpoint_profile,
    ← finiteWeilArithmeticAbsProfile_normalized]
  calc
    _ ≤ 2 * (∑ i, |finiteWeilCanonicalMassProfile r k i - finiteWeilArithmeticAbsProfile r i|) /
        finiteWeilArithmeticMass r := hnorm
    _ ≤ _ := by
      apply (div_le_iff₀ hG).mpr
      have hD := finiteWeilCanonicalMassProfile_l1_error r k hwidth
      nlinarith only [hD]

end RHTower
