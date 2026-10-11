import GaloisForLFunctions.RHTower.WeilLogShiftArithmeticConcentration
import GaloisForLFunctions.RHTower.WeilLogShiftBinomialProbabilityMoments

/-! Centered first moments and mixed second moments for weighted mean-bias control. -/

open scoped BigOperators

namespace RHTower

theorem finiteWeilArithmeticAbsProfile_half_first_moment (r : ℕ) :
    (∑ i, finiteWeilArithmeticAbsProfile r i *
      (((i : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2)) = 0 := by
  have hf : (∑ i, finiteWeilArithmeticAbsProfile r i * ((i : ℕ) : ℝ)) =
      (((r + 1 : ℕ) : ℝ) / 2) * finiteWeilArithmeticMass r := by
    simp only [finiteWeilArithmeticAbsProfile_eq_binomial, mul_assoc, ← Finset.mul_sum]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((r + 1).choose i : ℝ) * (i : ℝ)) (r + 2),
      finiteWeil_binomial_first_moment, finiteWeilArithmeticMass_eq_binomial]
    ring
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hf, finiteWeilArithmeticAbsProfile_sum]
  ring

theorem finiteWeilArithmeticAbsProfile_mixed_second_bound (r : ℕ) :
    (∑ i, finiteWeilArithmeticAbsProfile r i *
      |((i : ℕ) : ℝ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)| *
        |((i : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2|) ≤
      ((r + 1 : ℕ) : ℝ) * finiteWeilArithmeticMass r := by
  let q := finiteWeilArithmeticAbsProfile r
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let G := finiteWeilArithmeticMass r
  let d := fun i : Fin (r + 2) => ((i : ℕ) : ℝ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)
  let x := fun i : Fin (r + 2) => ((i : ℕ) : ℝ) - n / 2
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hG : 0 ≤ G := le_trans (by norm_num) (finiteWeilArithmeticMass_ge_two r)
  have hpoint (i : Fin (r + 2)) : |d i| * |x i| ≤ (d i ^ 2 + x i ^ 2) / 2 := by
    nlinarith only [sq_nonneg (|d i| - |x i|), sq_abs (d i), sq_abs (x i)]
  have h2 := finiteWeilArithmeticAbsProfile_center_second_moment r
  have hx := finiteWeilArithmeticAbsProfile_half_second_moment r
  change (∑ i, q i * d i ^ 2) ≤ (n + 1) / 2 * G at h2
  change (∑ i, q i * x i ^ 2) = n / 4 * G at hx
  change (∑ i, q i * |d i| * |x i|) ≤ n * G
  calc
    _ ≤ ∑ i, q i * ((d i ^ 2 + x i ^ 2) / 2) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hpoint i) (finiteWeilArithmeticAbsProfile_pos r i).le
    _ = ((∑ i, q i * d i ^ 2) + (∑ i, q i * x i ^ 2)) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := by
      have hp := mul_nonneg (sub_nonneg.mpr hn1) hG
      nlinarith only [h2, hx, hp, hG]

end RHTower
