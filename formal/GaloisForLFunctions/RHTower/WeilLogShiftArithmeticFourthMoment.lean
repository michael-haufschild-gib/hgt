import GaloisForLFunctions.RHTower.WeilLogShiftBinomialFourthMoment
import GaloisForLFunctions.RHTower.WeilLogShiftArithmeticConcentration

/-! Fourth moments control displacement-weighted quadratic tests of the arithmetic profile. -/

open scoped BigOperators

namespace RHTower

theorem finiteWeilArithmeticAbsProfile_half_fourth_moment (r : ℕ) :
    (∑ i, finiteWeilArithmeticAbsProfile r i *
      (((i : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 4) =
      ((3 * ((r + 1 : ℕ) : ℝ) ^ 2 - 2 * ((r + 1 : ℕ) : ℝ)) / 16) * finiteWeilArithmeticMass r := by
  simp only [finiteWeilArithmeticAbsProfile_eq_binomial, mul_assoc, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((r + 1).choose i : ℝ) *
    ((i : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 4) (r + 2),
    finiteWeil_binomial_half_centered_fourth_moment, finiteWeilArithmeticMass_eq_binomial]
  ring

theorem finiteWeilArithmeticAbsProfile_half_fourth_bound (r : ℕ) :
    (∑ i, finiteWeilArithmeticAbsProfile r i *
      (((i : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 4) ≤
      ((r + 1 : ℕ) : ℝ) ^ 2 * finiteWeilArithmeticMass r := by
  rw [finiteWeilArithmeticAbsProfile_half_fourth_moment]
  apply mul_le_mul_of_nonneg_right
  · have hn : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith only [hn, sq_nonneg (((r + 1 : ℕ) : ℝ))]
  · have hG := finiteWeilArithmeticMass_ge_two r
    linarith only [hG]

theorem finiteWeilArithmeticAbsProfile_mixed_third_bound (r : ℕ) :
    (∑ i, finiteWeilArithmeticAbsProfile r i *
      |((i : ℕ) : ℝ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)| *
        (((i : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) ^ 2) ≤
      finiteWeilArithmeticMass r * ((r + 1 : ℕ) : ℝ) *
        Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) := by
  let q := finiteWeilArithmeticAbsProfile r
  let d := fun i : Fin (r + 2) => ((i : ℕ) : ℝ) - ((finiteWeilArithmeticCenter r : Fin (r + 2)) : ℕ)
  let x := fun i : Fin (r + 2) => ((i : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2
  let G := finiteWeilArithmeticMass r
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let V : ℝ := (n + 1) / 2
  have hG : 0 < G := lt_of_lt_of_le (by norm_num) (finiteWeilArithmeticMass_ge_two r)
  have hn : 0 < n := by dsimp [n]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (Fin (r + 2)))
    (r := fun i => q i * |d i| * x i ^ 2)
    (f := fun i => q i * d i ^ 2) (g := fun i => q i * x i ^ 4)
    (fun i _ => mul_nonneg (finiteWeilArithmeticAbsProfile_pos r i).le (by positivity))
    (fun i _ => mul_nonneg (finiteWeilArithmeticAbsProfile_pos r i).le (by positivity))
    (fun i _ => le_of_eq (by rw [mul_pow, mul_pow, sq_abs]; ring))
  have h2 := finiteWeilArithmeticAbsProfile_center_second_moment r
  have h4 := finiteWeilArithmeticAbsProfile_half_fourth_bound r
  change (∑ i, q i * d i ^ 2) ≤ V * G at h2
  change (∑ i, q i * x i ^ 4) ≤ n ^ 2 * G at h4
  have hs := Real.sq_sqrt hV
  have hsq : (∑ i, q i * |d i| * x i ^ 2) ^ 2 ≤ (G * n * Real.sqrt V) ^ 2 := by
    calc
      _ ≤ (∑ i, q i * d i ^ 2) * ∑ i, q i * x i ^ 4 := hcs
      _ ≤ (V * G) * (n ^ 2 * G) := mul_le_mul h2 h4
        (Finset.sum_nonneg fun i _ => mul_nonneg (finiteWeilArithmeticAbsProfile_pos r i).le (by positivity))
        (mul_nonneg hV hG.le)
      _ = _ := by rw [mul_pow, mul_pow, hs]; ring
  change (∑ i, q i * |d i| * x i ^ 2) ≤ G * n * Real.sqrt V
  have hp : 0 ≤ G * n * Real.sqrt V := by positivity
  nlinarith only [hsq, hp]

end RHTower
