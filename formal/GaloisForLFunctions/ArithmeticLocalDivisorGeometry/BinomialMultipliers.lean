import GaloisForLFunctions.HTGeometry.PolynomialHeatProduct
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Exact coefficient inequalities for repeated real-factor repair

After scaling a conjugate pair, adjoining `n` equal real factors gives
`(1 + X)^n (X² - 2αX + 1)`. Its coefficient defect is a single binomial row.
The exact inequalities retain the full degree and every interior coefficient.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry

noncomputable section

/-- A normalized conjugate-pair factor multiplied by `n` equal real factors. -/
def binomialRepair (α : ℝ) (n : ℕ) : ℝ[X] :=
  (X + 1) ^ n * (X ^ 2 - C (2 * α) * X + 1)

/-- The entire signed contribution occupies one shifted binomial row. -/
theorem binomialRepair_eq (α : ℝ) (n : ℕ) :
    binomialRepair α n = (X + 1) ^ (n + 2) - C (2 * (α + 1)) *
      (X * (X + 1) ^ n) := by
  simp only [binomialRepair, pow_add, map_mul, map_add, map_ofNat, map_one]
  ring

theorem binomialRepair_coeff_zero (α : ℝ) (n : ℕ) :
    (binomialRepair α n).coeff 0 = 1 := by
  rw [binomialRepair_eq]
  simp [coeff_X_add_one_pow]

/-- The formula includes all multiplicities and remains valid outside the degree range. -/
theorem binomialRepair_coeff_succ (α : ℝ) (n j : ℕ) :
    (binomialRepair α n).coeff (j + 1) =
      ((n + 2).choose (j + 1) : ℝ) - 2 * (α + 1) * (n.choose j : ℝ) := by
  rw [binomialRepair_eq, coeff_sub, coeff_C_mul, coeff_X_mul,
    coeff_X_add_one_pow, coeff_X_add_one_pow]

/-- Cross multiplication removes factorials from the ratio of the two binomial rows. -/
theorem binomial_rows_identity (n j : ℕ) :
    (n + 2).choose (j + 1) * (j + 1) * (n + 1 - j) =
      (n + 2) * (n + 1) * n.choose j := by
  have h1 := Nat.add_one_mul_choose_eq n j
  have h2 := Nat.choose_mul_succ_eq (n + 1) (j + 1)
  have hsub : n + 1 + 1 - (j + 1) = n + 1 - j := by omega
  rw [hsub] at h2
  calc
    _ = ((n + 2).choose (j + 1) * (n + 1 - j)) * (j + 1) := by ring
    _ = (n + 1).choose (j + 1) * (n + 2) * (j + 1) := by rw [← h2]
    _ = (n + 2) * ((n + 1).choose (j + 1) * (j + 1)) := by ring
    _ = _ := by rw [← h1]; ring

/-- A coefficient's sign is exactly a quadratic inequality in its index. -/
theorem binomialRepair_coeff_nonneg_iff (α : ℝ) (n j : ℕ) (hj : j ≤ n) :
    0 ≤ (binomialRepair α n).coeff (j + 1) ↔
      2 * (α + 1) * (j + 1 : ℝ) * (n + 1 - j : ℝ) ≤ (n + 2 : ℝ) * (n + 1 : ℝ) := by
  have hc : 0 < (n.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj
  have hjr : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hd : 0 < (j + 1 : ℝ) * (n + 1 - j : ℝ) :=
    mul_pos (by positivity) (by linarith)
  have hid : ((n + 2).choose (j + 1) : ℝ) * (j + 1) * (n + 1 - j) =
      (n + 2) * (n + 1) * (n.choose j : ℝ) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) (binomial_rows_identity n j)
    have hle : j ≤ n + 1 := by omega
    push_cast [Nat.cast_sub hle] at h
    exact h
  rw [binomialRepair_coeff_succ]
  have heq : (j + 1 : ℝ) * (n + 1 - j) *
      (((n + 2).choose (j + 1) : ℝ) - 2 * (α + 1) * (n.choose j : ℝ)) =
      (n.choose j : ℝ) * ((n + 2) * (n + 1) -
        2 * (α + 1) * (j + 1) * (n + 1 - j)) := by
    nlinarith only [hid]
  rw [← mul_nonneg_iff_of_pos_left hd, heq, mul_nonneg_iff_of_pos_left hc, sub_nonneg]

/-- A finite, exact criterion whose order range grows with the actual multiplier degree. -/
theorem coeffNonneg_binomialRepair_iff (α : ℝ) (n : ℕ) :
    CoeffNonneg (binomialRepair α n) ↔
      ∀ j ≤ n, 2 * (α + 1) * (j + 1 : ℝ) * (n + 1 - j : ℝ) ≤
        (n + 2 : ℝ) * (n + 1 : ℝ) := by
  constructor
  · intro h j hj
    exact (binomialRepair_coeff_nonneg_iff α n j hj).mp (h (j + 1))
  · intro h k
    cases k with
    | zero => rw [binomialRepair_coeff_zero]; exact zero_le_one
    | succ j =>
      by_cases hj : j ≤ n
      · exact (binomialRepair_coeff_nonneg_iff α n j hj).mpr (h j hj)
      · rw [binomialRepair_coeff_succ, Nat.choose_eq_zero_of_lt (lt_of_not_ge hj)]
        simp only [Nat.cast_zero, mul_zero, sub_zero]
        positivity

/-- For an even number of real factors, the middle coefficient determines the entire cone. -/
theorem coeffNonneg_binomialRepair_even_iff (α : ℝ) (m : ℕ) :
    CoeffNonneg (binomialRepair α (2 * m)) ↔ α * (m + 1 : ℝ) ≤ m := by
  rw [coeffNonneg_binomialRepair_iff]
  have hmpos : (0 : ℝ) < m + 1 := by positivity
  constructor
  · intro h
    have hmid := h m (by omega)
    push_cast at hmid
    have hfac : 0 ≤ (m + 1 : ℝ) * (m - α * (m + 1)) := by
      nlinarith only [hmid]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hmpos).mp hfac)
  · intro h j hj
    have hjr : (j : ℝ) ≤ 2 * m := by exact_mod_cast hj
    have hd : 0 ≤ (j + 1 : ℝ) * (2 * m + 1 - j) :=
      mul_nonneg (by positivity) (by linarith)
    have hmax : (j + 1 : ℝ) * (2 * m + 1 - j) ≤ (m + 1 : ℝ) ^ 2 := by
      nlinarith only [sq_nonneg ((j : ℝ) - m)]
    have hbound : 2 * (α + 1) * (m + 1 : ℝ) ^ 2 ≤
        (2 * m + 2 : ℝ) * (2 * m + 1 : ℝ) := by
      have hf := mul_nonneg hmpos.le (sub_nonneg.mpr h)
      nlinarith only [hf]
    push_cast
    by_cases hα : 0 ≤ 2 * (α + 1)
    · have hm := mul_le_mul_of_nonneg_left hmax hα
      nlinarith only [hm, hbound]
    · have hn := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hα) hd
      have hr : 0 ≤ (2 * m + 2 : ℝ) * (2 * m + 1 : ℝ) := by positivity
      nlinarith only [hn, hr]

/-- Odd and subsequent even multiplier degrees have the same repair region. -/
theorem coeffNonneg_binomialRepair_odd_iff (α : ℝ) (m : ℕ) :
    CoeffNonneg (binomialRepair α (2 * m + 1)) ↔ α * (m + 2 : ℝ) ≤ m + 1 := by
  rw [coeffNonneg_binomialRepair_iff]
  have hmpos : (0 : ℝ) < m + 1 := by positivity
  constructor
  · intro h
    have hmid := h m (by omega)
    push_cast at hmid
    have hfac : 0 ≤ (m + 1 : ℝ) * (m + 1 - α * (m + 2)) := by
      nlinarith only [hmid]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hmpos).mp hfac)
  · intro h j hj
    have hjr : (j : ℝ) ≤ 2 * m + 1 := by exact_mod_cast hj
    have hd : 0 ≤ (j + 1 : ℝ) * (2 * m + 2 - j) :=
      mul_nonneg (by positivity) (by linarith)
    have hmax : (j + 1 : ℝ) * (2 * m + 2 - j) ≤
        (m + 1 : ℝ) * (m + 2 : ℝ) := by
      rcases le_or_gt j m with hjm | hjm
      · have hjm' : (j : ℝ) ≤ m := by exact_mod_cast hjm
        have hp := mul_nonneg (show 0 ≤ (m : ℝ) - j by linarith)
          (show 0 ≤ (m : ℝ) + 1 - j by linarith)
        nlinarith only [hp]
      · have hjm' : (m : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt hjm)
        have hp := mul_nonneg (show 0 ≤ (j : ℝ) - m by linarith)
          (show 0 ≤ (j : ℝ) - m - 1 by linarith)
        nlinarith only [hp]
    have hbound : 2 * (α + 1) * ((m + 1 : ℝ) * (m + 2 : ℝ)) ≤
        (2 * m + 3 : ℝ) * (2 * m + 2 : ℝ) := by
      have hf := mul_nonneg hmpos.le (sub_nonneg.mpr h)
      nlinarith only [hf]
    push_cast
    by_cases hα : 0 ≤ 2 * (α + 1)
    · have hm := mul_le_mul_of_nonneg_left hmax hα
      nlinarith only [hm, hbound]
    · have hn := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hα) hd
      have hr : 0 ≤ (2 * m + 3 : ℝ) * (2 * m + 2 : ℝ) := by positivity
      nlinarith only [hn, hr]

end

end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
