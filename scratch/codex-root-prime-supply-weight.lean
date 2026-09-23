import Mathlib

private theorem prime_supply_weight_ge
    {K a x P : ℝ} {B : ℕ}
    (hK : 0 < K) (ha : 0 < a) (hx : 1 < x)
    (hB : 0 < B) (hBx : (B : ℝ) ≤ K * x)
    (hP : a * (x / Real.log x) ≤ P) :
    (a * Real.log 2 / Real.sqrt K) *
        (Real.sqrt x / Real.log x) ≤
      P * (Real.log 2 / Real.sqrt B) := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hsB : 0 < Real.sqrt (B : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hB)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsble : Real.sqrt (B : ℝ) ≤ Real.sqrt (K * x) :=
    Real.sqrt_le_sqrt hBx
  have hweight : Real.log 2 / Real.sqrt (K * x) ≤
      Real.log 2 / Real.sqrt B :=
    div_le_div_of_nonneg_left hlog2.le hsB hsble
  have hcoeff : 0 ≤ a * (x / Real.log x) := by positivity
  have hprod : a * (x / Real.log x) *
        (Real.log 2 / Real.sqrt (K * x)) ≤
      a * (x / Real.log x) * (Real.log 2 / Real.sqrt B) :=
    mul_le_mul_of_nonneg_left hweight hcoeff
  have hprodP : a * (x / Real.log x) *
        (Real.log 2 / Real.sqrt B) ≤
      P * (Real.log 2 / Real.sqrt B) :=
    mul_le_mul_of_nonneg_right hP (by positivity)
  have hsplit : Real.sqrt (K * x) = Real.sqrt K * Real.sqrt x :=
    Real.sqrt_mul hK.le x
  have hroot : (Real.sqrt x) ^ (2 : ℕ) = x := Real.sq_sqrt (by linarith)
  calc
    (a * Real.log 2 / Real.sqrt K) * (Real.sqrt x / Real.log x) =
        a * (x / Real.log x) *
          (Real.log 2 / Real.sqrt (K * x)) := by
            rw [hsplit]
            field_simp [ne_of_gt hlx, ne_of_gt hsx, ne_of_gt hsK]
            nlinarith [hroot]
    _ ≤ _ := hprod
    _ ≤ _ := hprodP

private theorem prime_window_log_debit_le
    {K x : ℝ} {B : ℕ}
    (hK : 0 < K) (hx : 0 < x) (hB : 1 ≤ B)
    (hBx : (B : ℝ) ≤ K * x) :
    2 * Real.log B + Real.log 2 / Real.sqrt B ≤
      2 * (Real.log K + Real.log x) + Real.log 2 := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlogB : Real.log (B : ℝ) ≤ Real.log K + Real.log x := by
    calc
      Real.log (B : ℝ) ≤ Real.log (K * x) :=
        Real.log_le_log hBpos hBx
      _ = Real.log K + Real.log x :=
        Real.log_mul (ne_of_gt hK) (ne_of_gt hx)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt B := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ B by exact_mod_cast hB)
    simpa using h
  have hlog2 : 0 ≤ Real.log 2 :=
    le_of_lt (Real.log_pos (by norm_num))
  have hcost : Real.log 2 / Real.sqrt B ≤ Real.log 2 := by
    simpa using div_le_div_of_nonneg_left hlog2 (by norm_num : (0:ℝ)<1) hsqrt1
  linarith
