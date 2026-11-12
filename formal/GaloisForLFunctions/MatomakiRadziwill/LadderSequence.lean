import GaloisForLFunctions.MatomakiRadziwill.LadderDensity

/-!
# The scale sequence of the ladder

With `L = log h`, the logarithmic endpoints of the ladder scales are
`a_0 = 200 log L`, `b_0 = L/2`, and `a_{j+1} = 2b_j²`, `b_{j+1} = 4b_j⁴ = a_{j+1}²` (`seqA`, `seqB`); the
block widths are `H_0 = L^{25}`, `H_{j+1} = a_{j+1}^8` (`seqH`).  For `L ≥ 2^{20}`:

* the scales are proper and ordered: `a_j + 1 ≤ b_j < a_{j+1}` (`seqA_add_one_le_seqB`,
  `seqB_lt_seqA_succ`);
* they grow: `b_j ≥ 2^j b_0` (`seqB_ge`), `a_{j+1} ≥ a_j^4`;
* the widths are admissible: `3 ≤ H_j`, `2 ≤ H_j a_j`, `eH_j ≤ e^{a_j}` (`seqH_props`).
-/

open Finset

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- `b_j`: `b_0 = L/2`, `b_{j+1} = 4b_j⁴`. -/
def seqB (L : ℝ) : ℕ → ℝ
  | 0 => L / 2
  | j + 1 => 4 * seqB L j ^ 4

/-- `a_j`: `a_0 = 200 log L`, `a_{j+1} = 2b_j²`. -/
def seqA (L : ℝ) : ℕ → ℝ
  | 0 => 200 * Real.log L
  | j + 1 => 2 * seqB L j ^ 2

/-- `H_j`: `H_0 = L^{25}`, `H_{j+1} = a_{j+1}^8`. -/
def seqH (L : ℝ) : ℕ → ℝ
  | 0 => L ^ 25
  | j + 1 => seqA L (j + 1) ^ 8

theorem seqB_succ_eq (L : ℝ) (j : ℕ) : seqB L (j + 1) = seqA L (j + 1) ^ 2 := by
  simp only [seqB, seqA]; ring

/-- `b_j ≥ 2^j b_0` once `b_0 ≥ 1`. -/
theorem seqB_ge {L : ℝ} (hL : 2 ≤ L) (j : ℕ) : 2 ^ j * (L / 2) ≤ seqB L j := by
  induction j with
  | zero => simp [seqB]
  | succ j ih =>
    have hb1 : 1 ≤ seqB L j := le_trans (by
      have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      nlinarith) ih
    simp only [seqB, pow_succ]
    have h1 : seqB L j ≤ seqB L j ^ 4 := by
      calc seqB L j = seqB L j ^ 1 := (pow_one _).symm
        _ ≤ seqB L j ^ 4 := pow_le_pow_right₀ hb1 (by norm_num)
    nlinarith

theorem one_le_seqB {L : ℝ} (hL : 2 ≤ L) (j : ℕ) : 1 ≤ seqB L j := by
  have h := seqB_ge hL j
  have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  nlinarith

/-- `200 log L + 1 ≤ L/2` for `L ≥ 2^{20}`, so `a_0 + 1 ≤ b_0`. -/
theorem log_le_div_of_large {L : ℝ} (hL : 2 ^ 20 ≤ L) : 200 * Real.log L + 1 ≤ L / 2 := by
  have hL0 : 0 < L := by linarith
  have h1 : Real.log L ≤ L ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div hL0.le (by norm_num)
  rw [← Real.sqrt_eq_rpow] at h1
  have h1' : Real.log L ≤ 2 * Real.sqrt L := by
    have : Real.sqrt L / (1 / 2) = 2 * Real.sqrt L := by ring
    linarith
  have hs : (2 : ℝ) ^ 10 ≤ Real.sqrt L := by
    rw [show (2 : ℝ) ^ 10 = Real.sqrt ((2 ^ 10) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hsL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  have h2 : 400 * Real.sqrt L + 1 ≤ L / 2 := by nlinarith
  linarith

theorem seqA_add_one_le_seqB {L : ℝ} (hL : 2 ^ 20 ≤ L) (j : ℕ) : seqA L j + 1 ≤ seqB L j := by
  cases j with
  | zero => simp only [seqA, seqB]; exact log_le_div_of_large hL
  | succ j =>
    rw [seqB_succ_eq]
    have hb := one_le_seqB (by linarith : (2 : ℝ) ≤ L) j
    have ha : 2 ≤ seqA L (j + 1) := by simp only [seqA]; nlinarith
    nlinarith

theorem seqB_lt_seqA_succ {L : ℝ} (hL : 2 ≤ L) (j : ℕ) : seqB L j < seqA L (j + 1) := by
  have hb := one_le_seqB hL j
  simp only [seqA]
  nlinarith

theorem one_le_seqA {L : ℝ} (hL : 2 ^ 20 ≤ L) (j : ℕ) : 1 ≤ seqA L j := by
  cases j with
  | zero =>
    simp only [seqA]
    have : 1 ≤ Real.log L := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith [Real.exp_one_lt_d9]
    linarith
  | succ j =>
    have hb := one_le_seqB (by linarith : (2 : ℝ) ≤ L) j
    simp only [seqA]; nlinarith

/-- `a ≥ 2^{12}` gives `e · a^8 ≤ e^a`. -/
theorem exp_mul_pow_eight_le {a : ℝ} (ha : 2 ^ 12 ≤ a) : Real.exp 1 * a ^ 8 ≤ Real.exp a := by
  have ha0 : 0 < a := by linarith
  have h1 : Real.log a ≤ a ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div ha0.le (by norm_num)
  rw [← Real.sqrt_eq_rpow] at h1
  have hs : (2 : ℝ) ^ 6 ≤ Real.sqrt a := by
    rw [show (2 : ℝ) ^ 6 = Real.sqrt ((2 ^ 6) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hsa : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
  have hlog : 1 + 8 * Real.log a ≤ a := by nlinarith
  calc Real.exp 1 * a ^ 8 = Real.exp (1 + 8 * Real.log a) := by
        rw [Real.exp_add, show (8 : ℝ) * Real.log a = ((8 : ℕ) : ℝ) * Real.log a by norm_num,
          Real.exp_nat_mul, Real.exp_log ha0]
    _ ≤ Real.exp a := Real.exp_le_exp.mpr hlog

end

end GaloisForLFunctions.MatomakiRadziwill
