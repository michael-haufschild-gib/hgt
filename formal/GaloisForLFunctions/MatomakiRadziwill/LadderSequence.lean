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

theorem log_ge_twelve {L : ℝ} (hL : 2 ^ 20 ≤ L) : 12 ≤ Real.log L := by
  have hL0 : 0 < L := by linarith
  rw [Real.le_log_iff_exp_le hL0]
  have h1 : Real.exp 12 = Real.exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp 1 ^ 12 ≤ 3 ^ 12 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) 12
  have h3 : (3 : ℝ) ^ 12 ≤ 2 ^ 20 := by norm_num
  linarith

/-- `a_{j+1} ≥ L²/2`. -/
theorem seqA_succ_ge {L : ℝ} (hL : 2 ≤ L) (j : ℕ) : L ^ 2 / 2 ≤ seqA L (j + 1) := by
  have h := seqB_ge hL j
  have hj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hb : L / 2 ≤ seqB L j := le_trans (by nlinarith) h
  simp only [seqA]
  nlinarith

/-- **The widths are admissible.** -/
theorem seqH_props {L : ℝ} (hL : 2 ^ 20 ≤ L) (j : ℕ) :
    3 ≤ seqH L j ∧ 2 ≤ seqH L j * seqA L j ∧ Real.exp 1 * seqH L j ≤ Real.exp (seqA L j) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  cases j with
  | zero =>
    have hlog := log_ge_twelve hL
    simp only [seqH, seqA]
    have hL25 : (2 : ℝ) ^ 20 ≤ L ^ 25 := le_trans hL (by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 25 := pow_le_pow_right₀ hL1 (by norm_num))
    refine ⟨by linarith, by nlinarith, ?_⟩
    rw [show (200 : ℝ) * Real.log L = ((200 : ℕ) : ℝ) * Real.log L by norm_num, Real.exp_nat_mul,
      Real.exp_log hL0]
    have hL175 : L ≤ L ^ 175 := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 175 := pow_le_pow_right₀ hL1 (by norm_num)
    have he3 : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
    have he : Real.exp 1 ≤ L ^ 175 := by linarith
    calc Real.exp 1 * L ^ 25 ≤ L ^ 175 * L ^ 25 :=
          mul_le_mul_of_nonneg_right he (by positivity)
      _ = L ^ 200 := by ring
  | succ j =>
    have ha := seqA_succ_ge (by linarith : (2 : ℝ) ≤ L) j
    have ha12 : (2 : ℝ) ^ 12 ≤ seqA L (j + 1) := le_trans (by nlinarith) ha
    simp only [seqH]
    set a := seqA L (j + 1) with hadef
    have ha1 : 1 ≤ a := by linarith
    have h8 : a ≤ a ^ 8 := by
      calc a = a ^ 1 := (pow_one a).symm
        _ ≤ a ^ 8 := pow_le_pow_right₀ ha1 (by norm_num)
    exact ⟨by linarith, by nlinarith, exp_mul_pow_eight_le ha12⟩

/-- **The moment-step condition between scales `j` and `j+1`.** -/
theorem seq_step_condition {L : ℝ} (hL : 2 ^ 20 ≤ L) (j : ℕ) :
    18 * Real.exp 1 * (seqB L (j + 1) / (seqA L j - 1 / seqH L j) + 1) ≤ seqH L j := by
  have hL0 : 0 < L := by linarith
  have he : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  obtain ⟨hH3, -, -⟩ := seqH_props hL j
  have hHinv : 1 / seqH L j ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hH3
  cases j with
  | zero =>
    have hlog := log_ge_twelve hL
    simp only [seqB, seqA, seqH] at hHinv ⊢
    have hden : 1 ≤ 200 * Real.log L - 1 / L ^ 25 := by linarith
    have hratio : 4 * (L / 2) ^ 4 / (200 * Real.log L - 1 / L ^ 25) ≤ 4 * (L / 2) ^ 4 := by
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ 4 * (L / 2) ^ 4 := by positivity
      nlinarith
    have hL4 : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ (by linarith)
    have hL21 : (2 : ℝ) ^ 20 ≤ L ^ 21 := le_trans hL (by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 21 := pow_le_pow_right₀ (by linarith) (by norm_num))
    have h25 : L ^ 25 = L ^ 21 * L ^ 4 := by ring
    have hsimp : 4 * (L / 2) ^ 4 = L ^ 4 / 4 := by ring
    rw [hsimp] at hratio ⊢
    have hr0 : 0 ≤ L ^ 4 / 4 / (200 * Real.log L - 1 / L ^ 25) := by
      have : 0 < 200 * Real.log L - 1 / L ^ 25 := by linarith
      positivity
    calc 18 * Real.exp 1 * (L ^ 4 / 4 / (200 * Real.log L - 1 / L ^ 25) + 1)
        ≤ 18 * 3 * (L ^ 4 / 4 + 1) :=
          mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
      _ ≤ 2 ^ 20 * L ^ 4 := by nlinarith
      _ ≤ L ^ 21 * L ^ 4 := mul_le_mul_of_nonneg_right hL21 (by positivity)
      _ = L ^ 25 := h25.symm
  | succ j =>
    have ha := seqA_succ_ge (by linarith : (2 : ℝ) ≤ L) j
    have hb : seqB L (j + 1 + 1) = 4 * seqA L (j + 1) ^ 8 := by
      rw [seqB, seqB_succ_eq]; ring
    simp only [seqH] at hHinv ⊢
    rw [hb]
    set a := seqA L (j + 1) with hadef
    have ha441 : (441 : ℝ) ≤ a := le_trans (by nlinarith) ha
    have ha1 : 1 ≤ a := by linarith
    have ha8 : a ≤ a ^ 8 := by
      calc a = a ^ 1 := (pow_one a).symm
        _ ≤ a ^ 8 := pow_le_pow_right₀ ha1 (by norm_num)
    have hinv : 1 / a ^ 8 ≤ a / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hden : a / 2 ≤ a - 1 / a ^ 8 := by linarith
    have hratio : 4 * a ^ 8 / (a - 1 / a ^ 8) ≤ 8 * a ^ 7 := by
      rw [div_le_iff₀ (by linarith)]
      have h7 : 0 ≤ a ^ 7 := by positivity
      nlinarith
    have h87 : a ^ 8 = a * a ^ 7 := by ring
    have h7 : 1 ≤ a ^ 7 := one_le_pow₀ ha1
    have hr0 : 0 ≤ 4 * a ^ 8 / (a - 1 / a ^ 8) := by
      have : 0 < a - 1 / a ^ 8 := by linarith
      positivity
    calc 18 * Real.exp 1 * (4 * a ^ 8 / (a - 1 / a ^ 8) + 1)
        ≤ 18 * 3 * (8 * a ^ 7 + 1) :=
          mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
      _ ≤ 441 * a ^ 7 := by
          have h7' : a ≤ a ^ 7 := by
            calc a = a ^ 1 := (pow_one a).symm
              _ ≤ a ^ 7 := pow_le_pow_right₀ ha1 (by norm_num)
          linarith
      _ ≤ a * a ^ 7 := mul_le_mul_of_nonneg_right ha441 (by positivity)
      _ = a ^ 8 := h87.symm

end

end GaloisForLFunctions.MatomakiRadziwill
