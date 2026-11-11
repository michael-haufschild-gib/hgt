import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheLinearDetectorHasSmallTaperError

/-!
# Keeping one linear mollifier across the gate strip

Changing displacement from `d₀` to `d` multiplies the matched coefficient
by `exp((d−d₀) log n)`. If `(d−d₀) log N ≤ D`, the fixed coefficients
have envelope `exp D · n⁻ᵈ` and their difference from the matched ones
has envelope `D exp D · n⁻ᵈ`. These bounds retain a single coefficient
family while the strip position varies.
-/

open Complex
open RHTower

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The exact coefficient change under displacement, before taking absolute values. -/
theorem linearDetectorWeights_change_displacement (N : ℕ) {n : ℕ} (hn : 1 ≤ n)
    (d₀ d : ℝ) :
    linearDetectorWeights N d₀ n =
      Real.exp ((d - d₀) * Real.log n) * linearDetectorWeights N d n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (n : ℝ) ^ (1 / 2 - d₀) =
      Real.exp ((d - d₀) * Real.log n) * (n : ℝ) ^ (1 / 2 - d) := by
    rw [Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0, ← Real.exp_add]
    congr 1
    ring
  unfold linearDetectorWeights levinsonShiftedLinearMollifierCoeff
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hp]
  ring

private theorem exp_sub_one_le_self_mul_exp {x : ℝ} (hx : 0 ≤ x) :
    |Real.exp x - 1| ≤ x * Real.exp x := by
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add] at hh
  simp only [add_neg_cancel, Real.exp_zero] at hh
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hx))]
  nlinarith only [hh]

/-- Uniform envelopes for the fixed mollifier and its discrepancy from the matched mollifier. -/
theorem linearDetectorWeights_fixed_envelopes {N : ℕ} (hN : 1 < N)
    {d₀ d D : ℝ} (hd : d₀ ≤ d) (hD : (d - d₀) * Real.log N ≤ D) :
    ∀ n ∈ Finset.Icc 1 N,
      |linearDetectorWeights N d₀ n| ≤ Real.exp D * (n : ℝ) ^ (-d) ∧
      |linearDetectorWeights N d₀ n - linearDetectorWeights N d n| ≤
        (D * Real.exp D) * (n : ℝ) ^ (-d) := by
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hlog : Real.log n ≤ Real.log N := Real.log_le_log hn0
    (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
  have hx0 : 0 ≤ (d - d₀) * Real.log n :=
    mul_nonneg (sub_nonneg.mpr hd) (Real.log_nonneg hn1)
  have hxD : (d - d₀) * Real.log n ≤ D :=
    (mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr hd)).trans hD
  have he := Real.exp_le_exp.mpr hxD
  have hw := abs_linearDetectorWeights_le hN d (Finset.mem_Icc.mp hn).1
  constructor
  · rw [linearDetectorWeights_change_displacement N (Finset.mem_Icc.mp hn).1 d₀ d,
      abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul he hw (abs_nonneg _) (Real.exp_pos D).le
  · have hid : linearDetectorWeights N d₀ n - linearDetectorWeights N d n =
        (Real.exp ((d - d₀) * Real.log n) - 1) * linearDetectorWeights N d n := by
      rw [linearDetectorWeights_change_displacement N (Finset.mem_Icc.mp hn).1 d₀ d]
      ring
    have hf : |Real.exp ((d - d₀) * Real.log n) - 1| ≤ D * Real.exp D :=
      (exp_sub_one_le_self_mul_exp hx0).trans
        (mul_le_mul hxD he (Real.exp_pos _).le (hx0.trans hxD))
    rw [hid, abs_mul]
    exact mul_le_mul hf hw (abs_nonneg _) (mul_nonneg (hx0.trans hxD) (Real.exp_pos D).le)


/-- The full gate strip changes the normalized coefficient exponent by at most `R/(U−1)`. -/
theorem levinsonGate_coefficient_shift_width {U R d : ℝ} {N : ℕ}
    (hU : 2 < U) (hlog : 1 ≤ Real.log (U - 1)) (hR : 0 ≤ R)
    (hN : 1 < N) (hNU : (N : ℝ) ≤ U)
    (hlo : R ≤ d * Real.log U) (hhi : d * Real.log (U - 1) ≤ R) :
    R / Real.log U ≤ d ∧
      (d - R / Real.log U) * Real.log N ≤ R / (U - 1) := by
  have hUm : 0 < U - 1 := by linarith only [hU]
  have hU0 : 0 < U := by linarith only [hU]
  have hLU : 0 < Real.log U := Real.log_pos (by linarith only [hU])
  have hd₀ : R / Real.log U ≤ d := (div_le_iff₀ hLU).mpr hlo
  have hd : 0 ≤ d := (div_nonneg hR hLU.le).trans hd₀
  have hdR : d ≤ R := by
    have hh := mul_le_mul_of_nonneg_left hlog hd
    simp only [mul_one] at hh
    exact hh.trans hhi
  have hinc : Real.log U - Real.log (U - 1) ≤ 1 / (U - 1) := by
    have hh := Real.log_le_sub_one_of_pos (div_pos hU0 hUm)
    rw [Real.log_div hU0.ne' hUm.ne'] at hh
    have he : U / (U - 1) - 1 = 1 / (U - 1) := by field_simp [hUm.ne'] <;> ring
    exact hh.trans_eq he
  have hNL : Real.log (N : ℝ) ≤ Real.log U :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) hNU
  refine ⟨hd₀, ?_⟩
  calc
    _ ≤ (d - R / Real.log U) * Real.log U :=
      mul_le_mul_of_nonneg_left hNL (sub_nonneg.mpr hd₀)
    _ = d * Real.log U - R := by field_simp [hLU.ne'] <;> ring
    _ ≤ d * (Real.log U - Real.log (U - 1)) := by nlinarith only [hhi]
    _ ≤ d * (1 / (U - 1)) := mul_le_mul_of_nonneg_left hinc hd
    _ = d / (U - 1) := by ring
    _ ≤ R / (U - 1) := div_le_div_of_nonneg_right hdR hUm.le

end GaloisForLFunctions.MultiscaleMollifiedZetaField
