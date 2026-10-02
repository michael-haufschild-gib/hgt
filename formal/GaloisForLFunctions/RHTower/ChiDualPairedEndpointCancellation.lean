import GaloisForLFunctions.RHTower.ChiDualSignedIntegrationByParts
import GaloisForLFunctions.RHTower.ZetaChiDualIntegerBlockPoisson

open Complex Set Filter Topology MeasureTheory
noncomputable section
namespace RHTower


/-- The two spatial Fourier phases agree exactly at every half-integer endpoint. -/
theorem chiDual_spatial_phase_half_integer (v : ℝ) (z k : ℤ) :
    Complex.exp (I * ((v + 2 * Real.pi * k * ((z : ℝ) + 1 / 2) : ℝ) : ℂ)) =
      Complex.exp (I * ((v - 2 * Real.pi * k * ((z : ℝ) + 1 / 2) : ℝ) : ℂ)) := by
  have he : I * ((v + 2 * Real.pi * k * ((z : ℝ) + 1 / 2) : ℝ) : ℂ) =
      I * ((v - 2 * Real.pi * k * ((z : ℝ) + 1 / 2) : ℝ) : ℂ) +
        ((k * (2 * z + 1) : ℤ) : ℂ) * (2 * Real.pi * I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Opposite spatial endpoint denominators cancel their leading reciprocal frequency. -/
theorem chiDual_paired_inverse_frequency (v : ℂ) {lam ω : ℝ}
    (hp : lam + ω ≠ 0) (hm : lam - ω ≠ 0) :
    v / (I * ((lam + ω : ℝ) : ℂ)) + v / (I * ((lam - ω : ℝ) : ℂ)) =
      (v / I) * (((2 * lam / (lam ^ 2 - ω ^ 2) : ℝ)) : ℂ) := by
  have hd : lam ^ 2 - ω ^ 2 ≠ 0 := by
    rw [show lam ^ 2 - ω ^ 2 = (lam + ω) * (lam - ω) by ring]
    exact mul_ne_zero hp hm
  have hpC : (lam : ℂ) + ω ≠ 0 := by exact_mod_cast hp
  have hmC : (lam : ℂ) - ω ≠ 0 := by exact_mod_cast hm
  have hdC : (lam : ℂ) ^ 2 - (ω : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp [hpC, hmC, hdC, I_ne_zero]
  ring

/-- On the actual bounded spatial phase-slope range, the complete paired
endpoint coefficient has summable k^-2 decay. -/
theorem norm_chiDual_paired_inverse_frequency_le (v : ℂ) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam11 : lam ≤ 11) {k : ℕ} (hk : 2 ≤ k) :
    ‖v / (I * ((lam + 2 * Real.pi * k : ℝ) : ℂ)) +
      v / (I * ((lam - 2 * Real.pi * k : ℝ) : ℂ))‖ ≤ 22 * ‖v‖ / (k : ℝ) ^ 2 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  let ω : ℝ := 2 * Real.pi * k
  have hω : 6 * (k : ℝ) ≤ ω := by
    dsimp [ω]
    exact mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) hk0.le
  have hp : 0 < lam + ω := by linarith
  have hm : lam - ω < 0 := by linarith
  have hω2 : 36 * (k : ℝ) ^ 2 ≤ ω ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 6 * k) hω 2
    nlinarith only [hh]
  have hlam2 : lam ^ 2 ≤ 121 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hlam11) (show 0 ≤ 11 + lam by linarith)]
  have hk2 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hkR, sq_nonneg ((k : ℝ) - 2)]
  have hden : (k : ℝ) ^ 2 ≤ ω ^ 2 - lam ^ 2 := by nlinarith only [hω2, hlam2, hk2]
  have hk2pos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hdenpos : 0 < ω ^ 2 - lam ^ 2 := lt_of_lt_of_le hk2pos hden
  have hfrac : 2 * lam / (ω ^ 2 - lam ^ 2) ≤ 22 / (k : ℝ) ^ 2 := by
    calc
      _ ≤ 22 / (ω ^ 2 - lam ^ 2) := by gcongr; linarith
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hk2pos hden
  change ‖v / (I * ((lam + ω : ℝ) : ℂ)) + v / (I * ((lam - ω : ℝ) : ℂ))‖ ≤ _
  rw [chiDual_paired_inverse_frequency v hp.ne' (ne_of_lt hm), norm_mul, norm_div,
    Complex.norm_I, div_one, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (by positivity : 0 ≤ 2 * lam), abs_of_neg (by linarith : lam ^ 2 - ω ^ 2 < 0)]
  rw [show -(lam ^ 2 - ω ^ 2) = ω ^ 2 - lam ^ 2 by ring]
  calc
    _ ≤ ‖v‖ * (22 / (k : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hfrac (norm_nonneg _)
    _ = _ := by ring

end RHTower
