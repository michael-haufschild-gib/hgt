import GaloisForLFunctions.RHTower.StretchedBoseSeparator

/-!
# A polynomial lower reserve on the natural Gamma line

The quarter-line exponential lower bound and two Gamma recurrences retain
two frequency powers after squaring. This elementary reserve suffices to
pay the normalized errors of fixed radial prefixes.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms

/-- The positive constant retained by two quarter-line Gamma recurrences. -/
def gammaQuarterReserve : ℝ := Real.Gamma (1 / 4) ^ 2 / 25

theorem gammaQuarterReserve_pos : 0 < gammaQuarterReserve := by
  unfold gammaQuarterReserve
  exact div_pos (sq_pos_of_pos (Real.Gamma_pos_of_pos (by norm_num))) (by norm_num)

/-- Two Gamma recurrences retain a linear frequency reserve before squaring. -/
theorem norm_Gamma_nine_quarters_ge {τ : ℝ} (hτ : 1 ≤ τ) :
    Real.Gamma (1 / 4) / 5 * τ * Real.exp (-(Real.pi / 2 * τ)) ≤
      ‖Complex.Gamma ((9 / 4 : ℂ) + (τ : ℂ) * I)‖ := by
  have hτ0 : 0 ≤ τ := by linarith only [hτ]
  have hG : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hz1 : (1 / 4 : ℂ) + (τ : ℂ) * I ≠ 0 := by
    intro hz
    have hh := congrArg Complex.re hz
    norm_num at hh
  have hz5 : (5 / 4 : ℂ) + (τ : ℂ) * I ≠ 0 := by
    intro hz
    have hh := congrArg Complex.re hz
    norm_num at hh
  have h1 := Complex.Gamma_add_one ((1 / 4 : ℂ) + (τ : ℂ) * I) hz1
  have h5 := Complex.Gamma_add_one ((5 / 4 : ℂ) + (τ : ℂ) * I) hz5
  rw [show (1 / 4 : ℂ) + (τ : ℂ) * I + 1 = (5 / 4 : ℂ) + (τ : ℂ) * I by ring] at h1
  rw [show (5 / 4 : ℂ) + (τ : ℂ) * I + 1 = (9 / 4 : ℂ) + (τ : ℂ) * I by ring] at h5
  have hτ1 : τ ≤ ‖(1 / 4 : ℂ) + (τ : ℂ) * I‖ := by
    simpa [abs_of_nonneg hτ0] using Complex.abs_im_le_norm ((1 / 4 : ℂ) + (τ : ℂ) * I)
  have hτ5 : τ ≤ ‖(5 / 4 : ℂ) + (τ : ℂ) * I‖ := by
    simpa [abs_of_nonneg hτ0] using Complex.abs_im_le_norm ((5 / 4 : ℂ) + (τ : ℂ) * I)
  have hstep : τ ^ 2 * ‖Complex.Gamma ((1 / 4 : ℂ) + (τ : ℂ) * I)‖ ≤
      ‖Complex.Gamma ((9 / 4 : ℂ) + (τ : ℂ) * I)‖ := by
    rw [h5, h1, norm_mul, norm_mul]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul hτ5 hτ1 hτ0 (norm_nonneg _))
      (norm_nonneg (Complex.Gamma ((1 / 4 : ℂ) + (τ : ℂ) * I)))
    nlinarith only [hh]
  have hbase := _root_.RHTower.StretchedBose.norm_Gamma_ge
    (x := (1 / 4 : ℝ)) (by norm_num) τ
  rw [abs_of_nonneg hτ0, show 1 + τ / (1 / 4 : ℝ) = 1 + 4 * τ by ring] at hbase
  refine le_trans ?_ ((mul_le_mul_of_nonneg_left hbase (sq_nonneg τ)).trans hstep)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < 1 + 4 * τ)).mpr
  calc
    _ = (Real.Gamma (1 / 4) * Real.exp (-(Real.pi / 2 * τ)) * τ / 5) * (1 + 4 * τ) := by ring
    _ ≤ (Real.Gamma (1 / 4) * Real.exp (-(Real.pi / 2 * τ)) * τ / 5) * (5 * τ) :=
      mul_le_mul_of_nonneg_left (by linarith only [hτ]) (by positivity)
    _ = _ := by ring

/-- The natural Gamma modulus pays a quadratic frequency reserve on its exact exponential scale. -/
theorem gammaQuarterReserve_mul_sq_exp_le {τ : ℝ} (hτ : 1 ≤ τ) :
    gammaQuarterReserve * τ ^ 2 * Real.exp (-Real.pi * τ) ≤
      ‖Complex.Gamma ((9 / 4 : ℂ) + (τ : ℂ) * I)‖ ^ 2 := by
  have hG : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hτ0 : 0 ≤ τ := by linarith only [hτ]
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤
    Real.Gamma (1 / 4) / 5 * τ * Real.exp (-(Real.pi / 2 * τ)))
    (norm_Gamma_nine_quarters_ge hτ) 2
  have he : Real.exp (-(Real.pi / 2 * τ)) ^ 2 = Real.exp (-Real.pi * τ) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, mul_pow, div_pow, he] at hh
  norm_num only [show (5 : ℝ) ^ 2 = 25 by norm_num] at hh
  exact hh

#print axioms gammaQuarterReserve_mul_sq_exp_le

end GaloisForLFunctions.CompletedArithmeticForms
