import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualBorelBessel
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualBorelCarrier
import GaloisForLFunctions.RHTower.SquaredXiChebyshevWindow
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

private def secondFactorialBorelLaplaceTerm (w : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  (w ^ k / ((k.factorial : ℂ) ^ (2 : ℕ))) *
    ((t ^ k * Real.exp (-t) : ℝ) : ℂ)

private theorem integral_ofReal_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Integrable f μ) :
    (∫ x, ((f x : ℝ) : ℂ) ∂μ) = ((∫ x, f x ∂μ : ℝ) : ℂ) := by
  rw [← Complex.ofRealCLM_apply,
    ← ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hf]
  rfl

private theorem integrableOn_secondFactorialBorelLaplaceTerm (w : ℂ) (k : ℕ) :
    IntegrableOn (secondFactorialBorelLaplaceTerm w k) (Ioi 0) := by
  have hreal := integrableOn_pow_mul_exp_neg_mul_Ioi (r := 1) (by norm_num) k
  have hreal' : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-t)) (Ioi 0) := by
    convert hreal using 1
    funext t
    congr 2
    ring
  apply MeasureTheory.IntegrableOn.congr_fun
    (hreal'.ofReal.const_mul (w ^ k / ((k.factorial : ℂ) ^ (2 : ℕ))))
  intro t ht
  rfl
  exact measurableSet_Ioi

private theorem integral_secondFactorialBorelLaplaceTerm (w : ℂ) (k : ℕ) :
    (∫ t : ℝ in Ioi 0, secondFactorialBorelLaplaceTerm w k t) =
      w ^ k / (k.factorial : ℂ) := by
  have hreal := integrableOn_pow_mul_exp_neg_mul_Ioi (r := 1) (by norm_num) k
  have hreal' : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-t)) (Ioi 0) := by
    convert hreal using 1
    funext t
    congr 2
    ring
  change (∫ t : ℝ in Ioi 0,
    (w ^ k / ((k.factorial : ℂ) ^ (2 : ℕ))) *
      ((t ^ k * Real.exp (-t) : ℝ) : ℂ)) = _
  rw [integral_const_mul]
  rw [show (∫ t : ℝ in Ioi 0, ((t ^ k * Real.exp (-t) : ℝ) : ℂ)) =
      (((∫ t : ℝ in Ioi 0, t ^ k * Real.exp (-t)) : ℝ) : ℂ) by
    exact integral_ofReal_eq hreal']
  rw [show (∫ t : ℝ in Ioi 0, t ^ k * Real.exp (-t)) =
    (k.factorial : ℝ) by
      simpa using integral_pow_mul_exp_neg_mul_Ioi (r := 1) (by norm_num) k]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp
  norm_num

private theorem integral_norm_secondFactorialBorelLaplaceTerm (w : ℂ) (k : ℕ) :
    (∫ t : ℝ in Ioi 0, ‖secondFactorialBorelLaplaceTerm w k t‖) =
      ‖w‖ ^ k / (k.factorial : ℝ) := by
  have hmoment := integral_pow_mul_exp_neg_mul_Ioi (r := 1) (by norm_num) k
  calc
    (∫ t : ℝ in Ioi 0, ‖secondFactorialBorelLaplaceTerm w k t‖) =
        ∫ t : ℝ in Ioi 0,
          (‖w‖ ^ k / (k.factorial : ℝ) ^ (2 : ℕ)) *
            (t ^ k * Real.exp (-t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 ≤ t := le_of_lt ht
      change ‖(w ^ k / ((k.factorial : ℂ) ^ (2 : ℕ))) *
        ((t ^ k * Real.exp (-t) : ℝ) : ℂ)‖ = _
      rw [norm_mul, norm_div, norm_pow,
        norm_pow, Complex.norm_natCast, Complex.norm_real]
      simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg ht0 k)
        (Real.exp_pos _).le)]
    _ = (‖w‖ ^ k / (k.factorial : ℝ) ^ (2 : ℕ)) *
          (∫ t : ℝ in Ioi 0, t ^ k * Real.exp (-t)) := by
      rw [integral_const_mul]
    _ = ‖w‖ ^ k / (k.factorial : ℝ) := by
      rw [show (∫ t : ℝ in Ioi 0, t ^ k * Real.exp (-t)) =
        (k.factorial : ℝ) by simpa using hmoment]
      have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
      field_simp

private theorem summable_integral_norm_secondFactorialBorelLaplaceTerm (w : ℂ) :
    Summable (fun k : ℕ =>
      ∫ t : ℝ in Ioi 0, ‖secondFactorialBorelLaplaceTerm w k t‖) := by
  apply Summable.congr
      ((NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) ‖w‖).summable)
  intro k
  rw [integral_norm_secondFactorialBorelLaplaceTerm]

private theorem tsum_secondFactorialBorelLaplaceTerm (w : ℂ) (t : ℝ) :
    (∑' k : ℕ, secondFactorialBorelLaplaceTerm w k t) =
      ((Real.exp (-t) : ℝ) : ℂ) * secondFactorialBorelKernel (w * t) := by
  rw [secondFactorialBorelKernel, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [secondFactorialBorelLaplaceTerm]
  push_cast
  rw [mul_pow]
  ring

theorem integrableOn_exp_neg_mul_secondFactorialBorelKernel (w : ℂ) :
    IntegrableOn (fun t : ℝ =>
      ((Real.exp (-t) : ℝ) : ℂ) * secondFactorialBorelKernel (w * t))
      (Ioi 0) := by
  rw [← funext (tsum_secondFactorialBorelLaplaceTerm w)]
  exact GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (fun k => integrableOn_secondFactorialBorelLaplaceTerm w k)
    (summable_integral_norm_secondFactorialBorelLaplaceTerm w)

theorem integral_secondFactorialBorelKernel_eq_exp (w : ℂ) :
    (∫ t : ℝ in Ioi 0,
      ((Real.exp (-t) : ℝ) : ℂ) * secondFactorialBorelKernel (w * t)) =
      Complex.exp w := by
  rw [← funext (tsum_secondFactorialBorelLaplaceTerm w)]
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun k => integrableOn_secondFactorialBorelLaplaceTerm w k)
    (summable_integral_norm_secondFactorialBorelLaplaceTerm w)]
  rw [Complex.exp_eq_exp_ℂ]
  rw [← (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) w).tsum_eq]
  apply tsum_congr
  exact integral_secondFactorialBorelLaplaceTerm w

end

end RHTower
