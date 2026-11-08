import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanLineBounds
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.ExponentialMellinTail

/-!
# Exponentially small tails of the averaged Narain boundary

The Fourier phase has unit norm. Polynomial absorption therefore gives one
exponential truncation bound at every logarithmic frequency.
-/

open Complex RHTower Filter MeasureTheory
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The Fourier weight has unit norm on the boundary, so all logarithmic frequencies
share one integrable boundary majorant. -/
theorem integrable_narainMeanBoundary (Y Z : Height) (L : ℝ) :
    Integrable (fun t : ℝ => Complex.exp ((L : ℂ) * ((t : ℂ) * I)) *
      narainMellinMean Y Z ((t : ℂ) * I)) := by
  have hc : Continuous (fun t : ℝ => Complex.exp ((L : ℂ) * ((t : ℂ) * I))) := by fun_prop
  have hm : Continuous (fun t : ℝ => narainMellinMean Y Z ((t : ℂ) * I)) := by
    simpa using continuous_narainMellinMean_vertical Y Z (a := 0) le_rfl (by norm_num)
  apply (integrable_narainMellinMean_boundary Y Z).norm.mono' (hc.mul hm).aestronglyMeasurable
  filter_upwards [] with t
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- The actual boundary Mellin integral has exponentially small discarded tails,
uniformly in the logarithmic frequency. -/
theorem exists_narainMeanBoundary_tail_bound (Y Z : Height) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L T : ℝ, 1 ≤ T →
      ‖(∫ t : ℝ, Complex.exp ((L : ℂ) * ((t : ℂ) * I)) * narainMellinMean Y Z ((t : ℂ) * I)) -
        ∫ t : ℝ in (-T)..T, Complex.exp ((L : ℂ) * ((t : ℂ) * I)) *
          narainMellinMean Y Z ((t : ℂ) * I)‖ ≤
            C * Real.exp (-(Real.pi * T / 4)) := by
  obtain ⟨C, N, hC, hb⟩ := exists_narainMellinMean_boundary_bound Y Z
  let D : ℝ := (Nat.factorial N : ℝ) / (Real.pi / 4) ^ N * Real.exp (Real.pi / 4)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨2 * (C * D) / (Real.pi / 4), by positivity, ?_⟩
  intro L T hT
  have h := norm_integral_sub_truncated_le (integrable_narainMeanBoundary Y Z L)
    (show 0 ≤ T by linarith only [hT]) (show 0 < Real.pi / 4 by positivity)
    (C := C * D) (fun t ht => by
      have ht1 : 1 ≤ |t| := hT.trans ht
      have hp := _root_.HTGeometry.one_add_pow_le_const_mul_exp (abs_nonneg t)
        (show 0 < Real.pi / 4 by positivity) N
      change (1 + |t|) ^ N ≤ D * Real.exp (Real.pi / 4 * |t|) at hp
      have he : Real.exp (Real.pi / 4 * |t|) * Real.exp (-(Real.pi * |t| / 2)) =
          Real.exp (-(Real.pi / 4 * |t|)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hw : ‖Complex.exp ((L : ℂ) * ((t : ℂ) * I))‖ = 1 := by
        simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
      rw [norm_mul, hw, one_mul]
      calc
        _ ≤ C * (1 + |t|) ^ N * Real.exp (-(Real.pi * |t| / 2)) := hb t ht1
        _ ≤ C * (D * Real.exp (Real.pi / 4 * |t|)) * Real.exp (-(Real.pi * |t| / 2)) := by gcongr
        _ = C * D * (Real.exp (Real.pi / 4 * |t|) * Real.exp (-(Real.pi * |t| / 2))) := by ring
        _ = _ := by rw [he])
  simpa only [div_mul_eq_mul_div] using h

#print axioms integrable_narainMeanBoundary
#print axioms exists_narainMeanBoundary_tail_bound
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
