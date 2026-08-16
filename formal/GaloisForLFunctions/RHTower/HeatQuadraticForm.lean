import GaloisForLFunctions.RHTower.HeatMultiplierFourier
import GaloisForLFunctions.RHTower.HeatMomentAsymptotic

/-!
# The heat quadratic form of a trigonometric polynomial

Testing the heat multiplier against `|P|²` for a trigonometric polynomial `P` reproduces exactly
the additive-heat double sum of its coefficients.  This is the finite form of the Fourier
representation `(2)` of the additive heat aperture energy.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

theorem conj_exp_I_mul_real (m : ℤ) (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (I * (m : ℂ) * (θ : ℂ)))
      = Complex.exp (I * ((-m : ℤ) : ℂ) * (θ : ℂ)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, map_intCast, Complex.conj_ofReal]
  push_cast
  ring

/-- The multiplier against a single Fourier mode is integrable on the window. -/
theorem integrableOn_heatMultiplier_mul_exp {x : ℝ} (hx : 0 < x) (m : ℤ) :
    IntegrableOn (fun θ : ℝ => heatMultiplier x θ * Complex.exp (I * (m : ℂ) * (θ : ℂ)))
      (Ioc (-Real.pi) Real.pi) := by
  refine Continuous.integrableOn_Ioc ?_
  exact (continuous_heatMultiplier hx).mul (by fun_prop)

/-- **The heat quadratic form of a trigonometric polynomial.**  This is the finite form of the
Fourier representation `(2)`. -/
theorem integral_heatMultiplier_mul_trigPoly_normSq {x : ℝ} (hx : 0 < x) (s : Finset ℤ)
    (a : ℤ → ℂ) :
    (∫ θ in Ioc (-Real.pi) Real.pi,
        heatMultiplier x θ * ((∑ n ∈ s, a n * Complex.exp (I * (n : ℂ) * (θ : ℂ)))
          * (starRingEnd ℂ) (∑ n ∈ s, a n * Complex.exp (I * (n : ℂ) * (θ : ℂ)))))
      = 2 * Real.pi * ∑ n ∈ s, ∑ m ∈ s,
          a n * (starRingEnd ℂ) (a m) * ((heatCoeff x (n - m) : ℝ) : ℂ) := by
  have hexpand : ∀ θ : ℝ,
      heatMultiplier x θ * ((∑ n ∈ s, a n * Complex.exp (I * (n : ℂ) * (θ : ℂ)))
        * (starRingEnd ℂ) (∑ n ∈ s, a n * Complex.exp (I * (n : ℂ) * (θ : ℂ))))
      = ∑ n ∈ s, ∑ m ∈ s, (a n * (starRingEnd ℂ) (a m))
          * (heatMultiplier x θ * Complex.exp (I * ((n - m : ℤ) : ℂ) * (θ : ℂ))) := by
    intro θ
    rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, conj_exp_I_mul_real]
    have hmul : Complex.exp (I * (n : ℂ) * (θ : ℂ)) * Complex.exp (I * ((-m : ℤ) : ℂ) * (θ : ℂ))
        = Complex.exp (I * ((n - m : ℤ) : ℂ) * (θ : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc heatMultiplier x θ
        * (a n * Complex.exp (I * (n : ℂ) * (θ : ℂ))
            * ((starRingEnd ℂ) (a m) * Complex.exp (I * ((-m : ℤ) : ℂ) * (θ : ℂ))))
        = (a n * (starRingEnd ℂ) (a m))
            * (heatMultiplier x θ
              * (Complex.exp (I * (n : ℂ) * (θ : ℂ))
                  * Complex.exp (I * ((-m : ℤ) : ℂ) * (θ : ℂ)))) := by ring
      _ = (a n * (starRingEnd ℂ) (a m))
            * (heatMultiplier x θ * Complex.exp (I * ((n - m : ℤ) : ℂ) * (θ : ℂ))) := by
          rw [hmul]
  rw [setIntegral_congr_fun measurableSet_Ioc fun θ _ => hexpand θ,
    MeasureTheory.integral_finsetSum _ (fun n _ => MeasureTheory.integrable_finsetSum _
      fun m _ => ((integrableOn_heatMultiplier_mul_exp hx (n - m)).const_mul _)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun m _ =>
    ((integrableOn_heatMultiplier_mul_exp hx (n - m)).const_mul _)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MeasureTheory.integral_const_mul, integral_heatMultiplier_mul_exp hx]
  ring

end RHTower
