import GaloisForLFunctions.RHTower.ExpDecayFourierAnalytic

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Mathlib's real Fourier transform equals `expFourier` after the standard `2π` rescaling. -/
theorem fourier_eq_expFourier_two_pi (f : ℝ → ℂ) (w : ℝ) :
    FourierTransform.fourier f w = expFourier f ((2 * Real.pi * w : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [expFourier]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [smul_eq_mul]
  rw [mul_comm]
  congr 1
  push_cast
  ring_nf

end

end RHTower
