import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Quadratic Gaussian amplitudes and their imaginary-square defect

Taking the real part of a complex square subtracts twice its imaginary energy from
its norm energy.  The half-heat phase makes this identity exact for Gaussian
polynomial tests.  Its negative contribution is bounded quadratically in the
imaginary spectral displacement, without a sign assumption on the polynomial.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

def heatPhaseAmplitude (v : ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  v * Complex.exp (-((t / 2 : ℝ) : ℂ) * z)

theorem heatPhaseAmplitude_sq (v : ℂ) (t : ℝ) (z : ℂ) :
    heatPhaseAmplitude v t z ^ 2 = v ^ 2 * Complex.exp (-(t : ℂ) * z) := by
  rw [heatPhaseAmplitude, mul_pow]
  congr 1
  rw [pow_two, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem heatPhaseAmplitude_norm_sq (v : ℂ) (t : ℝ) (z : ℂ) :
    ‖heatPhaseAmplitude v t z‖ ^ 2 = ‖v‖ ^ 2 * Real.exp (-(t * z.re)) := by
  rw [heatPhaseAmplitude, norm_mul, mul_pow, Complex.norm_exp]
  congr 1
  rw [pow_two, ← Real.exp_add]
  congr 1
  simp [Complex.mul_re]
  ring

theorem heatPhaseAmplitude_im (v : ℂ) (t : ℝ) (z : ℂ) :
    (heatPhaseAmplitude v t z).im =
      Real.exp (-(t * z.re / 2)) *
        (v.im * Real.cos (t * z.im / 2) - v.re * Real.sin (t * z.im / 2)) := by
  have hre : (-((t / 2 : ℝ) : ℂ) * z).re = -(t * z.re / 2) := by
    simp [Complex.mul_re]
    ring
  have him : (-((t / 2 : ℝ) : ℂ) * z).im = -(t * z.im / 2) := by
    simp [Complex.mul_im]
    ring
  rw [heatPhaseAmplitude, Complex.mul_im, Complex.exp_re, Complex.exp_im,
    hre, him, Real.cos_neg, Real.sin_neg]
  ring

theorem heatPhaseAmplitude_real_square (v : ℂ) (t : ℝ) (z : ℂ) :
    (v ^ 2 * Complex.exp (-(t : ℂ) * z)).re =
      ‖heatPhaseAmplitude v t z‖ ^ 2 - 2 * (heatPhaseAmplitude v t z).im ^ 2 := by
  rw [← heatPhaseAmplitude_sq, Complex.sq_norm, Complex.normSq_apply,
    pow_two, Complex.mul_re]
  ring

theorem heatPhaseAmplitude_im_sq_le_norm_sq (v : ℂ) (t : ℝ) (z : ℂ) :
    (heatPhaseAmplitude v t z).im ^ 2 ≤ ‖heatPhaseAmplitude v t z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg (heatPhaseAmplitude v t z).re]

/-- The phase contribution costs a square of the imaginary spectral displacement. -/
theorem heatPhaseAmplitude_im_sq_bound (v : ℂ) (t : ℝ) (z : ℂ) :
    (heatPhaseAmplitude v t z).im ^ 2 ≤
      Real.exp (-(t * z.re)) * (2 * v.im ^ 2 + t ^ 2 * z.im ^ 2 / 2 * v.re ^ 2) := by
  rw [heatPhaseAmplitude_im, mul_pow]
  have he : Real.exp (-(t * z.re / 2)) ^ 2 = Real.exp (-(t * z.re)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hc := mul_le_mul_of_nonneg_left (Real.cos_sq_le_one (t * z.im / 2))
    (sq_nonneg v.im)
  have hs := mul_le_mul_of_nonneg_left
    (Real.sin_sq_le_sq (x := t * z.im / 2)) (sq_nonneg v.re)
  nlinarith [sq_nonneg
    (v.im * Real.cos (t * z.im / 2) + v.re * Real.sin (t * z.im / 2))]

def quadraticHeatValue (a b c : ℝ) (z : ℂ) : ℂ :=
  (a : ℂ) + (b : ℂ) * z + (c : ℂ) * z ^ 2

theorem quadraticHeatValue_re (a b c : ℝ) (z : ℂ) :
    (quadraticHeatValue a b c z).re = a + b * z.re + c * (z.re ^ 2 - z.im ^ 2) := by
  simp [quadraticHeatValue, pow_two, Complex.mul_re]

theorem quadraticHeatValue_im (a b c : ℝ) (z : ℂ) :
    (quadraticHeatValue a b c z).im = z.im * (b + 2 * c * z.re) := by
  simp [quadraticHeatValue, pow_two, Complex.mul_im, Complex.mul_re]
  ring

theorem quadraticHeatValue_norm_sq_le (a b c : ℝ) (z : ℂ) :
    ‖quadraticHeatValue a b c z‖ ^ 2 ≤
      3 * (a ^ 2 + b ^ 2 * ‖z‖ ^ 2 + c ^ 2 * ‖z‖ ^ 4) := by
  have h := norm_add_le ((a : ℂ) + (b : ℂ) * z) ((c : ℂ) * z ^ 2)
  have h' := norm_add_le (a : ℂ) ((b : ℂ) * z)
  have hsum : ‖quadraticHeatValue a b c z‖ ≤
      ‖(a : ℂ)‖ + ‖(b : ℂ) * z‖ + ‖(c : ℂ) * z ^ 2‖ := by
    dsimp only [quadraticHeatValue]
    linarith
  have hsq := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.2 hsum
  have hthree : (‖(a : ℂ)‖ + ‖(b : ℂ) * z‖ + ‖(c : ℂ) * z ^ 2‖) ^ 2 ≤
      3 * (‖(a : ℂ)‖ ^ 2 + ‖(b : ℂ) * z‖ ^ 2 + ‖(c : ℂ) * z ^ 2‖ ^ 2) := by
    nlinarith [sq_nonneg (‖(a : ℂ)‖ - ‖(b : ℂ) * z‖),
      sq_nonneg (‖(a : ℂ)‖ - ‖(c : ℂ) * z ^ 2‖),
      sq_nonneg (‖(b : ℂ) * z‖ - ‖(c : ℂ) * z ^ 2‖)]
  refine hsq.trans (hthree.trans_eq ?_)
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem quadraticHeatValue_derivative_sq_le (b c : ℝ) (z : ℂ) :
    (b + 2 * c * z.re) ^ 2 ≤ 2 * b ^ 2 + 8 * c ^ 2 * ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg (b - 2 * c * z.re), sq_nonneg (c * z.im)]

/-- Full phase debt, with the polynomial's mixed terms retained inside the squares. -/
theorem quadraticHeatPhaseDebt_bound (a b c t : ℝ) (z : ℂ) :
    2 * (heatPhaseAmplitude (quadraticHeatValue a b c z) t z).im ^ 2 ≤
      Real.exp (-(t * z.re)) * z.im ^ 2 *
        (4 * (b + 2 * c * z.re) ^ 2 + t ^ 2 *
          (a + b * z.re + c * (z.re ^ 2 - z.im ^ 2)) ^ 2) := by
  have h := heatPhaseAmplitude_im_sq_bound (quadraticHeatValue a b c z) t z
  rw [quadraticHeatValue_re, quadraticHeatValue_im] at h
  nlinarith

end
end GaloisForLFunctions.HTGeometry
