import GaloisForLFunctions.RHTower.Deninger.DeningerFourierRapidDecay
import Mathlib.Analysis.Fourier.AddCircle

/-!
# The interval Fourier coefficient is the coefficient on the circle

The coefficient defined by the integral over one period is the Fourier coefficient of the induced
function on the circle: the kernels agree, `exp (-2πinx/T)` being the character of index `-n`.

Through that identification the summation theorem for Fourier series applies, and a continuous
function with absolutely summable coefficients is bounded by the sum of their moduli — the
inequality opposite to the decay estimates, and the one that bounds a supremum by coefficients.

* `deningerFourierCoeff_eq_fourierCoeff` : the two coefficients agree.
* `deningerFourier_sup_le` : **a continuous function is bounded by the sum of the moduli of its
  coefficients.**
-/

namespace RHTower

open Complex

section Bridge

variable {T : ℝ} [hT : Fact (0 < T)]

omit hT in
theorem deningerFourierKernel_eq_fourier (n : ℤ) (x : ℝ) :
    deningerFourierKernel T n x = fourier (-n) (x : AddCircle T) := by
  rw [deningerFourierKernel, fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- **The interval coefficient is the coefficient on the circle.** -/
theorem deningerFourierCoeff_eq_fourierCoeff (f : AddCircle T → ℂ) (n : ℤ) :
    deningerFourierCoeff T (fun x : ℝ => f (x : AddCircle T)) n = fourierCoeff f n := by
  rw [fourierCoeff_eq_intervalIntegral f n 0, deningerFourierCoeff, zero_add]
  have hker : ∀ x : ℝ, deningerFourierKernel T n x * f (x : AddCircle T)
      = (fourier (-n)) (x : AddCircle T) • f (x : AddCircle T) := by
    intro x
    rw [deningerFourierKernel_eq_fourier, smul_eq_mul]
  rw [intervalIntegral.integral_congr fun x _ => hker x]
  rw [Complex.real_smul]
  norm_num

/-- **A continuous function on the circle is bounded by the sum of the moduli of its Fourier
coefficients**, when those are summable. -/
theorem deningerFourier_sup_le (f : C(AddCircle T, ℂ))
    (h : Summable fun n => ‖fourierCoeff (f : AddCircle T → ℂ) n‖) (x : AddCircle T) :
    ‖f x‖ ≤ ∑' n : ℤ, ‖fourierCoeff (f : AddCircle T → ℂ) n‖ := by
  have hsum : Summable (fourierCoeff (f : AddCircle T → ℂ)) := Summable.of_norm h
  have hseries := hasSum_fourier_series_of_summable (f := f) hsum
  have heval : HasSum (fun n : ℤ => fourierCoeff (f : AddCircle T → ℂ) n • fourier n x) (f x) := by
    have := (ContinuousMap.evalCLM ℂ x).hasSum hseries
    simpa using this
  have hnormeq : ∀ n : ℤ,
      ‖fourierCoeff (f : AddCircle T → ℂ) n • fourier n x‖
        = ‖fourierCoeff (f : AddCircle T → ℂ) n‖ := by
    intro n
    rw [norm_smul]
    simp
  have hsummable : Summable fun n : ℤ =>
      ‖fourierCoeff (f : AddCircle T → ℂ) n • fourier n x‖ := by
    refine h.congr fun n => (hnormeq n).symm
  rw [← heval.tsum_eq]
  refine le_trans (norm_tsum_le_tsum_norm hsummable) (le_of_eq ?_)
  exact tsum_congr hnormeq

end Bridge

end RHTower
