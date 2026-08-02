import GaloisForLFunctions.RHTower.DeningerTestPullback
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Fourier coefficients of a periodic function and its derivative

Integrating by parts over one period, the boundary terms of a periodic function cancel because the
Fourier kernel takes the same value at both ends, so the Fourier coefficient of the derivative is
the coefficient of the function times `2πin/T`.

Iterating this is what makes the coefficients of a smooth periodic function decay faster than any
power, the first step towards the nuclearity of a smooth test space.

* `deningerFourierKernel`, `_hasDerivAt`, `_periodic` : the kernel of the Fourier coefficient.
* `deningerFourierCoeff` : the `n`-th Fourier coefficient of a periodic function.
* `deningerFourierCoeff_deriv` : **the coefficient of the derivative.**
-/

namespace RHTower

open Complex intervalIntegral MeasureTheory

section FourierCoeff

/-- The kernel `exp (-2πinx/T)` of the `n`-th Fourier coefficient. -/
noncomputable def deningerFourierKernel (T : ℝ) (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * n * x) / T)

theorem deningerFourierKernel_hasDerivAt (T : ℝ) (n : ℤ) (x : ℝ) :
    HasDerivAt (deningerFourierKernel T n)
      (-(2 * Real.pi * Complex.I * n) / T * deningerFourierKernel T n x) x := by
  have hlin : HasDerivAt (fun x : ℝ => -(2 * Real.pi * Complex.I * n * (x : ℂ)) / T)
      (-(2 * Real.pi * Complex.I * n) / T) x := by
    have h0 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
    have h1 := (h0.const_mul (-(2 * Real.pi * Complex.I * (n : ℂ)))).div_const (T : ℂ)
    simpa [neg_mul] using h1
  have h := hlin.cexp
  refine h.congr_deriv ?_
  rw [deningerFourierKernel]
  ring

theorem deningerFourierKernel_periodic (T : ℝ) (hT : T ≠ 0) (n : ℤ) :
    deningerFourierKernel T n T = deningerFourierKernel T n 0 := by
  have h0 : deningerFourierKernel T n 0 = 1 := by
    rw [deningerFourierKernel]
    norm_num
  have hT' : deningerFourierKernel T n T = 1 := by
    rw [deningerFourierKernel]
    have hval : -(2 * Real.pi * Complex.I * n * (T : ℂ)) / T
        = (-n : ℤ) * (2 * Real.pi * Complex.I) := by
      have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast hT
      field_simp
      push_cast
      ring
    rw [hval, Complex.exp_int_mul_two_pi_mul_I]
  rw [h0, hT']

/-- **The `n`-th Fourier coefficient** of a function of period `T`. -/
noncomputable def deningerFourierCoeff (T : ℝ) (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  (1 / T) * ∫ x in (0 : ℝ)..T, deningerFourierKernel T n x * f x

/-- **The Fourier coefficient of the derivative of a periodic function.**  Integrating by parts
over one period, the boundary terms cancel by periodicity. -/
theorem deningerFourierCoeff_deriv {T : ℝ} (hT : T ≠ 0) {f f' : ℝ → ℂ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hper : f T = f 0) (n : ℤ) :
    deningerFourierCoeff T f' n
      = (2 * Real.pi * Complex.I * n) / T * deningerFourierCoeff T f n := by
  have hker : ∀ x ∈ Set.uIcc (0 : ℝ) T, HasDerivAt (deningerFourierKernel T n)
      (-(2 * Real.pi * Complex.I * n) / T * deningerFourierKernel T n x) x :=
    fun x _ => deningerFourierKernel_hasDerivAt T n x
  have hfder : ∀ x ∈ Set.uIcc (0 : ℝ) T, HasDerivAt f (f' x) x := fun x _ => hderiv x
  have hkercont : Continuous (deningerFourierKernel T n) := by
    refine Continuous.cexp ?_
    fun_prop
  have hint1 : IntervalIntegrable
      (fun x => -(2 * Real.pi * Complex.I * n) / T * deningerFourierKernel T n x)
      volume 0 T := (hkercont.const_mul _).intervalIntegrable _ _
  have hint2 : IntervalIntegrable f' volume 0 T := hf'.intervalIntegrable _ _
  have hparts := integral_mul_deriv_eq_deriv_mul hker hfder hint1 hint2
  have hbdry : deningerFourierKernel T n T * f T - deningerFourierKernel T n 0 * f 0 = 0 := by
    rw [deningerFourierKernel_periodic T hT n, hper]
    ring
  rw [hbdry] at hparts
  have hsimp : ∫ x in (0 : ℝ)..T, deningerFourierKernel T n x * f' x
      = (2 * Real.pi * Complex.I * n) / T
        * ∫ x in (0 : ℝ)..T, deningerFourierKernel T n x * f x := by
    rw [hparts]
    have hpull : ∫ x in (0 : ℝ)..T,
        (-(2 * Real.pi * Complex.I * n) / T * deningerFourierKernel T n x) * f x
        = (-(2 * Real.pi * Complex.I * n) / T)
          * ∫ x in (0 : ℝ)..T, deningerFourierKernel T n x * f x := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun x _ => by ring
    rw [hpull]
    ring
  rw [deningerFourierCoeff, deningerFourierCoeff, hsimp]
  ring

end FourierCoeff

end RHTower
