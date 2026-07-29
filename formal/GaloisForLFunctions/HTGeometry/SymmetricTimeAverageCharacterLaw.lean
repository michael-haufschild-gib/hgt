import GaloisForLFunctions.HTGeometry.TemporalCharacterWallCrossingLaw
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact symmetric time average of a spectral character

The normalized Fourier coefficient obtained by observing a real detuning
uniformly over a symmetric time window is exactly the sinc reporter used by
the temporal wall-crossing law.
-/

open scoped Interval

namespace GaloisForLFunctions.HTGeometry

/-- Symmetric uniform-time Fourier reporter of a real detuning. -/
noncomputable def symmetricPhaseAverage (T detuning : ℝ) : ℂ :=
  (2 * T : ℂ)⁻¹ *
    ∫ t : ℝ in -T..T,
      Complex.exp ((t * detuning : ℝ) * Complex.I)

/-- Exact Fourier identity behind the temporal wall-crossing reporter. -/
theorem symmetricPhaseAverage_eq_sinc
    (T detuning : ℝ) (hT : T ≠ 0) :
    symmetricPhaseAverage T detuning =
      Real.sinc (T * detuning) := by
  by_cases hd : detuning = 0
  · subst detuning
    simp [symmetricPhaseAverage]
    rw [← two_mul]
    calc
      (T : ℂ)⁻¹ * 2⁻¹ * (2 * T) = (T : ℂ)⁻¹ * T := by ring_nf
      _ = 1 := inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hT)
  · have hchange :=
      intervalIntegral.integral_comp_mul_right
        (fun x : ℝ => Complex.exp (x * Complex.I))
        (a := -T) (b := T) hd
    have hintegral :
        (∫ t : ℝ in -T..T,
          Complex.exp ((t * detuning : ℝ) * Complex.I)) =
        detuning⁻¹ •
          (2 * (T * detuning) *
            Real.sinc (T * detuning) : ℂ) := by
      rw [hchange]
      convert congrArg (fun z : ℂ => detuning⁻¹ • z)
        (integral_exp_mul_I_eq_sinc (T * detuning)) using 1
      · ring_nf
      · simp only [Complex.real_smul, Complex.ofReal_inv,
          Complex.ofReal_mul]
    rw [symmetricPhaseAverage, hintegral]
    simp only [Complex.real_smul, Complex.ofReal_inv]
    have hdc : (detuning : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hd
    rw [show (detuning⁻¹ : ℂ) * (2 * (T * detuning) *
          Real.sinc (T * detuning)) =
        ((detuning : ℂ)⁻¹ * detuning) *
          (2 * T * Real.sinc (T * detuning)) by ring_nf]
    rw [inv_mul_cancel₀ hdc, one_mul]
    exact inv_mul_cancel_left₀
      (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr hT))
      _

end GaloisForLFunctions.HTGeometry
