import GaloisForLFunctions.HTGeometry.QNMComplexHyperboloidalWave

/-!
# An exact Pöschl--Teller barrier wave family

Applying the optical paper's hyperboloidal operator to the constant compact
profile gives the barrier coefficient `-z * (z + 1)`. Choosing
`z = -1/2 + i s` makes that coefficient the real number `s² + 1/4`.
The resulting profiles solve the actual wave equation with potential
`(s² + 1/4) / cosh² x`, for every real parameter, time, and position.

This is a derived application of the coordinate machinery motivated by
Al Sheikh--Jaramillo, arXiv:2607.25133. The time convention agrees with
Morikawa, arXiv:2608.29806: frequency is `-s - i/2`, and amplitude decays
as `exp(-t/2)` at fixed position. Conclusions concern these explicit profiles,
their derivatives, and their norms.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry

/-- Damped exponent with a real oscillation parameter. -/
def qnmPoschlTellerExponent (s : ℝ) : ℂ := -1 / 2 + Complex.I * s

theorem qnmHyperboloidal_constant_barrier (z : ℂ) :
    (C (z ^ 2) + C (-z * (z + 1)) * (1 - X ^ 2)) * 1 -
      qnmHyperboloidalDx z (qnmHyperboloidalDx z (1 : Polynomial ℂ)) = 0 := by
  rw [qnmHyperboloidalDx_squared]
  simp [map_neg, map_mul, map_add, map_pow]
  ring

theorem qnmPoschlTeller_barrier_coefficient (s : ℝ) :
    -qnmPoschlTellerExponent s * (qnmPoschlTellerExponent s + 1) = (s : ℂ) ^ 2 + 1 / 4 := by
  unfold qnmPoschlTellerExponent
  have hI := Complex.I_sq
  linear_combination (norm := ring_nf) -(s : ℂ) ^ 2 * hI

theorem qnmPoschlTeller_barrier_polynomial (s : ℝ) :
    (C ((qnmPoschlTellerExponent s) ^ 2) +
        C ((s : ℂ) ^ 2 + 1 / 4) * (1 - X ^ 2)) * 1 -
      qnmHyperboloidalDx (qnmPoschlTellerExponent s)
        (qnmHyperboloidalDx (qnmPoschlTellerExponent s) (1 : Polynomial ℂ)) = 0 := by
  rw [← qnmPoschlTeller_barrier_coefficient]
  exact qnmHyperboloidal_constant_barrier _


theorem qnm_tanh_barrier_eq_cosh (x : ℝ) :
    1 - Real.tanh x ^ 2 = 1 / Real.cosh x ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have h := Real.cosh_sq_sub_sinh_sq x
  field_simp
  nlinarith

/-- Closed wave-equation identity for the explicit barrier mode family. -/
theorem qnmPoschlTeller_wave_equation (s t x : ℝ) :
    deriv (deriv (fun u => qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1 u x)) t -
        deriv (deriv (qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1 t)) x +
        (((s ^ 2 + 1 / 4) / Real.cosh x ^ 2 : ℝ) : ℂ) *
          qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1 t x = 0 := by
  have h := qnmComplexHyperboloidalWave_wave_residual (qnmPoschlTellerExponent s) 1
    (C ((s : ℂ) ^ 2 + 1 / 4) * (1 - X ^ 2)) t x
  rw [qnmPoschlTeller_barrier_polynomial] at h
  have hV : (C ((s : ℂ) ^ 2 + 1 / 4) * (1 - X ^ 2)).eval (Real.tanh x : ℂ) =
      (((s ^ 2 + 1 / 4) / Real.cosh x ^ 2 : ℝ) : ℂ) := by
    simp only [eval_mul, eval_C, eval_sub, eval_one, eval_pow, eval_X]
    have hx := congrArg Complex.ofReal (qnm_tanh_barrier_eq_cosh x)
    push_cast at hx ⊢
    rw [hx]
    ring
  rw [hV] at h
  simpa [qnmComplexHyperboloidalWave, qnmComplexHyperboloidalProfile] using h

theorem norm_qnmPoschlTeller_wave (s t x : ℝ) :
    ‖qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1 t x‖ =
      Real.exp ((qnmHyperboloidalHeight x - t) / 2) := by
  simp [qnmComplexHyperboloidalWave, qnmComplexHyperboloidalProfile,
    Complex.norm_exp, qnmPoschlTellerExponent, Complex.mul_re]
  rw [← Real.exp_add]
  congr 1
  ring

theorem qnmPoschlTeller_wave_ne_zero (s t x : ℝ) :
    qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1 t x ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_qnmPoschlTeller_wave]
  exact (Real.exp_pos _).ne'

theorem qnmPoschlTeller_wave_harmonic (s t x : ℝ) :
    qnmComplexHyperboloidalWave (qnmPoschlTellerExponent s) 1 t x =
      qnmHarmonic (-(s : ℂ) - Complex.I / 2) (t - qnmHyperboloidalHeight x) := by
  simp [qnmComplexHyperboloidalWave, qnmComplexHyperboloidalProfile, qnmHarmonic]
  rw [← Complex.exp_add]
  congr 1
  unfold qnmPoschlTellerExponent
  have hI := Complex.I_sq
  linear_combination (norm := ring_nf) -((t : ℂ) - qnmHyperboloidalHeight x) / 2 * hI
end GaloisForLFunctions.HTGeometry
