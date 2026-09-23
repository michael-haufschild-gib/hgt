import Mathlib

/-!
# Setup for the transcendence of `π`

`Mathlib` provides only the analytic half of Lindemann–Weierstrass
(`LindemannWeierstrass.exp_polynomial_approx`); the algebraic half is already supplied in this
project by `exp_relation_ne` and its corollaries (`SeamSpectrumTranscendence`).  The transcendence
of `π` is the specialization of that engine to the Euler relation `e^{iπ} = −1`: if `π` were
algebraic then `θ = iπ` would be a nonzero algebraic number, its conjugate set `θ₁,…,θ_d` would
carry the vanishing exponential relation `∏_j (1 + e^{θ_j}) = 0` (one factor is `1 + e^{iπ} = 0`),
and the symmetric-function estimate would force a contradiction.

This file records the elementary reduction facts feeding that assembly: the Euler value
`e^{iπ} = −1`, the nonvanishing `iπ ≠ 0`, the algebraicity of `i`, and the transfer
`π algebraic ⟹ iπ algebraic`.
-/

open Polynomial

namespace GaloisForLFunctions
namespace RHTower

/-- **Euler's identity in exponential form.**  `e^{iπ} = −1`. -/
theorem exp_pi_mul_I : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := by
  rw [Complex.exp_mul_I]; simp

/-- `iπ` is a nonzero complex number. -/
theorem pi_mul_I_ne_zero_piTranscendenceSetup : ((Real.pi : ℂ) * Complex.I) ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero

/-- For every integer `n`, `e^{n·iπ} = (−1)^n`. -/
theorem exp_int_mul_pi_mul_I (n : ℤ) :
    Complex.exp ((n : ℂ) * ((Real.pi : ℂ) * Complex.I)) = (-1) ^ n := by
  rw [Complex.exp_int_mul, exp_pi_mul_I]

/-- **`i` is algebraic over `ℚ`.**  It is a root of `X² + 1`. -/
theorem isAlgebraic_I : IsAlgebraic ℚ Complex.I := by
  refine ⟨Polynomial.X ^ (2 : ℕ) + 1, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun p : ℚ[X] => p.coeff 2) h
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_one] at hc
  · simp [Polynomial.aeval_def, Polynomial.eval₂_add, Complex.I_sq]

/-- **`π` algebraic forces `iπ` algebraic.**  As a product of the algebraic numbers `i` and `π`. -/
theorem isAlgebraic_pi_mul_I (hπ : IsAlgebraic ℚ (Real.pi : ℂ)) :
    IsAlgebraic ℚ ((Real.pi : ℂ) * Complex.I) :=
  hπ.mul isAlgebraic_I

end RHTower
end GaloisForLFunctions
