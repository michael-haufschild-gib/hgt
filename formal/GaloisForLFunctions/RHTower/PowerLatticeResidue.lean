import GaloisForLFunctions.RHTower.PowerLatticeLambertForm

/-!
# Simplicity of the power-lattice poles, and the even-order collapse

Two facts about the quadratic `1 + 2u cos α + u²` at its roots `-e^{∓iα}`.

Its derivative there is `∓2i sin α`.  So the roots are simple exactly when `sin α ≠ 0`, and the
residue of `u sin α/(1 + 2u cos α + u²)` at either root is `∓e^{∓iα}/(2i)` — independent of `α`
apart from the phase, which is what makes the residues of the transform constant along each
lattice.

When `α` is an integer multiple of `π` — the even-order case — every coefficient of the transform
carries a factor `sin(kα) = 0`, and the transform vanishes identically.

* `GaloisForLFunctions.RHTower.deriv_lambertQuadratic_at_root_pos`;
* `GaloisForLFunctions.RHTower.deriv_lambertQuadratic_at_root_neg`;
* `GaloisForLFunctions.RHTower.residue_lambertNumerator_pos`;
* `GaloisForLFunctions.RHTower.tsum_zeta_coeff_eq_zero_of_natMulPi`.
-/

open Complex

namespace GaloisForLFunctions.RHTower

/-- The derivative of the quadratic at the root `-e^{iα}`. -/
theorem deriv_lambertQuadratic_at_root_pos (α : ℝ) :
    2 * (Real.cos α : ℂ) + 2 * (-Complex.exp ((α : ℝ) * Complex.I))
      = -(2 * Complex.I * (Real.sin α : ℂ)) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- The derivative of the quadratic at the root `-e^{-iα}`. -/
theorem deriv_lambertQuadratic_at_root_neg (α : ℝ) :
    2 * (Real.cos α : ℂ) + 2 * (-Complex.exp (-((α : ℝ) * Complex.I)))
      = 2 * Complex.I * (Real.sin α : ℂ) := by
  have harg : -((α : ℝ) * Complex.I) = ((-α : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- **The roots are simple exactly off the even orders.**  The derivative vanishes at a root only
when `sin α = 0`. -/
theorem deriv_lambertQuadratic_ne_zero_pos {α : ℝ} (hα : Real.sin α ≠ 0) :
    2 * (Real.cos α : ℂ) + 2 * (-Complex.exp ((α : ℝ) * Complex.I)) ≠ 0 := by
  have hs : ((Real.sin α : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hα
  rw [deriv_lambertQuadratic_at_root_pos, neg_ne_zero]
  exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hs

/-- **The residue of the Lambert numerator at the root `-e^{iα}`.**  Simple pole, so the residue is
the quotient of the numerator by the derivative of the denominator. -/
theorem residue_lambertNumerator_pos {α : ℝ} (hα : Real.sin α ≠ 0) :
    (-Complex.exp ((α : ℝ) * Complex.I)) * (Real.sin α : ℂ)
        / (2 * (Real.cos α : ℂ) + 2 * (-Complex.exp ((α : ℝ) * Complex.I)))
      = Complex.exp ((α : ℝ) * Complex.I) / (2 * Complex.I) := by
  rw [deriv_lambertQuadratic_at_root_pos]
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by simp [Complex.I_ne_zero]
  have hs : ((Real.sin α : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hα
  field_simp

/-- **The residue at the root `-e^{-iα}`.** -/
theorem residue_lambertNumerator_neg {α : ℝ} (hα : Real.sin α ≠ 0) :
    (-Complex.exp (-((α : ℝ) * Complex.I))) * (Real.sin α : ℂ)
        / (2 * (Real.cos α : ℂ) + 2 * (-Complex.exp (-((α : ℝ) * Complex.I))))
      = -(Complex.exp (-((α : ℝ) * Complex.I)) / (2 * Complex.I)) := by
  rw [deriv_lambertQuadratic_at_root_neg]
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by simp [Complex.I_ne_zero]
  have hs : ((Real.sin α : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hα
  field_simp

/-- **The even-order collapse.**  At an integer multiple of `π` every coefficient of the transform
carries a vanishing sine, so the whole series is zero. -/
theorem tsum_zeta_coeff_eq_zero_of_natMulPi (m : ℕ) (s : ℝ) (ξ : ℂ) :
    ∑' k : ℕ, ((-1 : ℂ) ^ k * (Real.sin (((k : ℝ) + 1) * ((m : ℝ) * Real.pi)) : ℂ) * ξ ^ (k + 1)
          / (((2 * Real.pi) ^ (s * (k + 1)) : ℝ) : ℂ))
        * riemannZeta (((1 + s * (k + 1) : ℝ) : ℝ) : ℂ) = 0 := by
  have hzero : ∀ k : ℕ, Real.sin (((k : ℝ) + 1) * ((m : ℝ) * Real.pi)) = 0 := by
    intro k
    have harg : ((k : ℝ) + 1) * ((m : ℝ) * Real.pi) = (((k + 1) * m : ℕ) : ℝ) * Real.pi := by
      push_cast
      ring
    rw [harg]
    exact Real.sin_nat_mul_pi _
  have hterm : ∀ k : ℕ,
      ((-1 : ℂ) ^ k * (Real.sin (((k : ℝ) + 1) * ((m : ℝ) * Real.pi)) : ℂ) * ξ ^ (k + 1)
          / (((2 * Real.pi) ^ (s * (k + 1)) : ℝ) : ℂ))
        * riemannZeta (((1 + s * (k + 1) : ℝ) : ℝ) : ℂ) = 0 := by
    intro k
    rw [hzero k]
    simp
  rw [tsum_congr hterm, tsum_zero]

end GaloisForLFunctions.RHTower
