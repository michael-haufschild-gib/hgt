import Mathlib

/-!
# The Gamma factor on the critical line decays exponentially

On the critical line the Gamma function has modulus

```text
|Γ(1/2 + it)|² = π / cosh(π t) ,
```

by the reflection formula `Γ(z)Γ(1−z) = π/sin(πz)` together with `Γ(z̄) = Γ(z)‾`, which identifies
`Γ(1/2−it)` as the conjugate of `Γ(1/2+it)`.

The consequence is exponential decay in the height: `cosh(πt)` grows like `e^{π|t|}/2`, so the
modulus falls like `e^{−π|t|/2}`.  This is the mechanism that separates a *smoothed* Möbius statement
from its unsmoothed analogue.  Expanding `∑_n μ(n)e^{−nx}` over the zeros produces coefficients
`Γ(ρ)/ζ'(ρ)`, whose Gamma factor decays exponentially in the ordinate and renders the zero-sum
absolutely convergent; the unsmoothed Mertens sum carries only `1/(ρζ'(ρ))`, with polynomial decay,
which is why oscillation results bite there and not here.
-/

open Complex

namespace GaloisForLFunctions

/-- The reflected partner of a critical-line point is its conjugate. -/
theorem one_sub_half_add_mul_I (t : ℝ) :
    1 - ((1 : ℂ) / 2 + (t : ℂ) * I) = (starRingEnd ℂ) ((1 : ℂ) / 2 + (t : ℂ) * I) := by
  simp [Complex.ext_iff]
  norm_num

/-- The sine of `π` times a critical-line point is a real hyperbolic cosine. -/
theorem sin_pi_mul_half_add_mul_I (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) * ((1 : ℂ) / 2 + (t : ℂ) * I))
      = (Real.cosh (Real.pi * t) : ℂ) := by
  have h : (Real.pi : ℂ) * ((1 : ℂ) / 2 + (t : ℂ) * I)
      = (Real.pi : ℂ) / 2 + ((Real.pi * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.cos_mul_I]
  push_cast
  ring

/-- **The critical-line Gamma modulus.**  `|Γ(1/2+it)|² = π / cosh(π t)`. -/
theorem normSq_Gamma_half_add_mul_I (t : ℝ) :
    ‖Complex.Gamma ((1 : ℂ) / 2 + (t : ℂ) * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  set z : ℂ := (1 : ℂ) / 2 + (t : ℂ) * I with hz
  have hcoshpos : (0 : ℝ) < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have hconj : Complex.Gamma (1 - z) = (starRingEnd ℂ) (Complex.Gamma z) := by
    rw [hz, one_sub_half_add_mul_I t, Complex.Gamma_conj]
  have hmul : Complex.Gamma z * (starRingEnd ℂ) (Complex.Gamma z)
      = ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
    rw [← hconj, Complex.Gamma_mul_Gamma_one_sub z, hz, sin_pi_mul_half_add_mul_I t]
    push_cast
    ring
  have hcast : ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ)
      = ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
    rw [← hmul, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast hcast

/-- `cosh` dominates half the exponential of the absolute value. -/
theorem exp_abs_div_two_le_cosh (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
    nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

/-- **Exponential decay of the critical-line Gamma factor.**  The squared modulus is at most
`2π·e^{−π|t|}`: exponential decay in the ordinate.  This is the mechanism that makes a smoothed
Möbius zero-expansion absolutely convergent where the unsmoothed one, carrying only polynomial
decay, is not. -/
theorem normSq_Gamma_half_add_mul_I_le (t : ℝ) :
    ‖Complex.Gamma ((1 : ℂ) / 2 + (t : ℂ) * I)‖ ^ 2
      ≤ 2 * Real.pi * Real.exp (-(Real.pi * |t|)) := by
  rw [normSq_Gamma_half_add_mul_I]
  have hcosh : Real.exp (Real.pi * |t|) / 2 ≤ Real.cosh (Real.pi * t) := by
    have h := exp_abs_div_two_le_cosh (Real.pi * t)
    rwa [abs_mul, abs_of_pos Real.pi_pos] at h
  have hpos : (0 : ℝ) < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have hhalf : (0 : ℝ) < Real.exp (Real.pi * |t|) / 2 := by positivity
  have hstep : Real.pi / Real.cosh (Real.pi * t) ≤ Real.pi / (Real.exp (Real.pi * |t|) / 2) :=
    div_le_div_of_nonneg_left Real.pi_pos.le hhalf hcosh
  refine le_trans hstep ?_
  rw [Real.exp_neg, div_div_eq_mul_div]
  rw [div_le_iff₀ (Real.exp_pos (Real.pi * |t|))]
  have hcancel : Real.exp (Real.pi * |t|) * (Real.exp (Real.pi * |t|))⁻¹ = 1 :=
    mul_inv_cancel₀ (Real.exp_pos _).ne'
  nlinarith [hcancel, Real.pi_pos, Real.exp_pos (Real.pi * |t|)]

end GaloisForLFunctions
