import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The moment-Borel coefficient of a power canonical product

The coefficients of the inverse-power tail of the logarithmic derivative of a power canonical
product are `b_k = (-1)^k ζ(-sk)`, and the order-`s` moment-Borel transform divides them by
`Γ(1 + sk)`.  The functional equation turns that quotient into a value of `ζ` on the line of
absolute convergence, times a sine which is the only source of the sign oscillation:

`ζ(-w) = -2 (2π)^{-(1+w)} Γ(1+w) sin(πw/2) ζ(1+w)`.

The sine is what makes the tail vanish identically at even integers `s`: every `sk` is then an even
integer and `sin(πsk/2) = 0`.

* `GaloisForLFunctions.RHTower.riemannZeta_neg_eq`;
* `GaloisForLFunctions.RHTower.riemannZeta_neg_div_Gamma_eq`;
* `GaloisForLFunctions.RHTower.riemannZeta_neg_eq_zero_of_even`.
-/

open Complex

namespace GaloisForLFunctions.RHTower

/-- **The functional equation in reflected form.**  For `w` off the exceptional set, the value at
`-w` is the value at `1 + w` times a Gamma factor and a sine. -/
theorem riemannZeta_neg_eq {w : ℂ} (hw : ∀ n : ℕ, (1 + w) ≠ -(n : ℂ)) (hw0 : w ≠ 0) :
    riemannZeta (-w)
      = -2 * (2 * (Real.pi : ℂ)) ^ (-(1 + w)) * Complex.Gamma (1 + w)
        * Complex.sin (Real.pi * w / 2) * riemannZeta (1 + w) := by
  have hne1 : (1 + w) ≠ 1 := by
    intro hcon
    exact hw0 (by linear_combination hcon)
  have hfe := riemannZeta_one_sub hw hne1
  have hsub : (1 : ℂ) - (1 + w) = -w := by ring
  rw [hsub] at hfe
  have hcos : Complex.cos (Real.pi * (1 + w) / 2)
      = -Complex.sin (Real.pi * w / 2) := by
    have harg : (Real.pi : ℂ) * (1 + w) / 2 = Real.pi / 2 + Real.pi * w / 2 := by ring
    rw [harg, Complex.cos_add, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring
  rw [hfe, hcos]
  ring

/-- **The moment-Borel coefficient.**  Dividing by the Gamma factor of the order-`s` transform
leaves a value of `ζ` on the line of absolute convergence. -/
theorem riemannZeta_neg_div_Gamma_eq {w : ℂ} (hw : ∀ n : ℕ, (1 + w) ≠ -(n : ℂ)) (hw0 : w ≠ 0)
    (hGamma : Complex.Gamma (1 + w) ≠ 0) :
    riemannZeta (-w) / Complex.Gamma (1 + w)
      = -2 * (2 * (Real.pi : ℂ)) ^ (-(1 + w))
        * Complex.sin (Real.pi * w / 2) * riemannZeta (1 + w) := by
  rw [riemannZeta_neg_eq hw hw0]
  field_simp

/-- **The tail vanishes at every even order.**  When `w` is an even natural number the sine of the
functional equation vanishes, so the coefficient does. -/
theorem riemannZeta_neg_eq_zero_of_even {m : ℕ} (hm : 0 < m) :
    riemannZeta (-(2 * m : ℂ)) = 0 := by
  have hw : ∀ n : ℕ, (1 + (2 * m : ℂ)) ≠ -(n : ℂ) := by
    intro n hcon
    have hre : (1 + 2 * (m : ℝ)) = -(n : ℝ) := by
      have := congrArg Complex.re hcon
      simpa using this
    have h1 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hw0 : (2 * m : ℂ) ≠ 0 := by
    intro hcon
    have hmc : (m : ℂ) = 0 := by
      have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
      exact (mul_eq_zero.mp hcon).resolve_left h2
    have hm0 : m = 0 := by exact_mod_cast hmc
    omega
  rw [riemannZeta_neg_eq hw hw0]
  have hsin : Complex.sin ((Real.pi : ℂ) * (2 * m : ℂ) / 2) = 0 := by
    have harg : (Real.pi : ℂ) * (2 * m : ℂ) / 2 = (m : ℂ) * Real.pi := by ring
    rw [harg]
    exact Complex.sin_nat_mul_pi m
  rw [hsin]
  ring

end GaloisForLFunctions.RHTower
