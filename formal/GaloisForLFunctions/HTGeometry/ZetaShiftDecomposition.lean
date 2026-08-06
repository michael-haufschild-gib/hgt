import GaloisForLFunctions.HTGeometry.LimsupUnitFactor
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The functional-equation decomposition of the shifted zeta values

Applying the functional equation at `1 - s₀ + k` writes the factorially
normalized shifted zeta value as a geometric factor `(2π)^{-k}` times a
bounded-growth remainder: a constant, the Gamma quotient `Γ(1-s₀+k)/Γ(1+k)`, the
oscillating cosine, and a zeta value tending to one.

This is the exact splitting the independent cusp-constant computation needs.
Each of the four remainder factors has already been shown invisible to the
`k`-th root, so only the geometric factor survives, giving `1/(2π)`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

section Decomposition

variable {s₀ : ℂ}

theorem two_pi_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero two_ne_zero hpi

theorem shift_ne_negNat (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) (k n : ℕ) :
    1 - s₀ + (k : ℂ) ≠ -(n : ℂ) := by
  intro hcon
  refine hs (1 + k + n) ?_
  push_cast
  linear_combination -hcon

theorem shift_ne_one (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) (k : ℕ) :
    1 - s₀ + (k : ℂ) ≠ 1 := by
  intro hcon
  refine hs k ?_
  linear_combination -hcon

/-- The geometric factor of the functional equation splits off. -/
theorem two_pi_cpow_shift (k : ℕ) :
    (2 * (Real.pi : ℂ)) ^ (-(1 - s₀ + (k : ℂ)))
      = ((2 * (Real.pi : ℂ))⁻¹) ^ k * (2 * (Real.pi : ℂ)) ^ (-(1 - s₀)) := by
  have hsplit : -(1 - s₀ + (k : ℂ)) = -(k : ℂ) + -(1 - s₀) := by ring
  rw [hsplit, Complex.cpow_add _ _ two_pi_ne_zero, Complex.cpow_neg,
    Complex.cpow_natCast, ← inv_pow]

/-- **Functional-equation decomposition of the shifted zeta values.** -/
theorem zetaShift_decomposition (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) (k : ℕ) :
    riemannZeta (s₀ - (k : ℂ)) / (Nat.factorial k : ℂ)
      = ((2 * (Real.pi : ℂ))⁻¹) ^ k
        * (2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s₀))
            * (Complex.Gamma (1 - s₀ + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ)))
            * Complex.cos ((Real.pi : ℂ) * (1 - s₀ + (k : ℂ)) / 2)
            * riemannZeta (1 - s₀ + (k : ℂ))) := by
  have hfe := riemannZeta_one_sub (s := 1 - s₀ + (k : ℂ))
    (shift_ne_negNat hs k) (shift_ne_one hs k)
  have harg : 1 - (1 - s₀ + (k : ℂ)) = s₀ - (k : ℂ) := by ring
  rw [harg] at hfe
  have hfact : Complex.Gamma (1 + (k : ℂ)) = (Nat.factorial k : ℂ) := by
    rw [add_comm]
    exact Complex.Gamma_nat_eq_factorial k
  have hfactne : Complex.Gamma (1 + (k : ℂ)) ≠ 0 := by
    rw [hfact]
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [hfe, two_pi_cpow_shift, ← hfact]
  field_simp

end Decomposition

end GaloisForLFunctions.HTGeometry
