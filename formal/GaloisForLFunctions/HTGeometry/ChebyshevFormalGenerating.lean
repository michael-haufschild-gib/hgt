import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Formal generating series of Chebyshev polynomials at a node

For a complex node `y`, the formal power series `Σ_n T_n(y) X^n` of first-kind Chebyshev values satisfies
the classical rational generating-function identity `(1 - 2yX + X^2) Σ_n T_n(y) X^n = 1 - yX`, proved
coefficientwise from the three-term recurrence `T_(n+2) = 2y T_(n+1) - T_n`. The centered form
`2 Σ_n T_n(y) X^n - 1` then satisfies `(1 - 2yX + X^2)(2 Σ_n T_n(y) X^n - 1) = 1 - X^2`.

## Main results

- `chebyshevNodeSeries_equation`: `(1 - 2yX + X^2) · Σ_n T_n(y) X^n = 1 - yX` in `ℂ⟦X⟧`.
- `chebyshevNodeSeries_centered_equation`: `(1 - 2yX + X^2) · (2 Σ_n T_n(y) X^n - 1) = 1 - X^2`.

## Hypotheses

Unconditional identities of formal power series, valid for every `y : ℂ`.
-/

open Polynomial

namespace HTGeometry

/-- The formal power series `Σ_n T_n(y) X^n` of first-kind Chebyshev values at the node `y`. -/
noncomputable def chebyshevNodeSeries (y : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => (Chebyshev.T ℂ (n : ℤ)).eval y)

private theorem chebyshevNodeSeries_coeff (y : ℂ) (n : ℕ) :
    PowerSeries.coeff n (chebyshevNodeSeries y) =
      (Chebyshev.T ℂ (n : ℤ)).eval y := by
  simp [chebyshevNodeSeries]

private theorem chebyshevNodeSeries_coeff_add_two (y : ℂ) (n : ℕ) :
    PowerSeries.coeff (n + 2) (chebyshevNodeSeries y) =
      2 * y * PowerSeries.coeff (n + 1) (chebyshevNodeSeries y) -
        PowerSeries.coeff n (chebyshevNodeSeries y) := by
  simp only [chebyshevNodeSeries_coeff, Nat.cast_add, Nat.cast_ofNat,
    Chebyshev.T_add_two, eval_sub, eval_mul, eval_ofNat, eval_X]
  ring

/-- Chebyshev generating function as a formal identity: `(1 - 2yX + X^2) Σ_n T_n(y) X^n = 1 - yX`. -/
theorem chebyshevNodeSeries_equation (y : ℂ) :
    ((1 : PowerSeries ℂ) - PowerSeries.X * PowerSeries.C (2 * y) +
        PowerSeries.X ^ (2 : ℕ)) * chebyshevNodeSeries y =
      1 - PowerSeries.X * PowerSeries.C y := by
  have hrearrange :
      ((1 : PowerSeries ℂ) - PowerSeries.X * PowerSeries.C (2 * y) +
          PowerSeries.X ^ (2 : ℕ)) * chebyshevNodeSeries y =
        chebyshevNodeSeries y -
          PowerSeries.X * (PowerSeries.C (2 * y) * chebyshevNodeSeries y) +
          PowerSeries.X * (PowerSeries.X * chebyshevNodeSeries y) := by ring
  rw [hrearrange]
  apply PowerSeries.ext
  intro n
  rw [map_add, map_sub, map_sub]
  cases n with
  | zero =>
      simp [chebyshevNodeSeries, PowerSeries.coeff_zero_X_mul]
  | succ n =>
      cases n with
      | zero =>
          simp [chebyshevNodeSeries, PowerSeries.coeff_succ_X_mul]
          ring
      | succ n =>
          simp only [PowerSeries.coeff_succ_X_mul,
            PowerSeries.coeff_C_mul, chebyshevNodeSeries_coeff_add_two]
          simp

/-- Centered generating function: `(1 - 2yX + X^2) (2 Σ_n T_n(y) X^n - 1) = 1 - X^2`. -/
theorem chebyshevNodeSeries_centered_equation (y : ℂ) :
    ((1 : PowerSeries ℂ) - PowerSeries.X * PowerSeries.C (2 * y) +
        PowerSeries.X ^ (2 : ℕ)) *
        (2 * chebyshevNodeSeries y - 1) =
      1 - PowerSeries.X ^ (2 : ℕ) := by
  let D : PowerSeries ℂ :=
    1 - PowerSeries.X * PowerSeries.C (2 * y) + PowerSeries.X ^ (2 : ℕ)
  change D * (2 * chebyshevNodeSeries y - 1) = _
  calc
    D * (2 * chebyshevNodeSeries y - 1) =
        2 * (D * chebyshevNodeSeries y) - D := by ring
    _ = 1 - PowerSeries.X ^ (2 : ℕ) := by
      rw [chebyshevNodeSeries_equation]
      dsimp [D]
      have hcy : (PowerSeries.C (2 * y) : PowerSeries ℂ) =
          2 * PowerSeries.C y := by simp only [map_mul, map_ofNat]
      rw [hcy]
      ring

end HTGeometry
