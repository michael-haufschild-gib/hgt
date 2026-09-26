import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# The normalized Hecke operator in real coordinates

The generic finite-sum definition is independent of the Eisenstein analysis.
-/

open scoped BigOperators

namespace RHTower

/-- The normalized Hecke operator on functions of `(x, y)`. -/
noncomputable def heckeOp (p : ℕ) (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  (((Real.sqrt p)⁻¹ : ℝ) : ℂ) *
    (F (p * x) (p * y) + ∑ b ∈ Finset.range p, F ((x + b) / p) (y / p))

end RHTower
