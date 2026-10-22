import GaloisForLFunctions.RHTower.Deninger.DeningerPositiveCellDegreeZero
import Mathlib.Data.Complex.Basic

/-!
# Shift-pair local intersection algebra

The invertible center/shift coordinate change sends a local shifted pair to independent
coordinates `x` and `y`.  If the two divisor orders are `m` and `n`, units may be discarded and
the local algebra is the tensor product

`ℂ[x]/(x^m) ⊗[ℂ] ℂ[y]/(y^n)`.

This file constructs that algebra literally from two `AdjoinRoot` quotients and proves its
complex dimension is `m*n`.  It is the local product-multiplicity infrastructure used by the
Euler shift-pair incidence theorem.
-/

namespace GaloisForLFunctions
namespace RHTower
namespace ShiftPairLocalIntersectionAlgebra

open Polynomial

noncomputable section

/-- The invertible linear coordinate change `(c,u) ↦ (c-u,c+u)`. -/
def shiftPairLinearEquiv : (ℂ × ℂ) ≃ₗ[ℂ] (ℂ × ℂ) where
  toFun z := (z.1 - z.2, z.1 + z.2)
  invFun z := ((z.1 + z.2) / 2, (z.2 - z.1) / 2)
  left_inv z := by
    apply Prod.ext <;> dsimp <;> ring
  right_inv z := by
    apply Prod.ext <;> dsimp <;> ring
  map_add' x y := by
    apply Prod.ext <;> dsimp <;> ring
  map_smul' a x := by
    apply Prod.ext <;> dsimp <;> ring

@[simp] theorem shiftPairLinearEquiv_apply (c u : ℂ) :
    shiftPairLinearEquiv (c, u) = (c - u, c + u) := rfl

@[simp] theorem shiftPairLinearEquiv_symm_apply (x y : ℂ) :
    shiftPairLinearEquiv.symm (x, y) = ((x + y) / 2, (y - x) / 2) := rfl

/-- One-variable truncated local algebra `ℂ[x]/(x^m)`. -/
abbrev TruncatedRootAlgebra (m : ℕ) :=
  AdjoinRoot ((X : Polynomial ℂ) ^ m)

/-- Canonical monomial power basis of the truncated local algebra. -/
def truncatedRootPowerBasis (m : ℕ) :
    PowerBasis ℂ (TruncatedRootAlgebra m) :=
  _root_.RHTower.deningerMonicQuotient_powerBasis (Polynomial.monic_X_pow m)

/-- The monomials `1,x,...,x^(m-1)` give exact dimension `m`. -/
theorem finrank_truncatedRootAlgebra (m : ℕ) :
    Module.finrank ℂ (TruncatedRootAlgebra m) = m := by
  rw [(truncatedRootPowerBasis m).finrank]
  exact Polynomial.natDegree_X_pow (R := ℂ) m

/-- Literal algebraic model of `ℂ{x,y}/(x^m,y^n)`. -/
abbrev LocalIntersectionAlgebra (m n : ℕ) :=
  TensorProduct ℂ (TruncatedRootAlgebra m) (TruncatedRootAlgebra n)

/-- **Local product multiplicity.** The local shift-pair intersection algebra has dimension
`m*n`, including the degenerate zero-order cases. -/
theorem finrank_localIntersectionAlgebra (m n : ℕ) :
    Module.finrank ℂ (LocalIntersectionAlgebra m n) = m * n := by
  rw [Module.finrank_tensorProduct, finrank_truncatedRootAlgebra,
    finrank_truncatedRootAlgebra]

/-- Intersection multiplicity, defined as the colength of the literal local algebra. -/
def localIntersectionMultiplicity (m n : ℕ) : ℕ :=
  Module.finrank ℂ (LocalIntersectionAlgebra m n)

theorem localIntersectionMultiplicity_eq_mul (m n : ℕ) :
    localIntersectionMultiplicity m n = m * n :=
  finrank_localIntersectionAlgebra m n

/-- Multiplying a local equation by a unit does not change its principal ideal. -/
theorem span_singleton_unit_mul {R : Type*} [CommRing R] (v : Rˣ) (x : R) :
    Ideal.span ({(v : R) * x} : Set R) = Ideal.span {x} := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
  · rintro y (rfl : y = (v : R) * x)
    exact Ideal.mem_span_singleton.2 ⟨(v : R), mul_comm _ _⟩
  · rintro y (rfl : y = x)
    refine Ideal.mem_span_singleton.2 ⟨((v⁻¹ : Rˣ) : R), ?_⟩
    rw [mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- The reduced diagonal contribution left after removing `m` identity copies from the local
product `m²` is the multiplicity charge `m(m-1)`. -/
theorem diagonalReducedMultiplicity_eq (m : ℕ) :
    localIntersectionMultiplicity m m - m = m * (m - 1) := by
  rw [localIntersectionMultiplicity_eq_mul]
  cases m with
  | zero => simp
  | succ m => simp [Nat.succ_mul, Nat.mul_succ]

/-- Closed, premise-free capstone for the local shift-pair intersection calculation. -/
theorem shiftPairLocalIntersectionProductMultiplicity_unconditional :
    (∀ m n : ℕ, localIntersectionMultiplicity m n = m * n) ∧
      (∀ m : ℕ, localIntersectionMultiplicity m m - m = m * (m - 1)) := by
  exact ⟨localIntersectionMultiplicity_eq_mul, diagonalReducedMultiplicity_eq⟩

end
end ShiftPairLocalIntersectionAlgebra
end RHTower
end GaloisForLFunctions
