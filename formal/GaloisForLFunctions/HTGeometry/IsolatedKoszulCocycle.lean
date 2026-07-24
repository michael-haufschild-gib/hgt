import GaloisForLFunctions.HTGeometry.KoszulCohomology

/-!
# Cocycles of the isolated Koszul complex are the diagonal-free vectors

For the isolated (fully discrete) Stanley–Reisner boundary model, a coefficient vector
`a : Fin (n+2) → isolatedBoundarySubring` is a first Koszul cycle exactly when each `a k` has zero
`k`-th axis component.  Indeed the Koszul relation `Σ aᵢ xᵢ` reads off on axis `k` as `(a k)ₖ · X`
(the isolated axes multiply to zero off-diagonal, `isolatedBoundaryX_mul_eq_zero`), so it vanishes
iff every diagonal component `(a k)ₖ` vanishes.

This characterization of the cocycle space is the algebraic input for computing the exact first
Koszul cohomology rank, i.e. the algebraic side of the degree-0 Hochster identity matching the
combinatorial reduced `H̃⁰`.
-/

namespace GaloisForLFunctions

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] {n : ℕ}

/-- The Koszul relation reads off on axis `k` as `(a k)ₖ · X`. -/
theorem isolatedKoszulRelation_val_apply (a : Fin (n + 2) → isolatedBoundarySubring F n)
    (k : Fin (n + 2)) :
    (isolatedKoszulRelation a : Fin (n + 2) → Polynomial F) k
      = (a k : Fin (n + 2) → Polynomial F) k * Polynomial.X := by
  simp only [isolatedKoszulRelation, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply,
    MulMemClass.coe_mul, Pi.mul_apply, isolatedBoundaryX_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ k
    (fun i => (a i : Fin (n + 2) → Polynomial F) k * Polynomial.X)]
  simp

/-- **The isolated Koszul cocycles are the diagonal-free vectors.**  `Σ aᵢ xᵢ = 0` iff every axis
component `(a k)ₖ` vanishes. -/
theorem isolatedKoszulRelation_eq_zero_iff (a : Fin (n + 2) → isolatedBoundarySubring F n) :
    isolatedKoszulRelation a = 0 ↔ ∀ k, (a k : Fin (n + 2) → Polynomial F) k = 0 := by
  rw [← Subtype.coe_inj, ZeroMemClass.coe_zero, funext_iff]
  refine forall_congr' (fun k => ?_)
  rw [Pi.zero_apply, isolatedKoszulRelation_val_apply, mul_eq_zero,
    or_iff_left Polynomial.X_ne_zero]

end

end GaloisForLFunctions
