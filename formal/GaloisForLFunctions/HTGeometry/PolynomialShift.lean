import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Shifting the variable of a polynomial

Substituting `X + a` for `X` is an algebra automorphism of the polynomial ring, with inverse the
substitution of `X - a`.  It carries the linear factor at `c + a` to the linear factor at `c`, so it
transports divisibility by powers of linear factors, hence root multiplicities:

```text
rootMultiplicity c (p(X + a)) = rootMultiplicity (c + a) p.
```

This is what moves a pole orbit by one step, which is the reindexing the telescoped difference of a
rational function performs.
-/

open scoped BigOperators

namespace GaloisForLFunctions

open Polynomial

/-- Substituting `X + a` for the variable, as an algebra automorphism. -/
noncomputable def polyShift (a : ℂ) : Polynomial ℂ ≃ₐ[ℂ] Polynomial ℂ :=
  AlgEquiv.ofAlgHom (aeval (X + C a)) (aeval (X - C a))
    (by
      refine algHom_ext ?_
      simp)
    (by
      refine algHom_ext ?_
      simp)

@[simp] theorem polyShift_apply (a : ℂ) (p : Polynomial ℂ) :
    polyShift a p = aeval (X + C a) p := rfl

@[simp] theorem polyShift_X (a : ℂ) : polyShift a X = X + C a := by
  rw [polyShift_apply, aeval_X]

theorem polyShift_sub_C (a c : ℂ) : polyShift a (X - C (c + a)) = X - C c := by
  rw [polyShift_apply, map_sub, aeval_X, aeval_C, Polynomial.algebraMap_eq, C_add]
  ring

/-- **Shifting moves root multiplicities along the orbit.** -/
theorem rootMultiplicity_polyShift (a : ℂ) {p : Polynomial ℂ} (hp : p ≠ 0) (c : ℂ) :
    (polyShift a p).rootMultiplicity c = p.rootMultiplicity (c + a) := by
  have hshift : polyShift a p ≠ 0 := by
    intro hcon
    exact hp ((polyShift a).injective (by rw [hcon, map_zero]))
  have hkey : ∀ n : ℕ, ((X - C c) ^ n ∣ polyShift a p) ↔ ((X - C (c + a)) ^ n ∣ p) := by
    intro n
    rw [← polyShift_sub_C a c, ← map_pow]
    exact map_dvd_iff (polyShift a)
  refine le_antisymm ?_ ?_
  · rw [le_rootMultiplicity_iff hp, ← hkey]
    exact (le_rootMultiplicity_iff hshift).mp le_rfl
  · rw [le_rootMultiplicity_iff hshift, hkey]
    exact (le_rootMultiplicity_iff hp).mp le_rfl

end GaloisForLFunctions
