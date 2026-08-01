import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# A field is relatively algebraically closed in its field of rational functions

A rational function algebraic over the constants is integral over the polynomial ring, and the
polynomial ring is integrally closed, so it is a polynomial.  A polynomial algebraic over the
constants is constant, since a nonzero polynomial composed with a nonconstant one is nonzero.

So adjoining a rational function that is not constant adds a transcendental, and the constants are
exactly the algebraic elements.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F]

/-- **A polynomial algebraic over the constants is constant.** -/
theorem eq_C_of_isAlgebraic {f : Polynomial F} (hf : IsAlgebraic F f) :
    f = Polynomial.C (f.coeff 0) := by
  obtain ⟨P, hP0, hPf⟩ := hf
  have h : P.comp f = 0 := by
    rw [Polynomial.comp_eq_aeval]
    exact hPf
  rcases Polynomial.comp_eq_zero_iff.1 h with h1 | ⟨-, h2⟩
  · exact absurd h1 hP0
  · exact h2

/-- **A rational function algebraic over the constants is constant.** -/
theorem exists_algebraMap_eq_of_isAlgebraic {u : FractionRing (Polynomial F)}
    (hu : IsAlgebraic F u) :
    ∃ a : F, algebraMap F (FractionRing (Polynomial F)) a = u := by
  have hint : IsIntegral (Polynomial F) u := IsIntegral.tower_top hu.isIntegral
  obtain ⟨f, hf⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hinj : Function.Injective
      (algebraMap (Polynomial F) (FractionRing (Polynomial F))) :=
    IsFractionRing.injective _ _
  have hfalg : IsAlgebraic F f := by
    rw [← isAlgebraic_algebraMap_iff (A := FractionRing (Polynomial F)) hinj, hf]
    exact hu
  refine ⟨f.coeff 0, ?_⟩
  rw [IsScalarTower.algebraMap_apply F (Polynomial F) (FractionRing (Polynomial F)),
    Polynomial.algebraMap_eq, ← eq_C_of_isAlgebraic hfalg, hf]

/-- **The constants are exactly the algebraic elements of the field of rational functions.** -/
theorem isAlgebraic_iff_exists_algebraMap_eq (u : FractionRing (Polynomial F)) :
    IsAlgebraic F u ↔ ∃ a : F, algebraMap F (FractionRing (Polynomial F)) a = u := by
  refine ⟨exists_algebraMap_eq_of_isAlgebraic, ?_⟩
  rintro ⟨a, rfl⟩
  exact isAlgebraic_algebraMap a

end GaloisForLFunctions.HTGeometry
