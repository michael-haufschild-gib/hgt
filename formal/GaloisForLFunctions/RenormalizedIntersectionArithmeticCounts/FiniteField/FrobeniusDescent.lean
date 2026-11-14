import GaloisForLFunctions.HTGeometry.GaloisFixedByAll
import Mathlib.FieldTheory.Finite.Extension

/-!
# Descent along finite-field embeddings

The image of a finite-field embedding is precisely the fixed set of the
corresponding arithmetic Frobenius power. This identifies actual elements,
so coordinatewise descent and fixed-point counts can use the same equivalence.
-/

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open FiniteField
variable (F K E : Type*) [Field F] [Field K] [Field E]
  [Fintype F] [Fintype K] [Finite E] [Algebra F K] [Algebra F E]


/-- An arithmetic Frobenius power is the corresponding power map. -/
theorem finiteField_frobenius_pow_apply (n : ℕ) (x : E) :
    (frobeniusAlgEquivOfAlgebraic F E ^ n) x = x ^ (Fintype.card F ^ n) := by
  rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate]

/-- The fixed field of arithmetic Frobenius is the given base field. -/
theorem finiteField_frobenius_fixed_iff (x : E) :
    frobeniusAlgEquivOfAlgebraic F E x = x ↔ ∃ a : F, algebraMap F E a = x := by
  constructor
  · intro hx
    apply GaloisForLFunctions.HTGeometry.exists_algebraMap_of_forall_fixed
    intro σ
    obtain ⟨n, rfl⟩ := (bijective_frobeniusAlgEquivOfAlgebraic_pow F E).surjective σ
    have hp (k : ℕ) : (frobeniusAlgEquivOfAlgebraic F E ^ k) x = x := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ', AlgEquiv.mul_apply, ih, hx]
    exact hp n.val
  · rintro ⟨a, rfl⟩
    exact (frobeniusAlgEquivOfAlgebraic F E).commutes a

/-- An embedded finite field is exactly the fixed field of its degree's Frobenius power. -/
theorem finiteField_frobenius_pow_fixed_iff (e : K →ₐ[F] E) (x : E) :
    (frobeniusAlgEquivOfAlgebraic F E ^ Module.finrank F K) x = x ↔
      ∃ a : K, e a = x := by
  letI : Algebra K E := e.toRingHom.toAlgebra
  have hc : Fintype.card F ^ Module.finrank F K = Fintype.card K :=
    Module.card_eq_pow_finrank.symm
  rw [finiteField_frobenius_pow_apply, hc]
  exact finiteField_frobenius_fixed_iff K E x

/-- The embedded field, with its actual elements, parametrizes all Frobenius fixed elements. -/
def finiteFieldFrobeniusFixedEquiv (e : K →ₐ[F] E) :
    K ≃ {x : E // (frobeniusAlgEquivOfAlgebraic F E ^ Module.finrank F K) x = x} :=
  Equiv.ofBijective
    (fun a => ⟨e a, (finiteField_frobenius_pow_fixed_iff F K E e (e a)).mpr ⟨a, rfl⟩⟩)
    ⟨fun a b h => e.injective (congrArg Subtype.val h), fun x => by
      obtain ⟨a, ha⟩ := (finiteField_frobenius_pow_fixed_iff F K E e x.val).mp x.property
      exact ⟨a, Subtype.ext ha⟩⟩

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
