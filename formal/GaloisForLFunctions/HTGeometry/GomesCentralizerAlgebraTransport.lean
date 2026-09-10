import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Transporting full centralizers through algebra equivalences

These equivalences preserve every commuting element, so later operator models can
classify full symmetry algebras through a change of coordinates.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

variable (R : Type*) [CommSemiring R]
variable {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- Membership in a singleton centralizer is the exact commutation equation. -/
theorem gomesCentralizerSingleton_mem_iff (a x : A) :
    x ∈ Subalgebra.centralizer R {a} ↔ a * x = x * a := by
  simp only [Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]

/-- An algebra equivalence transports the full centralizer of every element. -/
def gomesCentralizerTransportEquiv (e : A ≃ₐ[R] B) (a : A) :
    (Subalgebra.centralizer R {a}) ≃ₐ[R] (Subalgebra.centralizer R {e a}) where
  toFun x := ⟨e x.val, by
    rw [gomesCentralizerSingleton_mem_iff]
    have hx := (gomesCentralizerSingleton_mem_iff R a x.val).mp x.property
    simpa only [map_mul] using congrArg e hx⟩
  invFun x := ⟨e.symm x.val, by
    rw [gomesCentralizerSingleton_mem_iff]
    have hx := (gomesCentralizerSingleton_mem_iff R (e a) x.val).mp x.property
    simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm hx⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)
  map_mul' x y := Subtype.ext (map_mul e x.val y.val)
  map_add' x y := Subtype.ext (map_add e x.val y.val)
  commutes' r := Subtype.ext (e.commutes r)

/-- Transport evaluates to the original algebra equivalence on each actual symmetry. -/
theorem gomesCentralizerTransportEquiv_apply (e : A ≃ₐ[R] B) (a : A)
    (x : Subalgebra.centralizer R {a}) :
    (gomesCentralizerTransportEquiv R e a x).val = e x.val := rfl

end GaloisForLFunctions.HTGeometry
