import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# An intermediate field inside a larger one

An intermediate field contained in another is the same field whether it is read inside the ambient
field or inside the larger one: pulling it back along the inclusion gives an isomorphic copy, so the
degrees over the base agree.

This is the identification needed to apply a statement proved by the Galois correspondence of a
subextension to a field originally given inside the ambient extension.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **Pulling an intermediate field back along an inclusion gives an isomorphic copy.** -/
noncomputable def comapValEquiv {E K : IntermediateField F L} (hKE : K ≤ E) :
    (IntermediateField.comap E.val K) ≃ₐ[F] K where
  toFun x := ⟨(x : L), x.2⟩
  invFun y := ⟨⟨(y : L), hKE y.2⟩, y.2⟩
  left_inv x := by
    refine Subtype.ext (Subtype.ext ?_)
    rfl
  right_inv y := by
    refine Subtype.ext ?_
    rfl
  map_mul' x y := by
    refine Subtype.ext ?_
    rfl
  map_add' x y := by
    refine Subtype.ext ?_
    rfl
  commutes' c := by
    refine Subtype.ext ?_
    rfl

/-- **The degrees agree.** -/
theorem finrank_comap_val {E K : IntermediateField F L} (hKE : K ≤ E) :
    Module.finrank F (IntermediateField.comap E.val K) = Module.finrank F K :=
  (comapValEquiv hKE).toLinearEquiv.finrank_eq

end GaloisForLFunctions.HTGeometry
