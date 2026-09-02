import GaloisForLFunctions.HTGeometry.AlgebraicTensorEigenvectorDescent
import GaloisForLFunctions.HTGeometry.HyperexponentialPrimitive
import GaloisForLFunctions.HTGeometry.IntermediateFieldTensorFraction

/-!
# Rank-one derivation descent from a concrete compositum

This module transports tensor-fraction eigenvector descent to two linearly disjoint intermediate
fields in a common differential overfield.  The derivation acts on the left field and fixes the
right field.  Algebraic eigenvectors over their compositum therefore descend to the left field.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Tensor multiplication intertwines the left tensor derivation with an ambient derivation which
restricts to the chosen derivation on the left field and kills the right field. -/
theorem intermediateFieldTensorMulMap_tensorLeftDerivation
    (C E : Type*) [Field C] [Field E] [Algebra C E]
    (A B : IntermediateField C E)
    (D : Derivation C A A) (DE : Derivation C E E)
    (hleft : ∀ a : A, DE (a : E) = (D a : A))
    (hright : ∀ b : B, DE (b : E) = 0)
    (x : A ⊗[C] B) :
    DE (GaloisForLFunctions.intermediateFieldTensorMulMap C E A B x) =
      GaloisForLFunctions.intermediateFieldTensorMulMap C E A B
        (tensorLeftDerivation C A B D x) := by
  induction x with
  | zero => simp
  | tmul a b =>
      rw [tensorLeftDerivation_tmul]
      simp only [GaloisForLFunctions.intermediateFieldTensorMulMap_tmul,
        Derivation.leibniz, smul_eq_mul, hleft, hright, mul_zero, zero_add]
      ring
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A derivation preserving each factor preserves their compositum. -/
theorem derivation_mem_intermediateField_sup
    (C E : Type*) [Field C] [Field E] [Algebra C E]
    (A B : IntermediateField C E) (DE : Derivation C E E)
    (hA : ∀ a : A, DE (a : E) ∈ A)
    (hB : ∀ b : B, DE (b : E) ∈ B)
    {x : E} (hx : x ∈ A ⊔ B) : DE x ∈ A ⊔ B := by
  rw [IntermediateField.sup_def] at hx
  apply IntermediateField.adjoin_induction C
      (s := ((A : Set E) ∪ (B : Set E)))
      (p := fun y _ => DE y ∈ IntermediateField.adjoin C
        ((A : Set E) ∪ (B : Set E)))
  · rintro y (hy | hy)
    · exact IntermediateField.subset_adjoin C _ (Or.inl (hA ⟨y, hy⟩))
    · exact IntermediateField.subset_adjoin C _ (Or.inr (hB ⟨y, hy⟩))
  · intro c
    rw [DE.map_algebraMap]
    exact (IntermediateField.adjoin C _).zero_mem
  · intro x y hx hy hDx hDy
    rw [map_add]
    exact (IntermediateField.adjoin C _).add_mem hDx hDy
  · intro x hx hDx
    rw [Derivation.leibniz_inv]
    exact (IntermediateField.adjoin C _).mul_mem
      ((IntermediateField.adjoin C _).neg_mem
        (by
          simpa [pow_two] using
            ((IntermediateField.adjoin C _).mul_mem
              ((IntermediateField.adjoin C _).inv_mem hx)
              ((IntermediateField.adjoin C _).inv_mem hx)))) hDx
  · intro x y hx hy hDx hDy
    rw [Derivation.leibniz]
    exact (IntermediateField.adjoin C _).add_mem
      ((IntermediateField.adjoin C _).mul_mem hx hDy)
      ((IntermediateField.adjoin C _).mul_mem hy hDx)
  exact hx

/-- **Concrete-compositum eigenvector descent.**  A nonzero algebraic eigenvector over a linearly
disjoint compositum descends to the left field when the ambient derivation acts only there. -/
theorem exists_left_eigenvector_of_algebraic_intermediateField_sup
    (C E : Type*) [Field C] [IsAlgClosed C] [CharZero C]
    [Field E] [Algebra C E]
    (A B : IntermediateField C E) [IsAlgClosed A]
    (hAB : A.LinearDisjoint B)
    (D : Derivation C A A) (DE : Derivation C E E)
    (hleft : ∀ a : A, DE (a : E) = (D a : A))
    (hright : ∀ b : B, DE (b : E) = 0)
    (q : A) {u : E}
    (hu : IsAlgebraic ↥(A ⊔ B) u) (hu0 : u ≠ 0)
    (hDu : DE u = (q : E) * u) :
    ∃ v : A, v ≠ 0 ∧ D v = q * v := by
  let T := A ⊗[C] B
  let mu := GaloisForLFunctions.intermediateFieldTensorSupMap C E A B
  letI : IsDomain (A ⊗[C] B) := isDomain_tensorProduct_of_fields
  letI : Algebra (A ⊗[C] B) ↥(A ⊔ B) := mu.toRingHom.toAlgebra
  letI : IsScalarTower C (A ⊗[C] B) ↥(A ⊔ B) := IsScalarTower.of_algebraMap_eq
      (R := C) (S := A ⊗[C] B) (A := ↥(A ⊔ B)) (fun c => by
    apply Subtype.ext
    change algebraMap C E c =
      GaloisForLFunctions.intermediateFieldTensorMulMap C E A B
        ((algebraMap C A c) ⊗ₜ[C] (1 : B))
    simp)
  letI : IsFractionRing (A ⊗[C] B) ↥(A ⊔ B) :=
    GaloisForLFunctions.intermediateFieldTensorSup_isFractionRing C E A B hAB
  have hstable : ∀ x : E, x ∈ A ⊔ B → DE x ∈ A ⊔ B := by
    intro x hx
    apply derivation_mem_intermediateField_sup C E A B DE
      (fun a => by rw [hleft]; exact (D a).property)
      (fun b => by rw [hright]; exact B.zero_mem)
      hx
  let DKambient : Derivation C ↥(A ⊔ B) ↥(A ⊔ B) :=
    restrictDerivation DE (A ⊔ B) hstable
  let DKtensor : Derivation C ↥(A ⊔ B) ↥(A ⊔ B) :=
    tensorFieldsFractionDerivation C A B ↥(A ⊔ B) D
  have hderiv : DKambient = DKtensor := by
    apply GaloisForLFunctions.fractionRing_derivation_ext
      (K := C) (A := T) (F := ↥(A ⊔ B))
    intro (x : T)
    apply Subtype.ext
    have hDK : DKtensor (mu x) =
        mu (tensorLeftDerivation C A B D x) := by
      exact tensorFieldsFractionDerivation_algebraMap
        C A B ↥(A ⊔ B) D x
    change DE ((mu x : ↥(A ⊔ B)) : E) =
      ((DKtensor (mu x) : ↥(A ⊔ B)) : E)
    rw [hDK]
    change DE (GaloisForLFunctions.intermediateFieldTensorMulMap C E A B x) =
      GaloisForLFunctions.intermediateFieldTensorMulMap C E A B
        (tensorLeftDerivation C A B D x)
    exact intermediateFieldTensorMulMap_tensorLeftDerivation
      C E A B D DE hleft hright x
  apply exists_left_eigenvector_of_algebraic_tensor_fraction
    C A B ↥(A ⊔ B) E D DE
  · intro x
    change DE (x : E) = ((DKtensor x : ↥(A ⊔ B)) : E)
    rw [← hderiv]
    rfl
  · exact hu
  · exact hu0
  · change DE u = ((mu (q ⊗ₜ[C] (1 : B)) : ↥(A ⊔ B)) : E) * u
    rw [hDu]
    congr 1
    simp [mu]

end

end GaloisForLFunctions.HTGeometry
