import GaloisForLFunctions.HTGeometry.TensorProductAlgClosedFieldDomain
import GaloisForLFunctions.HTGeometry.TensorFractionRingDomain
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraHomEquality
import Mathlib.FieldTheory.Galois.Basic

/-!
# Galois extensions under algebraically closed constant-field extension

Let `k` be algebraically closed, let `F/k` be a field, and let `E/F` be finite Galois.
For every field extension `K/k`, the tensor products with `K` are domains.  After passing the
base tensor to its fraction field, the scalar extension of `E` is therefore a field.  This file
proves that it is again Galois and that scalar extension gives an isomorphism of Galois groups.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- Fraction field of the compositum tensor `F ⊗[k] K`. -/
abbrev constantScalarBase (k F K : Type*) [Field k] [Field F] [Field K]
    [Algebra k F] [Algebra k K] :=
  FractionRing (F ⊗[k] K)

/-- Scalar extension of `E/F` to the fraction field of `F ⊗[k] K`. -/
abbrev constantScalarExtension (k F E K : Type*) [Field k] [Field F] [Field E]
    [Field K] [Algebra k F] [Algebra k K] [Algebra F E] :=
  constantScalarBase k F K ⊗[F] E

/-- Two fields over an algebraically closed common constant field have domain tensor product. -/
noncomputable instance constantTensorProduct_isDomain
    (k F K : Type*) [Field k] [IsAlgClosed k] [Field F] [Field K]
    [Algebra k F] [Algebra k K] : IsDomain (F ⊗[k] K) :=
  isDomain_tensorProduct_of_fields

private theorem isDomain_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain B] (e : A ≃+* B) : IsDomain A := by
  have h01 : (0 : A) ≠ 1 := by
    intro h
    have : (0 : B) = 1 := by rw [← e.map_zero, ← e.map_one, h]
    exact zero_ne_one this
  letI : Nontrivial A := ⟨⟨0, 1, h01⟩⟩
  letI : NoZeroDivisors A := ⟨by
    intro a b hab
    have : e a * e b = 0 := by simpa using congrArg e hab
    rcases mul_eq_zero.mp this with ha | hb
    · exact Or.inl (e.injective (by simpa using ha))
    · exact Or.inr (e.injective (by simpa using hb))⟩
  exact NoZeroDivisors.to_isDomain A

variable {k F E K : Type*} [Field k] [IsAlgClosed k]
  [Field F] [Field E] [Field K]
  [Algebra k F] [Algebra k K] [Algebra F E] [Algebra k E]
  [IsScalarTower k F E]

/-- The unlocalized right scalar extension is a domain. -/
theorem constantRightTensor_isDomain : IsDomain (E ⊗[F] (F ⊗[k] K)) := by
  exact isDomain_of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange k F E E K).toRingEquiv

/-- Localizing the right scalar extension at the nonzero base tensors preserves its domain. -/
theorem constantRightFractionTensor_isDomain :
    IsDomain (E ⊗[F] constantScalarBase k F K) := by
  letI : IsDomain (E ⊗[F] (F ⊗[k] K)) := constantRightTensor_isDomain
  exact isDomain_tensor_of_isFractionRing
    (k := F) (P := F ⊗[k] K) (Q := constantScalarBase k F K) (F := E)

/-- The standard left scalar extension is a domain. -/
theorem constantScalarExtension_isDomain :
    IsDomain (constantScalarExtension k F E K) := by
  letI : IsDomain (E ⊗[F] constantScalarBase k F K) :=
    constantRightFractionTensor_isDomain
  exact isDomain_of_ringEquiv
    (Algebra.TensorProduct.comm F (constantScalarBase k F K) E).toRingEquiv

/-- A finite scalar extension which is a domain has its canonical field structure. -/
@[implicit_reducible] noncomputable instance constantScalarExtensionField
    [FiniteDimensional F E] : Field (constantScalarExtension k F E K) := by
  letI : FiniteDimensional (constantScalarBase k F K)
      (constantScalarExtension k F E K) := inferInstance
  letI : IsDomain (constantScalarExtension k F E K) :=
    constantScalarExtension_isDomain
  letI : IsArtinianRing (constantScalarExtension k F E K) :=
    isArtinian_of_tower (constantScalarBase k F K) inferInstance
  exact IsField.toField (IsArtinianRing.isField_of_isDomain _)

/-- Scalar extension of automorphisms as a group homomorphism. -/
noncomputable def constantGaloisBaseChange [FiniteDimensional F E] :
    Gal(E/F) →*
      (constantScalarExtension k F E K ≃ₐ[constantScalarBase k F K]
        constantScalarExtension k F E K) where
  toFun e := ABHN.algEquivBaseChange (L := constantScalarBase k F K) e
  map_one' := by
    apply AlgEquiv.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [ABHN.algEquivBaseChange]
    | add x y hx hy => simpa using congrArg₂ (.+.) hx hy
  map_mul' e f := by
    apply AlgEquiv.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [ABHN.algEquivBaseChange]
    | add x y hx hy => simpa using congrArg₂ (.+.) hx hy

/-- Scalar extension does not identify distinct automorphisms. -/
theorem constantGaloisBaseChange_injective [FiniteDimensional F E] :
    Function.Injective
      (constantGaloisBaseChange (k := k) (F := F) (E := E) (K := K)) := by
  intro e f h
  exact (ABHN.algEquiv_eq_iff_baseChange_eq
    (L := constantScalarBase k F K) e f).mpr h

private theorem natCard_gal_le_finrank
    (A B : Type*) [Field A] [Field B] [Algebra A B] [FiniteDimensional A B] :
    Nat.card Gal(B/A) ≤ Module.finrank A B := by
  let H : Subgroup Gal(B/A) := ⊤
  have hFixed := IntermediateField.finrank_fixedField_eq_card H
  have hTower := Module.finrank_mul_finrank A (IntermediateField.fixedField H) B
  rw [hFixed] at hTower
  calc
    Nat.card Gal(B/A) = 1 * Nat.card Gal(B/A) := by simp
    _ ≤ Module.finrank A (IntermediateField.fixedField H) * Nat.card Gal(B/A) := by
      exact Nat.mul_le_mul_right _
        (Module.finrank_pos (R := A) (M := IntermediateField.fixedField H))
    _ = Module.finrank A B := by simpa [H] using hTower

/-- Finite Galois extensions remain Galois after arbitrary extension of algebraically closed
constants. -/
theorem constantScalarExtension_isGalois
    [FiniteDimensional F E] [IsGalois F E] :
    IsGalois (constantScalarBase k F K) (constantScalarExtension k F E K) := by
  letI : FiniteDimensional (constantScalarBase k F K)
      (constantScalarExtension k F E K) := inferInstance
  apply IsGalois.of_card_aut_eq_finrank
  apply le_antisymm
  · exact natCard_gal_le_finrank _ _
  · rw [Module.finrank_baseChange, ← IsGalois.card_aut_eq_finrank F E]
    exact Nat.card_le_card_of_injective
      (constantGaloisBaseChange (k := k) (F := F) (E := E) (K := K))
      constantGaloisBaseChange_injective

/-- Base change induces an isomorphism of Galois groups; algebraically closed constant extension
creates no new automorphisms. -/
noncomputable def constantGaloisBaseChangeEquiv
    [FiniteDimensional F E] [IsGalois F E] :
    Gal(E/F) ≃*
      (constantScalarExtension k F E K ≃ₐ[constantScalarBase k F K]
        constantScalarExtension k F E K) := by
  letI : FiniteDimensional (constantScalarBase k F K)
      (constantScalarExtension k F E K) := inferInstance
  letI : IsGalois (constantScalarBase k F K) (constantScalarExtension k F E K) :=
    constantScalarExtension_isGalois
  exact MulEquiv.ofBijective
    (constantGaloisBaseChange (k := k) (F := F) (E := E) (K := K))
    ((Fintype.bijective_iff_injective_and_card
      (constantGaloisBaseChange (k := k) (F := F) (E := E) (K := K))).mpr ⟨
        constantGaloisBaseChange_injective,
        by
          rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
            IsGalois.card_aut_eq_finrank F E,
            IsGalois.card_aut_eq_finrank (constantScalarBase k F K)
              (constantScalarExtension k F E K), Module.finrank_baseChange]⟩)

end

end GaloisForLFunctions.HTGeometry
