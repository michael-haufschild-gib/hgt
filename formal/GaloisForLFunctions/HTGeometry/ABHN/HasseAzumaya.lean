/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/

import GaloisForLFunctions.HTGeometry.ABHN.AzumayaScalarExtension
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapBaseChange

/-!
# Hasse detection for Azumaya algebras

For finite-dimensional algebras over a field, Azumaya-ness is reflected by every field scalar
extension.  Thus an algebra over either global-field model is Azumaya exactly when all of its
completed scalar extensions are Azumaya.  This is a genuine local-global descent theorem for the
Azumaya condition; it is independent of the still-missing local class-field-theory invariant.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- If a finite-dimensional algebra becomes Azumaya after a field scalar extension, then it was
already Azumaya. -/
theorem isAzumaya_of_scalarExtension
    {K : Type u} {L : Type v} {A : Type w} [Field K] [Field L] [Algebra K L]
    [Ring A] [Algebra K A] [Module.Finite K A] [IsAzumaya L (L ⊗[K] A)] :
    IsAzumaya K A := by
  letI : Nontrivial (L ⊗[K] A) := ⟨0, 1, fun h => zero_ne_one <|
    FaithfulSMul.algebraMap_injective L (L ⊗[K] A) (by
      simpa only [map_zero, map_one] using h)⟩
  letI : Nontrivial A := ⟨0, 1, fun h => zero_ne_one <| by
    calc
      (0 : L ⊗[K] A) = (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) 0 :=
        (map_zero _).symm
      _ = (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) 1 := congrArg _ h
      _ = 1 := map_one _⟩
  letI : FaithfulSMul K A := by infer_instance
  letI : Module.Projective K A := by infer_instance
  refine { bij := ?_ }
  have hcomp : Function.Surjective fun t =>
      AlgHom.mulLeftRight L (L ⊗[K] A)
        (AzumayaScalarExtension.envelopeBaseChangeMap (R := K) (S := L) (A := A) t) :=
    IsAzumaya.bij.2.comp
      (AzumayaScalarExtension.envelopeBaseChangeMap_surjective (R := K) (S := L) (A := A))
  have hend : Function.Bijective (LinearMap.tensorProductEnd K L A) :=
    tensorProductEnd_bijective_of_projective (R := K) (S := L) (M := A)
  have hbase : Function.Surjective ((AlgHom.mulLeftRight K A).toLinearMap.baseChange L) := by
    intro x
    obtain ⟨t, ht⟩ := hcomp (LinearMap.tensorProductEnd K L A x)
    refine ⟨t, ?_⟩
    apply hend.1
    rw [← AzumayaScalarExtension.mulLeftRight_envelopeBaseChangeMap
      (R := K) (S := L) (A := A)]
    exact ht
  have hbase' : Function.Surjective (AlgHom.mulLeftRight K A).toLinearMap :=
    (linearMap_surjective_iff_baseChange_surjective
      (L := L) (AlgHom.mulLeftRight K A).toLinearMap).mpr hbase
  refine ⟨?_, hbase'⟩
  change Function.Injective (AlgHom.mulLeftRight K A).toLinearMap
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr hbase'
  calc
    Module.finrank K (A ⊗[K] Aᵐᵒᵖ) = Module.finrank K A * Module.finrank K Aᵐᵒᵖ :=
      Module.finrank_tensorProduct
    _ = Module.finrank K A * Module.finrank K A := by
      rw [(MulOpposite.opLinearEquiv K).finrank_eq]
    _ = Module.finrank K (Module.End K A) := by
      rw [Module.finrank_linearMap]

/-- Azumaya-ness of a finite-dimensional field algebra is invariant under field scalar
extension. -/
theorem isAzumaya_iff_tensorProduct_isAzumaya
    {K : Type u} {L : Type v} {A : Type w} [Field K] [Field L] [Algebra K L]
    [Ring A] [Algebra K A] [Module.Finite K A] :
    IsAzumaya K A ↔ IsAzumaya L (L ⊗[K] A) := by
  constructor
  · intro h
    letI := h
    exact AzumayaScalarExtension.isAzumaya_scalarExtension (R := K) (S := L) (A := A)
  · intro h
    letI := h
    exact isAzumaya_of_scalarExtension (K := K) (L := L) (A := A)

/-- A finite-dimensional algebra over a number field is Azumaya exactly when every completed
scalar extension is Azumaya. -/
theorem numberField_isAzumaya_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [Ring A] [Algebra K A] [Module.Finite K A] :
    IsAzumaya K A ↔ ∀ p : NumberFieldPlace K,
      IsAzumaya (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h p
    exact (isAzumaya_iff_tensorProduct_isAzumaya (L := completion K p)).mp h
  · intro h
    exact (isAzumaya_iff_tensorProduct_isAzumaya
      (L := completion K (witnessPlace K))).mpr (h (witnessPlace K))

/-- A finite-dimensional algebra over `F(t)` is Azumaya exactly when every finite and infinite
completed scalar extension is Azumaya. -/
theorem rationalFunction_isAzumaya_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [Ring A] [Algebra (RatFunc F) A]
    [Module.Finite (RatFunc F) A] :
    IsAzumaya (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      IsAzumaya (rationalFunctionCompletion F p) (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h p
    exact (isAzumaya_iff_tensorProduct_isAzumaya
      (L := rationalFunctionCompletion F p)).mp h
  · intro h
    exact (isAzumaya_iff_tensorProduct_isAzumaya
      (L := rationalFunctionCompletion F .infinite)).mpr (h .infinite)

/-- For a finite-dimensional number-field algebra, Azumaya-ness is already detected at any one
completed scalar extension.  This is the existential form of Hasse detection for the Azumaya
criterion. -/
theorem numberField_isAzumaya_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [Ring A] [Algebra K A] [Module.Finite K A] :
    IsAzumaya K A ↔ ∃ p : NumberFieldPlace K,
      IsAzumaya (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (isAzumaya_iff_tensorProduct_isAzumaya (L := completion K (witnessPlace K))).mp h⟩
  · rintro ⟨p, hp⟩
    exact isAzumaya_of_scalarExtension (K := K) (L := completion K p) (A := A)

/-- For a finite-dimensional algebra over a rational function field, Azumaya-ness is already
detected at one finite or infinite completed scalar extension. -/
theorem rationalFunction_isAzumaya_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [Ring A] [Algebra (RatFunc F) A]
    [Module.Finite (RatFunc F) A] :
    IsAzumaya (RatFunc F) A ↔ ∃ p : RationalFunctionPlace F,
      IsAzumaya (rationalFunctionCompletion F p) (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (isAzumaya_iff_tensorProduct_isAzumaya
        (L := rationalFunctionCompletion F .infinite)).mp h⟩
  · rintro ⟨p, hp⟩
    exact isAzumaya_of_scalarExtension (K := RatFunc F)
      (L := rationalFunctionCompletion F p) (A := A)

end GaloisForLFunctions.HTGeometry.ABHN
