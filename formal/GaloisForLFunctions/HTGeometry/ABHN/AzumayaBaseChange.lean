/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CentralSimpleAzumaya
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Azumaya algebras and scalar extension

This file proves that an Azumaya algebra over a field remains Azumaya after scalar extension to
another field.  The proof identifies endomorphisms after base change using a finite basis, then
transports the left-right action through the canonical base-changed enveloping-algebra map.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-! ## Endomorphisms after scalar extension -/

/-- Extension of scalars identifies all endomorphisms of a finite-dimensional vector space after
base change. -/
theorem tensorProductEnd_surjective
    {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup A] [Module K A] [Module.Finite K A] :
    Function.Surjective (LinearMap.tensorProductEnd K L A) := by
  classical
  let b := Module.finBasis K A
  let bL := Algebra.TensorProduct.basis L b
  apply LinearMap.range_eq_top.1
  apply top_unique
  rw [← bL.end.span_eq]
  refine Submodule.span_le.2 ?_
  rintro f ⟨ij, rfl⟩
  refine ⟨1 ⊗ₜ[K] b.end ij, ?_⟩
  simp only [LinearMap.tensorProduct, TensorProduct.AlgebraTensorModule.lift_apply,
    TensorProduct.lift.tmul]
  dsimp
  simp only [one_smul, LinearMap.baseChangeHom_apply]
  rw [b.baseChange_end L ij]

/-! ## Base change of the enveloping algebra -/

section

variable {K L A : Type*} [Field K] [Field L] [Algebra K L]
variable [Ring A] [Algebra K A]

local notation "C" => L ⊗[K] A
local notation "P" => C ⊗[L] Cᵐᵒᵖ

/-- The left factor of the base-changed enveloping algebra. -/
noncomputable def leftInEnvelope : A →ₐ[K] P :=
  ((Algebra.TensorProduct.includeLeft : C →ₐ[L] P).restrictScalars K).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[K] C)

/-- The right, opposite factor of the base-changed enveloping algebra. -/
noncomputable def rightInEnvelope : Aᵐᵒᵖ →ₐ[K] P :=
  ((Algebra.TensorProduct.includeRight : Cᵐᵒᵖ →ₐ[L] P).restrictScalars K).comp
    (AlgHom.op (Algebra.TensorProduct.includeRight : A →ₐ[K] C))

/-- The canonical map from the scalar extension of `A ⊗ Aᵐᵒᵖ` to the enveloping algebra of the
scalar extension of `A`. -/
noncomputable def envelopeBaseChangeMap :
    L ⊗[K] (A ⊗[K] Aᵐᵒᵖ) →ₐ[L] P :=
  Algebra.TensorProduct.lift (Algebra.ofId L P)
    (Algebra.TensorProduct.lift (leftInEnvelope (K := K) (L := L))
      (rightInEnvelope (K := K) (L := L))
      fun x y ↦ by
        show ((1 ⊗ₜ[K] x) ⊗ₜ[L] (1 : Cᵐᵒᵖ)) *
          ((1 : C) ⊗ₜ[L] MulOpposite.op (1 ⊗ₜ[K] y.unop)) = _
        exact (Commute.one_right _).tmul (Commute.one_left _))
    fun x y ↦ Algebra.commutes _ _

theorem envelopeBaseChangeMap_tmul (l : L) (a : A) (b : Aᵐᵒᵖ) :
    envelopeBaseChangeMap (K := K) (l ⊗ₜ[K] (a ⊗ₜ[K] b)) =
      (l • (1 ⊗ₜ[K] a)) ⊗ₜ[L] (MulOpposite.op (1 ⊗ₜ[K] b.unop)) := by
  simp only [envelopeBaseChangeMap, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
  change (algebraMap L P l) *
      (((1 ⊗ₜ[K] a) ⊗ₜ[L] (1 : Cᵐᵒᵖ)) *
        ((1 : C) ⊗ₜ[L] MulOpposite.op (1 ⊗ₜ[K] b.unop))) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  simp

theorem mulLeftRight_envelopeBaseChangeMap (t : L ⊗[K] (A ⊗[K] Aᵐᵒᵖ)) :
    AlgHom.mulLeftRight L C (envelopeBaseChangeMap (K := K) t) =
      LinearMap.tensorProductEnd K L A
        ((AlgHom.mulLeftRight K A).toLinearMap.baseChange L t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul l z =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [TensorProduct.tmul_add, map_add]
      simp only [map_add, hx, hy]
    | tmul a b =>
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp [map_add, hx, hy]
      | tmul l' x =>
        rw [envelopeBaseChangeMap_tmul]
        rw [LinearMap.baseChange_tmul]
        simp only [AlgHom.mulLeftRight_apply, LinearMap.tensorProductEnd_apply]
        dsimp
        change (l • (1 ⊗ₜ[K] a)) * (l' ⊗ₜ[K] x) * (1 ⊗ₜ[K] b.unop) =
          l • LinearMap.baseChangeHom K L A A
            (AlgHom.mulLeftRight K A (a ⊗ₜ[K] b)) (l' ⊗ₜ[K] x)
        simp only [LinearMap.baseChangeHom_apply]
        rw [LinearMap.baseChange_tmul, AlgHom.mulLeftRight_apply]
        rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_assoc]
        simp
        rfl

/-! ## Azumaya stability under scalar extension -/

/-- An Azumaya algebra over a field remains Azumaya after arbitrary field scalar extension. -/
theorem isAzumaya_scalarExtension [IsAzumaya K A] : IsAzumaya L C := by
  letI : Nontrivial A := ⟨0, 1, fun h => zero_ne_one <|
    FaithfulSMul.algebraMap_injective K A (by simp [h])⟩
  letI : Nontrivial C := Function.Injective.nontrivial
    (Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective K L))
  refine { bij := ?_ }
  have hsurj : Function.Surjective (AlgHom.mulLeftRight L C) := by
    intro f
    obtain ⟨t, ht⟩ := tensorProductEnd_surjective (K := K) (L := L) (A := A) f
    have hbase : Function.Surjective (AlgHom.mulLeftRight K A).toLinearMap :=
      IsAzumaya.bij.2
    obtain ⟨s, hs⟩ := LinearMap.baseChange_surjective L hbase t
    refine ⟨envelopeBaseChangeMap (K := K) s, ?_⟩
    calc
      AlgHom.mulLeftRight L C (envelopeBaseChangeMap (K := K) s) =
          LinearMap.tensorProductEnd K L A
            ((AlgHom.mulLeftRight K A).toLinearMap.baseChange L s) :=
        mulLeftRight_envelopeBaseChangeMap s
      _ = LinearMap.tensorProductEnd K L A t := congrArg _ hs
      _ = f := ht
  refine ⟨?_, hsurj⟩
  change Function.Injective (AlgHom.mulLeftRight L C).toLinearMap
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr hsurj
  calc
    Module.finrank L (C ⊗[L] Cᵐᵒᵖ) = Module.finrank L C * Module.finrank L Cᵐᵒᵖ :=
      Module.finrank_tensorProduct
    _ = Module.finrank L C * Module.finrank L C := by
      rw [(MulOpposite.opLinearEquiv L).finrank_eq]
    _ = Module.finrank L (Module.End L C) := by
      rw [Module.finrank_linearMap]

/-- Scalar extension of a finite-dimensional central simple algebra is a simple ring. -/
theorem scalarExtension_isSimpleRing {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : CSA K) : IsSimpleRing (L ⊗[K] A.carrier) := by
  letI : IsAzumaya K A.carrier := csa_isAzumaya A
  letI : IsAzumaya L (L ⊗[K] A.carrier) :=
    isAzumaya_scalarExtension (K := K) (L := L) (A := A.carrier)
  exact isSimpleRing_of_isAzumaya (K := L) (L ⊗[K] A.carrier)

end

end GaloisForLFunctions.HTGeometry.ABHN
