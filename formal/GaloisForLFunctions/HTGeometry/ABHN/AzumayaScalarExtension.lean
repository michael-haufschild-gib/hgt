/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaEndBaseChange
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Support
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Scalar extension of the left-right Azumaya map

This file proves the algebraic core of stability of Azumaya algebras under scalar extension:
the left-right map of an Azumaya algebra remains bijective after arbitrary commutative-ring base
change. It also proves the finite-projective faithful-flatness bridge needed to recover the full
Azumaya statement.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN.AzumayaScalarExtension

open scoped TensorProduct

variable {R S A : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [Ring A] [Algebra R A]

local notation "C" => S ⊗[R] A
local notation "P" => C ⊗[S] Cᵐᵒᵖ

/-- A faithfully flat module carries a faithful scalar action. This form does not require the
module to be commutative as an algebra. -/
theorem faithfullyFlat_faithfulSMul {T M : Type*} [CommRing T] [AddCommGroup M] [Module T M]
    [Module.FaithfullyFlat T M] : FaithfulSMul T M := by
  constructor
  intro r s h
  let f : T →ₗ[T] T := LinearMap.lsmul T T (r - s)
  have hzero : f.lTensor M = 0 := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul m x =>
      change m ⊗ₜ[T] ((r - s) * x) = 0
      rw [← smul_eq_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rw [sub_smul, h m, sub_self]
      simp
  have hf : f = 0 := (Module.FaithfullyFlat.zero_iff_lTensor_zero T M f).mpr hzero
  have hrs : r - s = 0 := by
    simpa [f] using congrArg (fun q : T →ₗ[T] T => q 1) hf
  exact sub_eq_zero.mp hrs

/-- A finite projective faithful module is faithfully flat. Its support is all of `Spec R`, so a
maximal ideal cannot generate the entire module. -/
theorem faithfullyFlat_of_finite_projective_faithful {T M : Type*} [CommRing T]
    [AddCommGroup M] [Module T M] [Module.Projective T M] [Module.Finite T M]
    [FaithfulSMul T M] : Module.FaithfullyFlat T M := by
  refine { toFlat := Module.Flat.of_projective, submodule_ne_top := ?_ }
  intro m hm htop
  have hann : Module.annihilator T M = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  have hsupp : Module.support T M = Set.univ := by
    rw [Module.support_eq_zeroLocus, hann]
    simp
  have hsupport :
      (Module.support T (M ⧸ (m • ⊤ : Submodule T M))).Nonempty := by
    rw [Module.support_quotient, hsupp, Set.univ_inter]
    exact ⟨⟨m, hm.isPrime⟩, by simp⟩
  have hnontrivial : Nontrivial (M ⧸ (m • ⊤ : Submodule T M)) :=
    Module.nonempty_support_iff.mp hsupport
  rw [htop] at hnontrivial
  exact not_subsingleton_iff_nontrivial.mpr hnontrivial (by infer_instance)

/-- The left factor of the base-changed enveloping algebra. -/
noncomputable def leftInEnvelope : A →ₐ[R] P :=
  ((Algebra.TensorProduct.includeLeft : C →ₐ[S] P).restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[R] C)

/-- The right, opposite factor of the base-changed enveloping algebra. -/
noncomputable def rightInEnvelope : Aᵐᵒᵖ →ₐ[R] P :=
  ((Algebra.TensorProduct.includeRight : Cᵐᵒᵖ →ₐ[S] P).restrictScalars R).comp
    (AlgHom.op (Algebra.TensorProduct.includeRight : A →ₐ[R] C))

/-- The canonical map from the base change of the original enveloping algebra to the enveloping
algebra of the base change. -/
noncomputable def envelopeBaseChangeMap :
    S ⊗[R] (A ⊗[R] Aᵐᵒᵖ) →ₐ[S] P :=
  Algebra.TensorProduct.lift (Algebra.ofId S P)
    (Algebra.TensorProduct.lift (leftInEnvelope (R := R) (S := S))
      (rightInEnvelope (R := R) (S := S))
      fun x y ↦ by
        show ((1 ⊗ₜ[R] x) ⊗ₜ[S] (1 : Cᵐᵒᵖ)) *
          ((1 : C) ⊗ₜ[S] MulOpposite.op (1 ⊗ₜ[R] y.unop)) = _
        exact (Commute.one_right _).tmul (Commute.one_left _))
    fun x y ↦ Algebra.commutes _ _

theorem envelopeBaseChangeMap_tmul (s : S) (a : A) (b : Aᵐᵒᵖ) :
    envelopeBaseChangeMap (R := R) (S := S) (s ⊗ₜ[R] (a ⊗ₜ[R] b)) =
      (s • (1 ⊗ₜ[R] a)) ⊗ₜ[S] (MulOpposite.op (1 ⊗ₜ[R] b.unop)) := by
  simp only [envelopeBaseChangeMap, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
  change (algebraMap S P s) *
      (((1 ⊗ₜ[R] a) ⊗ₜ[S] (1 : Cᵐᵒᵖ)) *
        ((1 : C) ⊗ₜ[S] MulOpposite.op (1 ⊗ₜ[R] b.unop))) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  simp

/-- The base-changed left-right action factors through the canonical enveloping-algebra map. -/
theorem mulLeftRight_envelopeBaseChangeMap (t : S ⊗[R] (A ⊗[R] Aᵐᵒᵖ)) :
    AlgHom.mulLeftRight S C (envelopeBaseChangeMap (R := R) (S := S) t) =
      LinearMap.tensorProductEnd R S A
        ((AlgHom.mulLeftRight R A).toLinearMap.baseChange S t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul s z =>
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
      | tmul s' x =>
        rw [envelopeBaseChangeMap_tmul]
        rw [LinearMap.baseChange_tmul]
        simp only [AlgHom.mulLeftRight_apply, LinearMap.tensorProductEnd_apply]
        dsimp
        change (s • (1 ⊗ₜ[R] a)) * (s' ⊗ₜ[R] x) * (1 ⊗ₜ[R] b.unop) =
          s • LinearMap.baseChangeHom R S A A
            (AlgHom.mulLeftRight R A (a ⊗ₜ[R] b)) (s' ⊗ₜ[R] x)
        simp only [LinearMap.baseChangeHom_apply]
        rw [LinearMap.baseChange_tmul, AlgHom.mulLeftRight_apply]
        rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_assoc]
        simp
        rfl

/-- The canonical map from the base-changed enveloping algebra is surjective. -/
theorem envelopeBaseChangeMap_surjective :
    Function.Surjective (envelopeBaseChangeMap (R := R) (S := S) (A := A)) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨x, hx⟩ := hx
    obtain ⟨y, hy⟩ := hy
    exact ⟨x + y, by rw [map_add, hx, hy]⟩
  | tmul c d =>
    induction c using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add c₁ c₂ hc₁ hc₂ =>
      rw [TensorProduct.add_tmul]
      obtain ⟨x, hx⟩ := hc₁
      obtain ⟨y, hy⟩ := hc₂
      exact ⟨x + y, by rw [map_add, hx, hy]⟩
    | tmul s a =>
      rcases d with ⟨d⟩
      change ∃ x, envelopeBaseChangeMap x = (s ⊗ₜ[R] a) ⊗ₜ[S] MulOpposite.op d
      induction d using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | add d₁ d₂ hd₁ hd₂ =>
        rw [MulOpposite.op_add, TensorProduct.tmul_add]
        obtain ⟨x, hx⟩ := hd₁
        obtain ⟨y, hy⟩ := hd₂
        exact ⟨x + y, by rw [map_add, hx, hy]⟩
      | tmul t b =>
        refine ⟨(t * s) ⊗ₜ[R] (a ⊗ₜ[R] MulOpposite.op b), ?_⟩
        rw [envelopeBaseChangeMap_tmul]
        rw [MulOpposite.unop_op]
        have h : (t * s) • (1 ⊗ₜ[R] a) = t • (s ⊗ₜ[R] a) := by
          rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
          simp [smul_eq_mul]
        rw [h, TensorProduct.smul_tmul, ← MulOpposite.op_smul,
          TensorProduct.smul_tmul']
        simp [smul_eq_mul]

/-- The composite of the canonical enveloping-algebra map with the base-changed left-right
action is bijective. -/
theorem mulLeftRight_envelopeBaseChangeMap_bijective [IsAzumaya R A] :
    Function.Bijective fun t =>
      AlgHom.mulLeftRight S C (envelopeBaseChangeMap (R := R) (S := S) t) := by
  let e : (A ⊗[R] Aᵐᵒᵖ) ≃ₗ[R] Module.End R A :=
    LinearEquiv.ofBijective (AlgHom.mulLeftRight R A).toLinearMap IsAzumaya.bij
  have hbase : Function.Bijective ((AlgHom.mulLeftRight R A).toLinearMap.baseChange S) := by
    change Function.Bijective (LinearMap.baseChange S e.toLinearMap)
    rw [← LinearEquiv.coe_baseChange]
    exact (LinearEquiv.baseChange R S _ _ e).bijective
  have hend : Function.Bijective (LinearMap.tensorProductEnd R S A) :=
    tensorProductEnd_bijective_of_projective (R := R) (S := S) (M := A)
  rw [show (fun t => AlgHom.mulLeftRight S C (envelopeBaseChangeMap (R := R) (S := S) t)) =
      LinearMap.tensorProductEnd R S A ∘
        (AlgHom.mulLeftRight R A).toLinearMap.baseChange S from
      funext fun t => mulLeftRight_envelopeBaseChangeMap t]
  exact hend.comp hbase

/-- The left-right map of an Azumaya algebra remains bijective after arbitrary scalar extension.
This is the non-faithfulness portion of the Azumaya base-change theorem. -/
theorem mulLeftRight_scalarExtension_bijective [IsAzumaya R A] :
    Function.Bijective (AlgHom.mulLeftRight S C) := by
  have hcomp := mulLeftRight_envelopeBaseChangeMap_bijective (R := R) (S := S) (A := A)
  refine ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨u, hu⟩ := envelopeBaseChangeMap_surjective (R := R) (S := S) (A := A) x
    obtain ⟨v, hv⟩ := envelopeBaseChangeMap_surjective (R := R) (S := S) (A := A) y
    calc
      x = envelopeBaseChangeMap u := hu.symm
      _ = envelopeBaseChangeMap v := congrArg envelopeBaseChangeMap <| hcomp.1 <| by
        simpa only [hu, hv] using hxy
      _ = y := hv
  · intro f
    obtain ⟨t, ht⟩ := hcomp.2 f
    exact ⟨envelopeBaseChangeMap t, ht⟩

/-- Scalar extension preserves the Azumaya structure whenever its faithful flatness is supplied. -/
theorem isAzumaya_scalarExtension_of_faithfullyFlat [IsAzumaya R A]
    [Module.FaithfullyFlat R A] : IsAzumaya S C := by
  letI : Module.FaithfullyFlat S C := inferInstance
  letI : FaithfulSMul S C := faithfullyFlat_faithfulSMul
  exact { bij := mulLeftRight_scalarExtension_bijective (R := R) (S := S) (A := A) }

/-- Azumaya algebras remain Azumaya after arbitrary commutative-ring scalar extension. -/
theorem isAzumaya_scalarExtension [IsAzumaya R A] : IsAzumaya S C := by
  letI : Module.FaithfullyFlat R A := faithfullyFlat_of_finite_projective_faithful
  exact isAzumaya_scalarExtension_of_faithfullyFlat (R := R) (S := S) (A := A)

end GaloisForLFunctions.HTGeometry.ABHN.AzumayaScalarExtension
