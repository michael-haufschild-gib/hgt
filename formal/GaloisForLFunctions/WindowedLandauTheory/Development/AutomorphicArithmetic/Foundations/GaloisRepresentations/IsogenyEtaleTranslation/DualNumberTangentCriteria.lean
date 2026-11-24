import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Module.PUnit
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.Tactic.Algebraize

/-! Geometric dual-number lifts detect formal smoothness and formal unramifiedness. -/

open TensorProduct

noncomputable section

namespace GlobalTheory.TangentCrit

section Alg

variable {R A B k : Type*} [CommRing R] [CommRing A] [CommRing B]

section Der

variable [CommRing k] [Algebra R A] [Algebra A k] [Algebra R k] [IsScalarTower R A k]

private def derToDual (D : Derivation R A k) : A →+* DualNumber k where
  toFun a := TrivSqZeroExt.inl (algebraMap A k a) + TrivSqZeroExt.inr (D a)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [Algebra.smul_def, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]

omit [IsScalarTower R A k] in
@[simp] private lemma fst_derToDual (D : Derivation R A k) (a : A) :
    (derToDual D a).fst = algebraMap A k a := by simp [derToDual]

omit [IsScalarTower R A k] in
@[simp] private lemma snd_derToDual (D : Derivation R A k) (a : A) :
    (derToDual D a).snd = D a := by simp [derToDual]

private def dualToDer (φ : A →+* DualNumber k) (h₁ : ∀ a, (φ a).fst = algebraMap A k a)
    (h₂ : ∀ r, (φ (algebraMap R A r)).snd = 0) : Derivation R A k :=
  Derivation.mk'
    { toFun a := (φ a).snd
      map_add' a b := by simp
      map_smul' r a := by
        rw [Algebra.smul_def, map_mul, DualNumber.snd_mul, h₂, h₁, ← IsScalarTower.algebraMap_apply]
        simp [Algebra.smul_def] }
    (fun a b => by
      simp [h₁, Algebra.smul_def, mul_comm])

@[simp] private lemma dualToDer_apply (φ : A →+* DualNumber k) (h₁ : ∀ a, (φ a).fst = algebraMap A k a)
    (h₂ : ∀ r, (φ (algebraMap R A r)).snd = 0) (a : A) :
    dualToDer φ h₁ h₂ a = (φ a).snd := rfl

end Der

private lemma lTensor_injective_of_extend {κ M N : Type*} [Field κ] [Field k] [Algebra B κ] [Algebra B k]
    [Algebra κ k] [IsScalarTower B κ k] [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (l : M →ₗ[B] N) (H : ∀ φ : M →ₗ[B] k, ∃ ψ : N →ₗ[B] k, ψ ∘ₗ l = φ) :
    Function.Injective (l.lTensor κ) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  rw [← Module.forall_dual_apply_eq_zero_iff κ]
  intro χ
  obtain ⟨ψ, hψ⟩ := H ((Algebra.linearMap κ k ∘ₗ χ).restrictScalars B ∘ₗ TensorProduct.mk B κ M 1)
  have : ∀ z : κ ⊗[B] M, ψ.liftBaseChange κ (l.lTensor κ z) = algebraMap κ k (χ z) := by
    intro z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c m =>
      have h := LinearMap.congr_fun hψ m
      simp only [LinearMap.comp_apply] at h
      have e : c ⊗ₜ[B] m = c • ((1 : κ) ⊗ₜ[B] m) := by simp [smul_tmul']
      rw [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul, h, e, map_smul]
      simp [Algebra.smul_def]
  have h := this z
  rw [hz, map_zero] at h
  exact (algebraMap κ k).injective (by rw [← h, map_zero])

private lemma formallySmooth_of_split [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallySmooth R B] (r : Ω[B⁄R] →ₗ[B] B ⊗[A] Ω[A⁄R])
    (hr : r ∘ₗ KaehlerDifferential.mapBaseChange R A B = LinearMap.id) :
    Algebra.FormallySmooth A B := by
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R A B) :=
    Function.LeftInverse.injective (g := r) (LinearMap.congr_fun hr)
  rw [Algebra.formallySmooth_iff]
  constructor
  · have hex := KaehlerDifferential.exact_mapBaseChange_map R A B
    have hs := KaehlerDifferential.map_surjective R A B
    have h₀ : ∃ l, l ∘ₗ KaehlerDifferential.mapBaseChange R A B = LinearMap.id := ⟨r, hr⟩
    obtain ⟨s, hs'⟩ : ∃ l, KaehlerDifferential.map R A B B ∘ₗ l = LinearMap.id :=
      ((hex.split_tfae hinj hs).out 1 0).mp h₀
    exact Module.Projective.of_split s _ hs'
  · refine subsingleton_of_forall_eq 0 fun x => ?_
    have h₁ : Algebra.H1Cotangent.δ R A B x = 0 := by
      apply hinj
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B).apply_apply_eq_zero x
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R A B x).mp h₁
    rw [Subsingleton.elim y 0, map_zero]

/-- Lifting relative maps to dual numbers gives a split injection on
cotangent modules at the local ring. -/
theorem formallySmooth_of_dual_lift [Field k] [IsLocalRing B] (α : R →+* A) (β : A →+* B)
    (hA : α.EssFiniteType) (hB : (β.comp α).EssFiniteType) (hs : (β.comp α).FormallySmooth)
    (x : B →+* k) [IsLocalHom x]
    (H : ∀ ψ : A →+* DualNumber k, (∀ a, (ψ a).fst = x (β a)) → (∀ r, (ψ (α r)).snd = 0) →
      ∃ φ : B →+* DualNumber k, (∀ b, (φ b).fst = x b) ∧ ∀ a, φ (β a) = ψ a) :
    β.FormallySmooth := by
  algebraize [α, β, β.comp α, x, x.comp β, (x.comp β).comp α]
  have : IsScalarTower R B k := .of_algebraMap_eq' rfl
  haveI : IsLocalHom (algebraMap B k) := ‹_›
  letI : Algebra (IsLocalRing.ResidueField B) k := (IsLocalRing.ResidueField.lift x).toAlgebra
  haveI : IsScalarTower B (IsLocalRing.ResidueField B) k := .of_algebraMap_eq fun _ => rfl
  haveI : Module.Free B Ω[B⁄R] := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective
    (KaehlerDifferential.mapBaseChange R A B)).mpr (lTensor_injective_of_extend (k := k) _ fun χ => by
      let D : Derivation R A k :=
        ((χ.restrictScalars A) ∘ₗ TensorProduct.mk A B Ω[A⁄R] 1).compDer (KaehlerDifferential.D R A)
      obtain ⟨φ, h₁, h₂⟩ := H (derToDual D) (fun a => fst_derToDual D a)
        (fun r => (snd_derToDual D _).trans (D.map_algebraMap r))
      let E : Derivation R B k := dualToDer φ h₁ (fun r => by
        change (φ (β (α r))).snd = 0
        rw [h₂]; exact (snd_derToDual D _).trans (D.map_algebraMap r))
      refine ⟨E.liftKaehlerDifferential, ?_⟩
      refine TensorProduct.AlgebraTensorModule.curry_injective (LinearMap.ext_ring ?_)
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun a => ?_)
      have : E (algebraMap A B a) = D a := by
        change (φ (β a)).snd = _
        rw [h₂, snd_derToDual]
      simpa [D, KaehlerDifferential.map_D] using this)
  exact formallySmooth_of_split r hr

/-- Vanishing of all geometric relative tangent vectors implies
vanishing of the module of differentials. -/
theorem formallyUnramified_of_dual_const.{u} {A B : Type u} [CommRing A] [CommRing B]
    (β : A →+* B) (hβ : β.EssFiniteType)
    (H : ∀ (k : Type u) [Field k] [IsAlgClosed k] (φ : B →+* DualNumber k),
      (∀ a, (φ (β a)).snd = 0) → ∀ b, (φ b).snd = 0) : β.FormallyUnramified := by
  algebraize [β]
  refine ⟨?_⟩
  rw [← Module.support_eq_empty_iff (R := B), Set.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  let κ := p.asIdeal.ResidueField
  let k := AlgebraicClosure κ
  have key : Function.Injective ((0 : Ω[B⁄A] →ₗ[B] PUnit.{1}).lTensor κ) :=
    lTensor_injective_of_extend (k := k) _ fun χ => by
      refine ⟨0, ?_⟩
      let D : Derivation A B k := χ.compDer (KaehlerDifferential.D A B)
      have := H k (derToDual D) (fun a => (snd_derToDual D _).trans (D.map_algebraMap a))
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun b => ?_)
      have := this b
      rw [snd_derToDual] at this
      simpa [D] using this.symm
  obtain ⟨z, hz⟩ := exists_ne (0 : κ ⊗[B] Ω[B⁄A])
  exact hz (key (by simp))

end Alg

end GlobalTheory.TangentCrit
