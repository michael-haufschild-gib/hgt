import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Trace.Basic

/-! Trace for finite projective modules and its compatibility with base change. -/

open TensorProduct

noncomputable section

namespace GlobalTheory.SchemeCohomology

private theorem dualTensorHom_precompose {R U V W : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (f : U →ₗ[R] V) (t : Module.Dual R V ⊗[R] W) (x : U) :
    dualTensorHom R U W (TensorProduct.map f.dualMap (LinearMap.id : W →ₗ[R] W) t) x =
      dualTensorHom R V W t (f x) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul g w => simp only [TensorProduct.map_tmul, LinearMap.dualMap_apply, LinearMap.id_apply,
      dualTensorHom_apply]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

section Module

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

private theorem projectiveDualTensor_bijective : Function.Bijective (dualTensorHom R M M) := by
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let e := dualTensorHomEquivOfBasis (N := M) (Pi.basisFun R (Fin n))
  let j := TensorProduct.map p.dualMap (LinearMap.id : M →ₗ[R] M)
  let k := TensorProduct.map i.dualMap (LinearMap.id : M →ₗ[R] M)
  have hj : Function.Injective j :=
    Function.LeftInverse.injective (g := k) fun t => by
      change TensorProduct.map i.dualMap LinearMap.id
        (TensorProduct.map p.dualMap LinearMap.id t) = t
      rw [TensorProduct.map_map, LinearMap.dualMap_comp_dualMap, hpi, LinearMap.dualMap_id,
        LinearMap.id_comp, TensorProduct.map_id, LinearMap.id_apply]
  constructor
  · intro t t' h
    apply hj
    apply e.injective
    apply LinearMap.ext
    intro x
    change dualTensorHom R (Fin n → R) M (TensorProduct.map p.dualMap LinearMap.id t) x =
      dualTensorHom R (Fin n → R) M (TensorProduct.map p.dualMap LinearMap.id t') x
    rw [dualTensorHom_precompose, dualTensorHom_precompose, h]
  · intro f
    obtain ⟨t, ht⟩ := e.surjective (f.comp p)
    change dualTensorHom R (Fin n → R) M t = f.comp p at ht
    refine ⟨k t, LinearMap.ext fun x => ?_⟩
    change dualTensorHom R M M (TensorProduct.map i.dualMap LinearMap.id t) x = f x
    rw [dualTensorHom_precompose, ht, LinearMap.comp_apply]
    exact congrArg f (LinearMap.congr_fun hpi x)

private def projectiveDualTensorEquiv : Module.Dual R M ⊗[R] M ≃ₗ[R] Module.End R M :=
  LinearEquiv.ofBijective _ (projectiveDualTensor_bijective R M)

/-- The trace is contraction under the dual tensor description of endomorphisms. -/
def projectiveTrace : Module.End R M →ₗ[R] R :=
  contractLeft R M ∘ₗ (projectiveDualTensorEquiv R M).symm.toLinearMap

variable {R M}

theorem projectiveTrace_tensor (t : Module.Dual R M ⊗[R] M) :
    projectiveTrace R M (dualTensorHom R M M t) = contractLeft R M t :=
  congrArg (contractLeft R M) ((projectiveDualTensorEquiv R M).symm_apply_apply t)

theorem projectiveTrace_eq_trace [Module.Free R M] (φ : Module.End R M) :
    projectiveTrace R M φ = LinearMap.trace R M φ := by
  obtain ⟨t, rfl⟩ := (projectiveDualTensor_bijective R M).2 φ
  exact (projectiveTrace_tensor t).trans (LinearMap.trace_eq_contract_apply R M t).symm

/-- Compatible endomorphisms have compatible traces under extension of scalars. -/
theorem projectiveTrace_baseChange {S N : Type*} [CommRing S] [Algebra R S] [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] [Module.Finite S N] [Module.Projective S N]
    {l : M →ₗ[R] N} (hl : IsBaseChange S l) (φ : Module.End R M) (ψ : Module.End S N)
    (h : ∀ x, ψ (l x) = l (φ x)) :
    projectiveTrace S N ψ = algebraMap R S (projectiveTrace R M φ) := by
  -- Extend each rank-one summand by extending its linear functional.
  have liftTensor (t : Module.Dual R M ⊗[R] M) :
      ∃ t' : Module.Dual S N ⊗[S] N,
        (∀ x, dualTensorHom S N N t' (l x) = l (dualTensorHom R M M t x)) ∧
        contractLeft S N t' = algebraMap R S (contractLeft R M t) := by
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | add a b ha hb =>
      obtain ⟨a', ha, hta⟩ := ha
      obtain ⟨b', hb, htb⟩ := hb
      exact ⟨a' + b', fun x => by simp [ha, hb], by simp [hta, htb]⟩
    | tmul ξ m =>
      refine ⟨hl.lift (Algebra.linearMap R S ∘ₗ ξ) ⊗ₜ l m, fun x => ?_, ?_⟩
      · simp [hl.lift_eq]
      · simp [hl.lift_eq]
  obtain ⟨t, rfl⟩ := (projectiveDualTensor_bijective R M).2 φ
  obtain ⟨t', hmap, htrace⟩ := liftTensor t
  have hψ : ψ = dualTensorHom S N N t' :=
    hl.algHom_ext _ _ fun x => (h x).trans (hmap x).symm
  rw [hψ, projectiveTrace_tensor, projectiveTrace_tensor, htrace]

theorem projectiveTrace_id_of_constant_rank {d : ℕ}
    (h : ∀ p, Module.rankAtStalk (R := R) M p = d) :
    projectiveTrace R M LinearMap.id = d := by
  refine Module.eq_of_localization_maximal (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap R (Localization.AtPrime P)) _ _ fun P hP => ?_
  rw [Algebra.linearMap_apply, Algebra.linearMap_apply]
  have hloc := IsLocalizedModule.isBaseChange P.primeCompl (Localization.AtPrime P)
    (LocalizedModule.mkLinearMap P.primeCompl M)
  haveI : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  rw [← projectiveTrace_baseChange hloc LinearMap.id LinearMap.id (fun _ => rfl),
    projectiveTrace_eq_trace, LinearMap.trace_id, map_natCast, ← h ⟨P, hP.isPrime⟩]
  rfl

end Module

section Algebra

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
  [Module.Projective R A]

/-- The trace of multiplication in a finite projective algebra. -/
def projectiveAlgebraTrace : A →ₗ[R] R :=
  projectiveTrace R A ∘ₗ LinearMap.mul R A

variable {R A}

theorem projectiveAlgebraTrace_eq_trace [Module.Free R A] (a : A) :
    projectiveAlgebraTrace R A a = Algebra.trace R A a :=
  projectiveTrace_eq_trace _

theorem projectiveAlgebraTrace_baseChange {S B : Type*} [CommRing S] [CommRing B]
    [Algebra R S] [Algebra S B] [Algebra A B] [Algebra R B] [IsScalarTower R S B]
    [IsScalarTower R A B] [Module.Finite S B] [Module.Projective S B]
    [h : Algebra.IsPushout R S A B] (a : A) :
    projectiveAlgebraTrace S B (algebraMap A B a) =
      algebraMap R S (projectiveAlgebraTrace R A a) :=
  projectiveTrace_baseChange h.out _ _ fun x => (map_mul (algebraMap A B) a x).symm

theorem projectiveAlgebraTrace_one {d : ℕ} (h : ∀ p, Module.rankAtStalk (R := R) A p = d) :
    projectiveAlgebraTrace R A 1 = d := by
  change projectiveTrace R A (LinearMap.mul R A 1) = _
  rw [show LinearMap.mul R A 1 = LinearMap.id by ext x; simp, projectiveTrace_id_of_constant_rank h]

end Algebra

end GlobalTheory.SchemeCohomology
