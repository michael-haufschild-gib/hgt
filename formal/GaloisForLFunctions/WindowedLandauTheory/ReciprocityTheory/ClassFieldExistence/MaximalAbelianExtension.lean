import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization

/-! The maximal abelian subextension of a Galois extension is fixed by
the closed commutator subgroup. Its Galois group carries the quotient
topology and its restriction maps are continuous. -/

noncomputable section

namespace GlobalTheory.Reciprocity

open IntermediateField

open scoped commutatorElement

section MaximalAbelian

variable (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]

def commutatorClosure : ClosedSubgroup (Ω ≃ₐ[F] Ω) where
  toSubgroup := (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure
  isClosed' := Subgroup.isClosed_topologicalClosure _

instance normal_commutatorClosure : (commutatorClosure F Ω).Normal :=
  inferInstanceAs (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure.Normal

def maximalAbelianExtension : IntermediateField F Ω :=
  fixedField (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure

variable [IsGalois F Ω]

instance isGalois_maximalAbelianExtension : IsGalois F (maximalAbelianExtension F Ω) :=
  IsGalois.of_fixedField_normal_subgroup _

theorem fixingSubgroup_maximalAbelianExtension :
    (maximalAbelianExtension F Ω).fixingSubgroup = (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure :=
  InfiniteGalois.fixingSubgroup_fixedField (commutatorClosure F Ω)

noncomputable def topologicalAbelianizationEquiv :
    TopologicalAbelianization (Ω ≃ₐ[F] Ω) ≃ₜ*
      (maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) :=
  have : T2Space (maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) :=
    krullTopology_t2
  let e := InfiniteGalois.normalAutEquivQuotient (commutatorClosure F Ω)
  have hc : Continuous e := by
    apply Continuous.quotient_lift
    exact InfiniteGalois.restrictNormalHom_continuous _
  { e with
    continuous_toFun := hc
    continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

theorem topologicalAbelianizationEquiv_mk (σ : Ω ≃ₐ[F] Ω) :
    topologicalAbelianizationEquiv F Ω (σ : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) =
      AlgEquiv.restrictNormalHom (maximalAbelianExtension F Ω) σ :=
  rfl

theorem topologicalAbelianizationEquiv_mk_apply (σ : Ω ≃ₐ[F] Ω) (x : maximalAbelianExtension F Ω) :
    ((topologicalAbelianizationEquiv F Ω (σ : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) x : _) : Ω) =
      σ x := by
  rw [topologicalAbelianizationEquiv_mk, AlgEquiv.restrictNormalHom_apply]

end MaximalAbelian

section Restrict

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem commutator_le_ker_of_comm {G M : Type*} [Group G] [Group M] [IsMulCommutative M]
    (f : G →* M) : commutator G ≤ f.ker := by
  rw [commutator, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm' _ _

theorem le_maximalAbelianExtension (L : IntermediateField F Ω) [IsAbelianGalois F L] :
    L ≤ maximalAbelianExtension F Ω := by
  have : T2Space (L ≃ₐ[F] L) := krullTopology_t2
  rw [maximalAbelianExtension, le_iff_le, ← L.restrictNormalHom_ker]
  refine Subgroup.topologicalClosure_minimal _ (commutator_le_ker_of_comm _) ?_
  exact isClosed_singleton.preimage (InfiniteGalois.restrictNormalHom_continuous L)

variable (E : IntermediateField F Ω) [Normal F E]

theorem closure_commutator_le_ker_restrictNormalHom (h : E ≤ maximalAbelianExtension F Ω) :
    (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure ≤ (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) E).ker := by
  rw [E.restrictNormalHom_ker, ← fixingSubgroup_maximalAbelianExtension]
  exact fixingSubgroup_le h

noncomputable def restrictAb (h : E ≤ maximalAbelianExtension F Ω) :
    (maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) →* (E ≃ₐ[F] E) :=
  (QuotientGroup.lift _ (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) E)
    (closure_commutator_le_ker_restrictNormalHom E h)).comp
      (topologicalAbelianizationEquiv F Ω).symm.toMulEquiv.toMonoidHom

theorem restrictAb_topologicalAbelianizationEquiv (h : E ≤ maximalAbelianExtension F Ω) (σ : Ω ≃ₐ[F] Ω) :
    restrictAb E h (topologicalAbelianizationEquiv F Ω (σ : TopologicalAbelianization (Ω ≃ₐ[F] Ω))) =
      AlgEquiv.restrictNormalHom E σ := by
  change QuotientGroup.lift _ _ (closure_commutator_le_ker_restrictNormalHom E h)
    ((topologicalAbelianizationEquiv F Ω).symm (topologicalAbelianizationEquiv F Ω _)) = _
  rw [ContinuousMulEquiv.symm_apply_apply]
  rfl

theorem restrictAb_apply (h : E ≤ maximalAbelianExtension F Ω) (σ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) (x : E) :
    ((restrictAb E h σ x : E) : Ω) = ((σ ⟨x, h x.2⟩ : maximalAbelianExtension F Ω) : Ω) := by
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective ((topologicalAbelianizationEquiv F Ω).symm σ)
  have hσ : σ = topologicalAbelianizationEquiv F Ω (τ : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) := by
    rw [hτ, ContinuousMulEquiv.apply_symm_apply]
  rw [hσ, restrictAb_topologicalAbelianizationEquiv, AlgEquiv.restrictNormalHom_apply,
    topologicalAbelianizationEquiv_mk_apply]

theorem continuous_restrictAb (h : E ≤ maximalAbelianExtension F Ω) : Continuous (restrictAb E h) := by
  have h1 : Continuous (QuotientGroup.lift _ (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) E)
      (closure_commutator_le_ker_restrictNormalHom E h)) :=
    Continuous.quotient_lift (InfiniteGalois.restrictNormalHom_continuous E) _
  exact h1.comp (topologicalAbelianizationEquiv F Ω).symm.continuous

end Restrict

end GlobalTheory.Reciprocity
