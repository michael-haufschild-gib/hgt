import GaloisForLFunctions.RHTower.CHMDArchimedeanDomain
import GaloisForLFunctions.RHTower.CHMDArithmeticResolvent

/-!
# Arithmetic preserves the exact operator domain

The actual full and archimedean Riesz resolvents satisfy both bounded-perturbation
identities. Their ranges, hence their generator domains, coincide. The generator
graph relation changes by the literal bounded prime operator; no weak-domain
admission premise or operator-core assumption is introduced.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

def archRieszLift : MassSpace →L[ℝ] ArchGraph := archSourceMap.adjoint

theorem inner_archRieszLift (w : MassSpace) (q : ArchGraph) :
    ⟪archRieszLift w, q⟫_ℝ = ⟪w, archSourceMap q⟫_ℝ :=
  archSourceMap.adjoint_inner_left q w

theorem archRieszLift_unique {w : MassSpace} {p : ArchGraph}
    (h : ∀ q : ArchGraph, ⟪p, q⟫_ℝ = ⟪w, archSourceMap q⟫_ℝ) : archRieszLift w = p := by
  apply ext_inner_right ℝ
  intro q
  rw [inner_archRieszLift, h]

/-- Riesz resolvent of the actual closed archimedean graph. -/
def archResolvent : MassSpace →L[ℝ] MassSpace := archSourceMap.comp archRieszLift

theorem archResolvent_apply (w : MassSpace) :
    archResolvent w = archSourceMap (archRieszLift w) := rfl

theorem archResolvent_isPositive : archResolvent.IsPositive :=
  ContinuousLinearMap.isPositive_self_comp_adjoint archSourceMap

theorem archResolvent_isSelfAdjoint : IsSelfAdjoint archResolvent :=
  archResolvent_isPositive.isSelfAdjoint

theorem archRieszLift_full (w : MassSpace) :
    archRieszLift (w - primeGenerator (resolvent w)) = graphArchEquiv (rieszLift w) := by
  apply archRieszLift_unique
  intro q
  have h := full_graph_inner_decomposition (rieszLift w) (graphArchEquiv.symm q)
  rw [graphArchEquiv.apply_symm_apply, inner_rieszLift] at h
  have hs : sourceMap (graphArchEquiv.symm q) = archSourceMap q :=
    graphArchEquiv_symm_source q
  change ⟪w, (graphArchEquiv.symm q).val.fst⟫_ℝ =
    ⟪graphArchEquiv (rieszLift w), q⟫_ℝ +
      ⟪primeGenerator (resolvent w), sourceMap (graphArchEquiv.symm q)⟫_ℝ at h
  change ⟪w, sourceMap (graphArchEquiv.symm q)⟫_ℝ = _ at h
  rw [hs] at h
  rw [inner_sub_left]
  linarith

theorem fullRieszLift_arch (w : MassSpace) :
    rieszLift (w + primeGenerator (archResolvent w)) =
      graphArchEquiv.symm (archRieszLift w) := by
  apply rieszLift_unique
  intro q
  rw [full_graph_inner_decomposition, graphArchEquiv.apply_symm_apply, inner_archRieszLift,
    inner_add_left]
  have hs : archSourceMap (graphArchEquiv q) = sourceMap q := graphArchEquiv_source q
  have hs' : sourceMap (graphArchEquiv.symm (archRieszLift w)) = archResolvent w :=
    graphArchEquiv_symm_source (archRieszLift w)
  rw [hs, hs']
  rfl

theorem archResolvent_full_shift (w : MassSpace) :
    archResolvent (w - primeGenerator (resolvent w)) = resolvent w := by
  rw [archResolvent_apply, archRieszLift_full]
  exact graphArchEquiv_source (rieszLift w)

theorem fullResolvent_arch_shift (w : MassSpace) :
    resolvent (w + primeGenerator (archResolvent w)) = archResolvent w := by
  rw [resolvent_apply, fullRieszLift_arch]
  exact graphArchEquiv_symm_source (archRieszLift w)

/-- Full and archimedean generators have the same actual operator domain. -/
theorem full_operator_domain_eq_arch : Set.range resolvent = Set.range archResolvent := by
  ext u
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w - primeGenerator (resolvent w), archResolvent_full_shift w⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w + primeGenerator (archResolvent w), fullResolvent_arch_shift w⟩

/-- On that domain the full generator is exactly the archimedean generator plus P. -/
theorem full_generator_relation_iff_arch (u v : MassSpace) :
    resolvent (u + v) = u ↔ archResolvent (u + v - primeGenerator u) = u := by
  constructor
  · intro h
    have h' := archResolvent_full_shift (u + v)
    rwa [h] at h'
  · intro h
    have h' := fullResolvent_arch_shift (u + v - primeGenerator u)
    rw [h, sub_add_cancel] at h'
    exact h'

/-- Bounded invertible change between the actual generator graph coordinates. -/
def primeGeneratorShear : (MassSpace × MassSpace) ≃L[ℝ] (MassSpace × MassSpace) where
  toFun p := (p.1, p.2 - primeGenerator p.1)
  invFun p := (p.1, p.2 + primeGenerator p.1)
  left_inv p := by
    exact Prod.ext rfl (sub_add_cancel _ _)
  right_inv p := by
    exact Prod.ext rfl (add_sub_cancel_right _ _)
  map_add' p q := by
    apply Prod.ext
    · rfl
    · change p.2 + q.2 - primeGenerator (p.1 + q.1) =
        (p.2 - primeGenerator p.1) + (q.2 - primeGenerator q.1)
      rw [map_add]
      abel
  map_smul' c p := by
    apply Prod.ext
    · rfl
    · change c • p.2 - primeGenerator (c • p.1) = c • (p.2 - primeGenerator p.1)
      rw [map_smul, smul_sub]
  continuous_toFun := continuous_fst.prodMk
    (continuous_snd.sub (primeGenerator.continuous.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk
    (continuous_snd.add (primeGenerator.continuous.comp continuous_fst))

theorem full_generator_graph_shift (p : MassSpace × MassSpace) :
    resolvent (p.1 + p.2) = p.1 ↔
      archResolvent ((primeGeneratorShear p).1 + (primeGeneratorShear p).2) =
        (primeGeneratorShear p).1 := by
  change resolvent (p.1 + p.2) = p.1 ↔
    archResolvent (p.1 + (p.2 - primeGenerator p.1)) = p.1
  rw [← add_sub_assoc]
  exact full_generator_relation_iff_arch p.1 p.2

end RHTower.CHMDDoobGraph
