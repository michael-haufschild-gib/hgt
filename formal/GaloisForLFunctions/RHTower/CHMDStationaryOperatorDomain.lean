import GaloisForLFunctions.RHTower.CHMDStationaryGroundEquivalence
import GaloisForLFunctions.RHTower.CHMDPrimeOperatorDomain

/-!
# Exact stationary pullback of the full CHMD operator domain

The entire arithmetic generator differs from the stationary theta pullback by
the sum of the bounded prime operator and the explicit ground-state potential.
Both resolvent identities are proved on their actual Hilbert spaces. No compact
operator core or weak-domain admission hypothesis is used.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

def fullGroundEquiv : SourceGraph ≃L[ℝ] stationaryGroundGraph :=
  graphArchEquiv.trans archGroundEquiv

theorem fullGroundEquiv_source (p : SourceGraph) :
    stationaryGroundSourceMap (fullGroundEquiv p) = sourceMap p := by
  change (archGroundEquiv (graphArchEquiv p)).val.fst = p.val.fst
  rw [archGroundEquiv_source, graphArchEquiv_source]

theorem fullGroundEquiv_symm_source (p : stationaryGroundGraph) :
    sourceMap (fullGroundEquiv.symm p) = stationaryGroundSourceMap p := by
  change (graphArchEquiv.symm (archGroundEquiv.symm p)).val.fst = p.val.fst
  rw [graphArchEquiv_symm_source, archGroundEquiv_symm_source]

def groundPerturbation : MassSpace →L[ℝ] MassSpace := primeGenerator + groundPotentialOperator

theorem groundPerturbation_symmetric (u v : MassSpace) :
    ⟪groundPerturbation u, v⟫_ℝ = ⟪u, groundPerturbation v⟫_ℝ := by
  change ⟪primeGenerator u + groundPotentialOperator u, v⟫_ℝ =
    ⟪u, primeGenerator v + groundPotentialOperator v⟫_ℝ
  rw [inner_add_left, inner_add_right, groundPotentialOperator_symmetric,
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp primeGenerator_isSelfAdjoint u v]

theorem fullGround_inner_decomposition (p q : SourceGraph) :
    ⟪p, q⟫_ℝ = ⟪fullGroundEquiv p, fullGroundEquiv q⟫_ℝ +
      ⟪groundPerturbation (sourceMap p), sourceMap q⟫_ℝ := by
  rw [full_graph_inner_decomposition, archGround_inner_decomposition]
  have hp : archSourceMap (graphArchEquiv p) = sourceMap p := graphArchEquiv_source p
  have hq : archSourceMap (graphArchEquiv q) = sourceMap q := graphArchEquiv_source q
  rw [hp, hq]
  change _ = _ + ⟪primeGenerator (sourceMap p) + groundPotentialOperator (sourceMap p), sourceMap q⟫_ℝ
  rw [inner_add_left]
  ring

def stationaryRieszLift : MassSpace →L[ℝ] stationaryGroundGraph := stationaryGroundSourceMap.adjoint

theorem inner_stationaryRieszLift (w : MassSpace) (q : stationaryGroundGraph) :
    ⟪stationaryRieszLift w, q⟫_ℝ = ⟪w, stationaryGroundSourceMap q⟫_ℝ :=
  stationaryGroundSourceMap.adjoint_inner_left q w

theorem stationaryRieszLift_unique {w : MassSpace} {p : stationaryGroundGraph}
    (h : ∀ q : stationaryGroundGraph, ⟪p, q⟫_ℝ = ⟪w, stationaryGroundSourceMap q⟫_ℝ) :
    stationaryRieszLift w = p := by
  apply ext_inner_right ℝ
  intro q
  rw [inner_stationaryRieszLift, h]

def stationaryResolvent : MassSpace →L[ℝ] MassSpace :=
  stationaryGroundSourceMap.comp stationaryRieszLift

theorem stationaryResolvent_apply (w : MassSpace) :
    stationaryResolvent w = stationaryGroundSourceMap (stationaryRieszLift w) := rfl

theorem stationaryResolvent_isPositive : stationaryResolvent.IsPositive :=
  ContinuousLinearMap.isPositive_self_comp_adjoint stationaryGroundSourceMap

theorem stationaryResolvent_isSelfAdjoint : IsSelfAdjoint stationaryResolvent :=
  stationaryResolvent_isPositive.isSelfAdjoint

theorem stationaryRieszLift_full (w : MassSpace) :
    stationaryRieszLift (w - groundPerturbation (resolvent w)) = fullGroundEquiv (rieszLift w) := by
  apply stationaryRieszLift_unique
  intro q
  have h := inner_rieszLift w (fullGroundEquiv.symm q)
  rw [fullGround_inner_decomposition, fullGroundEquiv.apply_symm_apply] at h
  have hs : sourceMap (fullGroundEquiv.symm q) = stationaryGroundSourceMap q :=
    fullGroundEquiv_symm_source q
  change ⟪w, (fullGroundEquiv.symm q).val.fst⟫_ℝ =
    ⟪fullGroundEquiv (rieszLift w), q⟫_ℝ +
      ⟪groundPerturbation (resolvent w), sourceMap (fullGroundEquiv.symm q)⟫_ℝ at h
  change ⟪w, sourceMap (fullGroundEquiv.symm q)⟫_ℝ = _ at h
  rw [hs] at h
  rw [inner_sub_left]
  linarith

theorem fullRieszLift_stationary (w : MassSpace) :
    rieszLift (w + groundPerturbation (stationaryResolvent w)) =
      fullGroundEquiv.symm (stationaryRieszLift w) := by
  apply rieszLift_unique
  intro q
  rw [fullGround_inner_decomposition, fullGroundEquiv.apply_symm_apply, inner_stationaryRieszLift,
    inner_add_left]
  have hs : stationaryGroundSourceMap (fullGroundEquiv q) = sourceMap q := fullGroundEquiv_source q
  have hs' : sourceMap (fullGroundEquiv.symm (stationaryRieszLift w)) = stationaryResolvent w :=
    fullGroundEquiv_symm_source (stationaryRieszLift w)
  rw [hs, hs']
  rfl

theorem stationaryResolvent_full_shift (w : MassSpace) :
    stationaryResolvent (w - groundPerturbation (resolvent w)) = resolvent w := by
  rw [stationaryResolvent_apply, stationaryRieszLift_full]
  exact fullGroundEquiv_source (rieszLift w)

theorem fullResolvent_stationary_shift (w : MassSpace) :
    resolvent (w + groundPerturbation (stationaryResolvent w)) = stationaryResolvent w := by
  rw [resolvent_apply, fullRieszLift_stationary]
  exact fullGroundEquiv_symm_source (stationaryRieszLift w)

/-- The actual full and stationary-pullback generators have identical operator domains. -/
theorem full_operator_domain_eq_stationary : Set.range resolvent = Set.range stationaryResolvent := by
  ext u
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w - groundPerturbation (resolvent w), stationaryResolvent_full_shift w⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w + groundPerturbation (stationaryResolvent w), fullResolvent_stationary_shift w⟩

/-- Exact generator graph relation, with every nonsingular term displayed. -/
theorem full_generator_relation_iff_stationary (u v : MassSpace) :
    resolvent (u + v) = u ↔ stationaryResolvent (u + v - groundPerturbation u) = u := by
  constructor
  · intro h
    have h' := stationaryResolvent_full_shift (u + v)
    rwa [h] at h'
  · intro h
    have h' := fullResolvent_stationary_shift (u + v - groundPerturbation u)
    rw [h, sub_add_cancel] at h'
    exact h'

end RHTower.CHMDDoobGraph
