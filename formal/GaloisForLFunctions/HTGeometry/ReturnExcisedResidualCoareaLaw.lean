import GaloisForLFunctions.HTGeometry.ReturnExcisedMinimalIncidenceRankLaw

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Return-excised minimal-rank coarea for targets in the closed Hilbert
unit ball. This retains the norm loss created by scalar-return subtraction;
renormalizing residual targets would erase the growing-replica gain. -/
theorem quenchedReplica_returnExcisedMinimalIncidence_bound_of_replicaNorm_le_one
    {X C α : Type*} [MeasurableSpace X] [Fintype C] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c,
      ‖finitePureTensorPowerEuclidean r (target c)‖ ≤ 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r target state returnSet)
        (state x) i) (μ.restrict returnSetᶜ))
    (hcoord : ∀ i, Integrable
      (fun x => ‖replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r target state returnSet)
        (state x) i‖ ^ 2) (μ.restrict returnSetᶜ)) :
    (((μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} *
        threshold ^ r) ^ 2) ≤
      (returnExcisedReplicaIncidenceNumber r target state returnSet : ℝ) *
        returnExcisedReplicaMinimalIncidenceAction
          μ r target state returnSet := by
  let U := returnExcisedReplicaIncidenceSpan r target state returnSet
  let a : X → Fin (Module.finrank ℂ U) → ℂ :=
    fun x i => replicaSubspaceCoordinate r U (state x) i
  let E : Set X := {x | ∃ c,
    threshold ≤ finitePureStateFidelity (state x) (target c)}
  have hcapture : E ∩ returnSetᶜ ⊆
      {x | threshold ^ r ≤ finiteCoordinateEnergy a x} := by
    intro x hx
    have hproj := completePureStateTargetCapture_subset_replicaProjectionMass
      hr target state htarget threshold hthreshold.le hx.1
    change threshold ^ r ≤ replicaTargetProjectionMass r target (state x) at hproj
    have heq := replicaTargetProjectionMass_eq_incidenceProjectionMass_offReturn
      r target state returnSet hx.2
    rw [heq, replicaSubspaceProjectionMass_eq_finiteCoordinateEnergy] at hproj
    simpa [finiteCoordinateEnergy, a, U] using hproj
  simpa [E, a, U, returnExcisedReplicaIncidenceNumber,
    returnExcisedReplicaMinimalIncidenceAction, Fintype.card_fin] using
    returnExcisedFiniteCoordinateIncidence_bound
      μ E returnSet hreturn a (threshold ^ r) (pow_pos hthreshold r)
        hcapture hmeas hcoord

/-- Closed-unit-ball version of incidence-normalized coarea. Occupied target
image, surviving source sheets, and residual norm suppression all remain in
the exact pair action. -/
theorem quenchedReplica_returnExcisedMinimalRankCoareaIncidence_bound_of_replicaNorm_le_one
    {X C α : Type*} [MeasurableSpace X] [Fintype C] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c,
      ‖finitePureTensorPowerEuclidean r (target c)‖ ≤ 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r target state returnSet)
        (state x) i) (μ.restrict returnSetᶜ))
    (hcoord : ∀ i, Integrable
      (fun x => ‖replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r target state returnSet)
        (state x) i‖ ^ 2) (μ.restrict returnSetᶜ)) :
    (μ.real {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
      μ.real returnSet +
        (μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)}) ∧
    (((μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} *
        threshold ^ r) ^ 2 ≤
      (returnExcisedReplicaIncidenceNumber r target state returnSet : ℝ) *
        returnExcisedReplicaIncidenceAction
          μ r target state returnSet) := by
  constructor
  · exact measureReal_capture_le_return_add_restrict_compl
      μ target state threshold returnSet hreturn
  · rw [← returnExcisedReplicaMinimalIncidenceAction_eq_targetAction
      μ r target state returnSet hreturn]
    exact quenchedReplica_returnExcisedMinimalIncidence_bound_of_replicaNorm_le_one
      μ hr target state htarget threshold hthreshold returnSet hreturn hmeas hcoord

end

end GaloisForLFunctions.HTGeometry
