import GaloisForLFunctions.HTGeometry.QuenchedReplicaPairIncidenceLaw

/-!
# Quenched replica return-excision law

Cutting a relation after the occupied-image covariance is formed can leave
mixed return/nonreturn pairs in the term that still requires
anti-concentration.  The correct operation is source excision: restrict the
quenched source measure to the complement of one measurable recurrence set
before forming the covariance.

The complete target-capture mass then has two terms.  Recurrence mass is paid
once.  Every remaining pair lies in the return-free square, while the target
family is still represented only by its occupied replica image.  Source
points are never quotiented, so all surviving fibre sheets retain their full
multiplicity.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Occupied-image pair action after removing a source recurrence set before
forming the replica covariance.  Both endpoints are forced off return. -/
noncomputable def returnExcisedReplicaIncidenceAction
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ) (target : C → α → ℂ)
    (state : X → α → ℂ) (returnSet : Set X) : ℝ :=
  ∫ p in (returnSetᶜ ×ˢ returnSetᶜ),
    replicaTargetPairIncidenceKernel r target state p ∂(μ.prod μ)

/-- Source restriction before taking the product is exactly integration over
the return-free square.  In particular, no mixed return/nonreturn pair
survives. -/
theorem returnExcisedReplicaIncidenceAction_eq_restrictProduct
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [SFinite μ] (r : ℕ) (target : C → α → ℂ)
    (state : X → α → ℂ) (returnSet : Set X) :
    returnExcisedReplicaIncidenceAction μ r target state returnSet =
      ∫ p, replicaTargetPairIncidenceKernel r target state p
        ∂((μ.restrict returnSetᶜ).prod (μ.restrict returnSetᶜ)) := by
  unfold returnExcisedReplicaIncidenceAction
  rw [Measure.prod_restrict]

/-- Repeating target labels does not alter the return-excised action. -/
theorem returnExcisedReplicaIncidenceAction_duplicated
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ) (target : C → α → ℂ)
    (state : X → α → ℂ) (returnSet : Set X) :
    returnExcisedReplicaIncidenceAction μ r
        (duplicatedReplicaTarget target) state returnSet =
      returnExcisedReplicaIncidenceAction μ r target state returnSet := by
  unfold returnExcisedReplicaIncidenceAction
  rw [replicaTargetPairIncidenceKernel_duplicated]

/-- At positive replica order, adjoining the zero residual of an exact return
does not alter the return-excised action. -/
theorem returnExcisedReplicaIncidenceAction_withZero
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (returnSet : Set X) :
    returnExcisedReplicaIncidenceAction μ r
        (replicaTargetWithZero target) state returnSet =
      returnExcisedReplicaIncidenceAction μ r target state returnSet := by
  unfold returnExcisedReplicaIncidenceAction
  rw [replicaTargetPairIncidenceKernel_withZero hr]

/-- Every capture point is either in the removed recurrence set or remains in
the restricted source.  Thus recurrence mass is paid once, before any replica
moment or target-image rank appears. -/
theorem measureReal_capture_le_return_add_restrict_compl
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    (target : C → α → ℂ) (state : X → α → ℂ)
    (threshold : ℝ) (returnSet : Set X)
    (hreturn : MeasurableSet returnSet) :
    μ.real {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
      μ.real returnSet +
        (μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} := by
  let E : Set X :=
    {x | ∃ c, threshold ≤ finitePureStateFidelity (state x) (target c)}
  have hsub : E ⊆ returnSet ∪ (E ∩ returnSetᶜ) := by
    intro x hx
    by_cases hxReturn : x ∈ returnSet
    · exact Set.mem_union_left _ hxReturn
    · exact Set.mem_union_right _ ⟨hx, hxReturn⟩
  calc
    μ.real E ≤ μ.real (returnSet ∪ (E ∩ returnSetᶜ)) :=
      measureReal_mono hsub
    _ ≤ μ.real returnSet + μ.real (E ∩ returnSetᶜ) :=
      measureReal_union_le _ _
    _ = μ.real returnSet + (μ.restrict returnSetᶜ).real E := by
      rw [measureReal_restrict_apply' hreturn.compl]

/-- **Return-excised quenched coarea-incidence law.**  The full shortcut mass
is at most one recurrence mass plus the surviving shortcut mass.  The square
of that surviving mass, at matched replica threshold, is controlled by the
occupied-image Hilbert number times one pair action supported entirely on the
return-free square. -/
theorem quenchedReplica_returnExcisedCoareaIncidence_bound
    {X C α : Type*} [MeasurableSpace X] [Fintype C] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaTargetCoordinate r target (state x) i)
        (μ.restrict returnSetᶜ))
    (hcoord : ∀ i, Integrable
      (fun x => ‖replicaTargetCoordinate r target (state x) i‖ ^ (2 : ℕ))
        (μ.restrict returnSetᶜ)) :
    (μ.real {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
      μ.real returnSet +
        (μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)}) ∧
    (((μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} *
        threshold ^ r) ^ (2 : ℕ) ≤
      (replicaTargetHilbertNumber r target : ℝ) *
        returnExcisedReplicaIncidenceAction μ r target state returnSet) := by
  constructor
  · exact measureReal_capture_le_return_add_restrict_compl
      μ target state threshold returnSet hreturn
  · calc
      (((μ.restrict returnSetᶜ).real {x | ∃ c,
            threshold ≤ finitePureStateFidelity (state x) (target c)} *
          threshold ^ r) ^ (2 : ℕ)) ≤
          (replicaTargetHilbertNumber r target : ℝ) *
            replicaTargetIncidenceCollision
              (μ.restrict returnSetᶜ) r target state :=
        quenchedReplica_incidenceCovariance_bound
          (μ.restrict returnSetᶜ) hr target state htarget threshold
            hthreshold hcoord
      _ = (replicaTargetHilbertNumber r target : ℝ) *
          returnExcisedReplicaIncidenceAction
            μ r target state returnSet := by
        rw [replicaTargetIncidenceCollision_eq_integral_pairKernel
          (μ.restrict returnSetᶜ) r target state hmeas hcoord]
        rw [← returnExcisedReplicaIncidenceAction_eq_restrictProduct]

/-- Scalar form of the return-excision law.  Complete shortcut mass is at
most recurrence mass plus the square root of the return-free occupied-image
pair action, divided by the matched replica threshold. -/
theorem measureReal_capture_le_return_add_sqrt_action
    {X C α : Type*} [MeasurableSpace X] [Fintype C] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaTargetCoordinate r target (state x) i)
        (μ.restrict returnSetᶜ))
    (hcoord : ∀ i, Integrable
      (fun x => ‖replicaTargetCoordinate r target (state x) i‖ ^ (2 : ℕ))
        (μ.restrict returnSetᶜ)) :
    μ.real {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
      μ.real returnSet +
        Real.sqrt ((replicaTargetHilbertNumber r target : ℝ) *
          returnExcisedReplicaIncidenceAction
            μ r target state returnSet) / threshold ^ r := by
  have hcut := quenchedReplica_returnExcisedCoareaIncidence_bound
    μ hr target state htarget threshold hthreshold returnSet hreturn
      hmeas hcoord
  have hscaled :
      (μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} *
          threshold ^ r ≤
        Real.sqrt ((replicaTargetHilbertNumber r target : ℝ) *
          returnExcisedReplicaIncidenceAction
            μ r target state returnSet) :=
    Real.le_sqrt_of_sq_le hcut.2
  have hresidual :
      (μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
        Real.sqrt ((replicaTargetHilbertNumber r target : ℝ) *
          returnExcisedReplicaIncidenceAction
            μ r target state returnSet) / threshold ^ r :=
    (le_div_iff₀' (pow_pos hthreshold r)).2 (by
      simpa [mul_comm] using hscaled)
  exact hcut.1.trans (by
    simpa [add_comm] using add_le_add_left hresidual (μ.real returnSet))

end

end GaloisForLFunctions.HTGeometry
