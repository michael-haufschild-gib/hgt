import GaloisForLFunctions.RHTower.RouteRStrongCompactApproximationBlindness

/-!
# Route R operator-topology compactness dichotomy

Let `C` be the compact ideal in the fixed physical operator space.  For any topology on that
operator space, a receiver in the closure of `C` is compact whenever `C` is closed.  Hence no
operator topology can simultaneously make Route R's nonneutral `(2,3)` receiver compactly
approximable and preserve compactness under passage to limits.

For the norm topology the classification is exact: approximation by a sequence of compact
operators is equivalent to compactness, hence for the fixed receiver it is equivalent to neutral
grade and globally equivalent to RH.  Together with the explicit strong compact approximation,
this closes every topology-only version of the proposed external handoff: weakening topology can
create approximants only by making the compact ideal nonclosed.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Fixed physical operator space used by the Route R Stokes--Calkin receiver. -/
abbrev RouteRPhysicalOperator :=
  ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2

/-- Compact ideal as a set, independent of any subsequently chosen topology on operator space. -/
def routeRCompactOperatorSet : Set RouteRPhysicalOperator :=
  {T | IsCompactOperator T}

/-- A topology is compactness-detecting when the physical compact ideal is closed in it. -/
def RouteROperatorTopologyClosesCompactIdeal
    (τ : TopologicalSpace RouteRPhysicalOperator) : Prop :=
  @IsClosed RouteRPhysicalOperator τ routeRCompactOperatorSet

/-- A topology compactly approximates an operator when that operator belongs to the closure of the
physical compact ideal. -/
def RouteROperatorTopologyCompactlyApproximates
    (τ : TopologicalSpace RouteRPhysicalOperator)
    (T : RouteRPhysicalOperator) : Prop :=
  T ∈ @closure RouteRPhysicalOperator τ routeRCompactOperatorSet

/-- **Topology-independent closure law.**  Compact approximation can imply compactness only when
the chosen operator topology keeps the compact ideal closed. -/
theorem isCompactOperator_of_operatorTopology_closed_of_compactlyApproximates
    (τ : TopologicalSpace RouteRPhysicalOperator)
    (T : RouteRPhysicalOperator)
    (hclosed : RouteROperatorTopologyClosesCompactIdeal τ)
    (happrox : RouteROperatorTopologyCompactlyApproximates τ T) :
    IsCompactOperator T := by
  letI := τ
  exact hclosed.closure_subset happrox

/-- **Universal topology-only no-go on the actual receiver.**  Away from neutral grade, no
topology can both close the compact ideal and place the fixed Route R receiver in its closure. -/
theorem no_routeRTwoThree_operatorTopology_closed_and_compactlyApproximates
    {A : ℝ} (hA : 0 < A) {a : ℝ} (ha : a ≠ 0)
    (τ : TopologicalSpace RouteRPhysicalOperator) :
    ¬(RouteROperatorTopologyClosesCompactIdeal τ ∧
      RouteROperatorTopologyCompactlyApproximates τ
        (routeRTwoThreeStokesSoninCommutator A a)) := by
  rintro ⟨hclosed, happrox⟩
  have hcompact :=
    isCompactOperator_of_operatorTopology_closed_of_compactlyApproximates
      τ (routeRTwoThreeStokesSoninCommutator A a) hclosed happrox
  exact ha
    ((routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff hA a).1 hcompact)

/-- Sequential norm-approximation by compact physical operators. -/
def IsNormCompactlyApproximable (T : RouteRPhysicalOperator) : Prop :=
  ∃ K : ℕ → RouteRPhysicalOperator,
    (∀ N, IsCompactOperator (K N)) ∧
      Tendsto K atTop (nhds T)

/-- Compact operators are norm closed, so sequential norm compact-approximability is exactly
compactness. -/
theorem isNormCompactlyApproximable_iff_isCompactOperator
    (T : RouteRPhysicalOperator) :
    IsNormCompactlyApproximable T ↔ IsCompactOperator T := by
  constructor
  · rintro ⟨K, hK, hconv⟩
    exact isCompactOperator_of_tendsto hconv (Filter.Eventually.of_forall hK)
  · intro hT
    exact ⟨fun _ => T, fun _ => hT, tendsto_const_nhds⟩

/-- On the fixed `(2,3)` receiver, norm compact-approximability cuts out exactly neutral grade. -/
theorem routeRTwoThreeStokesSoninCommutator_normCompactlyApproximable_iff
    {A : ℝ} (hA : 0 < A) (a : ℝ) :
    IsNormCompactlyApproximable
        (routeRTwoThreeStokesSoninCommutator A a) ↔
      a = 0 := by
  rw [isNormCompactlyApproximable_iff_isCompactOperator,
    routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff hA]

/-- Global norm compact-approximability of the fixed source-selected receiver is exactly RH. -/
theorem routeRTwoThreeStokesSoninCommutator_globalNormCompactlyApproximable_iff_rh
    {A : ℝ} (hA : 0 < A) :
    (∀ rho : XiDivisorSupport,
      IsNormCompactlyApproximable
        (routeRTwoThreeStokesSoninCommutator A
          (primeDepthBVWoldXiCenteredRate rho))) ↔
      RiemannHypothesis := by
  simpa only [isNormCompactlyApproximable_iff_isCompactOperator] using
    routeRTwoThreeStokesSoninCommutator_globalCompact_iff_riemannHypothesis hA

end

end RHTower
