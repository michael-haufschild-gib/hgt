import GaloisForLFunctions.RHTower.RouteROperatorTopologyCompactnessDichotomy

/-!
# Route R strong approximation compact escape

Pointwise convergence to a bounded operator becomes compactness as soon as all approximating images
of the unit ball lie in one compact set.  Therefore Route R's explicit compact Hilbert-basis
truncations can converge strongly to a nonneutral receiver only by escaping every common compact
envelope.  This is the exact positive residue of strong-topology blindness: failure is loss of
uniform tightness, not failure of finite-stage compactness.
-/

open Complex Filter Topology Metric Set

namespace RHTower

noncomputable section

/-- A pointwise operator limit is compact if all stage images of the unit ball share one compact
envelope.  Individual stage compactness is not needed. -/
theorem isCompactOperator_of_pointwise_tendsto_of_common_compact_envelope
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (K : ι → RouteRPhysicalOperator) (T : RouteRPhysicalOperator)
    (hconv : ∀ x, Tendsto (fun i => K i x) l (nhds (T x)))
    (C : Set ArchimedeanWeightedL2) (hC : IsCompact C)
    (hcontain : ∀ i, K i '' ball 0 1 ⊆ C) :
    IsCompactOperator T := by
  refine ⟨C, hC, ?_⟩
  apply Filter.mem_of_superset (ball_mem_nhds (0 : ArchimedeanWeightedL2) one_pos)
  intro x hx
  exact hC.isClosed.mem_of_tendsto (hconv x)
    (Filter.Eventually.of_forall fun i => hcontain i ⟨x, hx, rfl⟩)

/-- **Compact-escape law for the actual Route R receiver.**  At nonneutral grade, every compact
subset of physical Hilbert space misses some unit-ball value of some finite Hilbert-basis
truncation. -/
theorem routeRTwoThreeStokesStrongCompactApproximation_escapes_every_compact
    {A : ℝ} (hA : 0 < A) {a : ℝ} (ha : a ≠ 0)
    (C : Set ArchimedeanWeightedL2) (hC : IsCompact C) :
    ∃ s : Finset (exists_hilbertBasis ℂ ArchimedeanWeightedL2).choose,
      ∃ x ∈ ball (0 : ArchimedeanWeightedL2) 1,
        routeRTwoThreeStokesStrongCompactApproximation A a s x ∉ C := by
  by_contra hescape
  have hcontain : ∀ s,
      routeRTwoThreeStokesStrongCompactApproximation A a s ''
          ball (0 : ArchimedeanWeightedL2) 1 ⊆ C := by
    intro s y hy
    rcases hy with ⟨x, hx, rfl⟩
    by_contra hnot
    exact hescape ⟨s, x, hx, hnot⟩
  have hcompact : IsCompactOperator (routeRTwoThreeStokesSoninCommutator A a) :=
    isCompactOperator_of_pointwise_tendsto_of_common_compact_envelope
      (routeRTwoThreeStokesStrongCompactApproximation A a)
      (routeRTwoThreeStokesSoninCommutator A a)
      (routeRTwoThreeStokesStrongCompactApproximation_tendsto_pointwise A a)
      C hC hcontain
  exact ha
    ((routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff hA a).1 hcompact)

/-- Existence of compact stages converging strongly with a common compact unit-ball envelope. -/
def IsCollectivelyCompactStronglyApproximable
    (T : RouteRPhysicalOperator) : Prop :=
  ∃ K : ℕ → RouteRPhysicalOperator,
    (∀ N, IsCompactOperator (K N)) ∧
      (∀ x, Tendsto (fun N => K N x) atTop (nhds (T x))) ∧
      ∃ C : Set ArchimedeanWeightedL2,
        IsCompact C ∧ ∀ N, K N '' ball 0 1 ⊆ C

/-- Collective compactness is the exact uniform-tightness supplement that upgrades strong
approximation to physical compactness. -/
theorem isCollectivelyCompactStronglyApproximable_iff_isCompactOperator
    (T : RouteRPhysicalOperator) :
    IsCollectivelyCompactStronglyApproximable T ↔ IsCompactOperator T := by
  constructor
  · rintro ⟨K, -, hconv, C, hC, hcontain⟩
    exact isCompactOperator_of_pointwise_tendsto_of_common_compact_envelope
      K T hconv C hC hcontain
  · intro hT
    obtain ⟨C, hC, hcontain⟩ := hT.image_ball_subset_compact 1
    exact ⟨fun _ => T, fun _ => hT, fun _ => tendsto_const_nhds,
      C, hC, fun _ => hcontain⟩

/-- On the fixed receiver, collectively compact strong approximation cuts out neutral grade. -/
theorem routeRTwoThreeStokesSoninCommutator_collectivelyCompactStronglyApproximable_iff
    {A : ℝ} (hA : 0 < A) (a : ℝ) :
    IsCollectivelyCompactStronglyApproximable
        (routeRTwoThreeStokesSoninCommutator A a) ↔
      a = 0 := by
  rw [isCollectivelyCompactStronglyApproximable_iff_isCompactOperator,
    routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff hA]

/-- Global collective compactness of a strong approximation is exactly RH on the fixed source
receiver. -/
theorem routeRTwoThreeStokesSoninCommutator_globalCollectivelyCompactStronglyApproximable_iff_rh
    {A : ℝ} (hA : 0 < A) :
    (∀ rho : XiDivisorSupport,
      IsCollectivelyCompactStronglyApproximable
        (routeRTwoThreeStokesSoninCommutator A
          (primeDepthBVWoldXiCenteredRate rho))) ↔
      RiemannHypothesis := by
  simpa only [isCollectivelyCompactStronglyApproximable_iff_isCompactOperator] using
    routeRTwoThreeStokesSoninCommutator_globalCompact_iff_riemannHypothesis hA

/-- At neutral grade the two curvature coefficients agree, so the fixed compressed commutator is
literally zero. -/
@[simp] theorem routeRTwoThreeStokesSoninCommutator_zero_grade (A : ℝ) :
    routeRTwoThreeStokesSoninCommutator A 0 = 0 := by
  rw [routeRTwoThreeStokesSoninCommutator_eq_neg_orientationGram]
  have hconst : ∀ i j : Fin 2,
      routeRTwoThreeStokesCurvaturePacket 0 i =
        routeRTwoThreeStokesCurvaturePacket 0 j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [routeRTwoThreeStokesCurvaturePacket]
  have hmatrix :
      finiteEulerOrientationMatrix (routeRTwoThreeStokesCurvaturePacket 0) = 0 :=
    (finiteEulerOrientationMatrix_eq_zero_iff _).2 hconst
  rw [finiteArchimedeanEulerOrientationGram, hmatrix]
  simp [finiteArchimedeanPrimeEulerGramCombination]

/-- Common compact-envelope property for the canonical Hilbert-basis truncation net itself. -/
def RouteRTwoThreeCanonicalStrongApproximationHasCompactEnvelope
    (A a : ℝ) : Prop :=
  ∃ C : Set ArchimedeanWeightedL2,
    IsCompact C ∧
      ∀ s : Finset (exists_hilbertBasis ℂ ArchimedeanWeightedL2).choose,
        routeRTwoThreeStokesStrongCompactApproximation A a s '' ball 0 1 ⊆ C

/-- The canonical compact strong approximation is uniformly tight exactly at neutral grade. -/
theorem routeRTwoThreeCanonicalStrongApproximation_hasCompactEnvelope_iff
    {A : ℝ} (hA : 0 < A) (a : ℝ) :
    RouteRTwoThreeCanonicalStrongApproximationHasCompactEnvelope A a ↔ a = 0 := by
  constructor
  · rintro ⟨C, hC, hcontain⟩
    have hcompact : IsCompactOperator (routeRTwoThreeStokesSoninCommutator A a) :=
      isCompactOperator_of_pointwise_tendsto_of_common_compact_envelope
        (routeRTwoThreeStokesStrongCompactApproximation A a)
        (routeRTwoThreeStokesSoninCommutator A a)
        (routeRTwoThreeStokesStrongCompactApproximation_tendsto_pointwise A a)
        C hC hcontain
    exact (routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff hA a).1 hcompact
  · rintro rfl
    refine ⟨{0}, isCompact_singleton, ?_⟩
    intro s y hy
    rcases hy with ⟨x, -, rfl⟩
    simp [routeRTwoThreeStokesStrongCompactApproximation,
      ContinuousLinearMap.hsTruncation_apply]

end

end RHTower
