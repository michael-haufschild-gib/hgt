import GaloisForLFunctions.RHTower.WeilPaperPhaseCovarianceRecovery
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Algebra.IsUniformGroup.Constructions


/-!
# Finite covariance control on compact spectral completions

The covariance recovery embedding turns compactness into a finite measurement
principle: finitely many off-diagonal coordinates at one positive precision
uniformly control any continuous metric-valued observable. In particular they
control every bounded spectral expectation, and finite families simultaneously.
No numerical or effective bound on the required coordinates is asserted.
-/

open MeasureTheory Filter Set Topology Uniformity
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

private theorem finite_coordinate_control {κ β : Type*} [PseudoMetricSpace β]
    (K : Set (κ → ℝ)) [CompactSpace K] (E : C(K, β)) (δ : {r : ℝ // 0 < r}) :
    ∃ s : Finset κ, ∃ ε : {r : ℝ // 0 < r}, ∀ x y : K,
      (∀ k ∈ s, |x.1 k - y.1 k| < ε.1) → dist (E x) (E y) < δ.1 := by
  classical
  have hE := CompactSpace.uniformContinuous_of_continuous E.continuous
  have hu : {p : K × K | dist (E p.1) (E p.2) < δ.1} ∈ 𝓤 K :=
    hE (Metric.dist_mem_uniformity δ.2)
  have hb : (𝓝 (0 : κ → ℝ)).HasBasis
      (fun q : Set κ × ℝ => q.1.Finite ∧ 0 < q.2)
      (fun q => q.1.pi (fun _ => Metric.ball 0 q.2)) := by
    rw [nhds_pi]
    exact Metric.nhds_basis_ball.pi_self
  rw [uniformity_subtype, uniformity_eq_comap_nhds_zero (κ → ℝ), comap_comap] at hu
  obtain ⟨⟨s, ε⟩, ⟨hs, hε⟩, hsub⟩ := (hb.comap _).mem_iff.mp hu
  refine ⟨hs.toFinset, ⟨ε, hε⟩, fun x y hxy => @hsub (x, y) ?_⟩
  change ∀ k ∈ s, (y.1 - x.1) k ∈ Metric.ball 0 ε
  intro k hk
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, Pi.sub_apply, abs_sub_comm]
    using hxy k (hs.mem_toFinset.mpr hk)

variable {ι : Type*}

/-- Finitely many covariance coordinates control every continuous metric-valued
observable uniformly over the entire compact completion. -/
theorem exists_paperFiniteCovarianceControl {β : Type*} [PseudoMetricSpace β]
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (E : C(PaperObservedSpectralCompletion c F, β)) (δ : {r : ℝ // 0 < r}) :
    ∃ s : Finset (LogIndex × LogIndex × Bool), ∃ ε : {r : ℝ // 0 < r},
      ∀ μ ν : PaperObservedSpectralCompletion c F,
        (∀ k ∈ s, |paperObservedPhaseCovariances c F μ k -
          paperObservedPhaseCovariances c F ν k| < ε.1) → dist (E μ) (E ν) < δ.1 := by
  let K := Set.range (paperObservedPhaseCovariances c F)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (isCompact_paperObservedPhaseCovariances_range c F)
  obtain ⟨s, ε, h⟩ := finite_coordinate_control K (E.comp (paperPhaseCovarianceRecovery c F)) δ
  refine ⟨s, ε, fun μ ν hμν => ?_⟩
  have hp := h (paperPhaseCovarianceRecoveryHomeomorph c F μ)
    (paperPhaseCovarianceRecoveryHomeomorph c F ν) hμν
  have hμ : (E.comp (paperPhaseCovarianceRecovery c F))
      (paperPhaseCovarianceRecoveryHomeomorph c F μ) = E μ :=
    congrArg E (paperPhaseCovarianceRecovery_roundtrip c F μ)
  have hν : (E.comp (paperPhaseCovarianceRecovery c F))
      (paperPhaseCovarianceRecoveryHomeomorph c F ν) = E ν :=
    congrArg E (paperPhaseCovarianceRecovery_roundtrip c F ν)
  rwa [hμ, hν] at hp

/-- The universally fixed diagonal never needs to be measured. -/
theorem exists_paperOffDiagonalFiniteCovarianceControl {β : Type*} [PseudoMetricSpace β]
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (E : C(PaperObservedSpectralCompletion c F, β)) (δ : {r : ℝ // 0 < r}) :
    ∃ s : Finset (LogIndex × LogIndex × Bool), (∀ k ∈ s, k.1 ≠ k.2.1) ∧
      ∃ ε : {r : ℝ // 0 < r}, ∀ μ ν : PaperObservedSpectralCompletion c F,
        (∀ k ∈ s, |paperObservedPhaseCovariances c F μ k -
          paperObservedPhaseCovariances c F ν k| < ε.1) → dist (E μ) (E ν) < δ.1 := by
  classical
  obtain ⟨s, ε, h⟩ := exists_paperFiniteCovarianceControl c F E δ
  refine ⟨s.filter (fun k => k.1 ≠ k.2.1), ?_, ε, fun μ ν hμν => h μ ν ?_⟩
  · intro k hk
    exact (Finset.mem_filter.mp hk).2
  · rintro ⟨n, m, b⟩ hk
    by_cases hnm : n = m
    · subst m
      have heq : paperObservedPhaseCovariances c F μ (n, n, b) =
          paperObservedPhaseCovariances c F ν (n, n, b) := by
        cases b
        · exact (paperObservedPhaseCovariances_diagonal c F μ n).1.trans
            (paperObservedPhaseCovariances_diagonal c F ν n).1.symm
        · exact (paperObservedPhaseCovariances_diagonal c F μ n).2.trans
            (paperObservedPhaseCovariances_diagonal c F ν n).2.symm
      simpa only [heq, sub_self, abs_zero] using ε.2
    · exact hμν (n, m, b) (Finset.mem_filter.mpr ⟨hk, hnm⟩)

/-- Any bounded real spectral expectation is uniformly controlled by finitely
many off-diagonal phase covariances at a positive common precision. -/
theorem exists_paperBoundedObservable_finiteCovarianceControl
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ) (δ : {r : ℝ // 0 < r}) :
    ∃ s : Finset (LogIndex × LogIndex × Bool), (∀ k ∈ s, k.1 ≠ k.2.1) ∧
      ∃ ε : {r : ℝ // 0 < r}, ∀ μ ν : PaperObservedSpectralCompletion c F,
        (∀ k ∈ s, |paperObservedPhaseCovariances c F μ k -
          paperObservedPhaseCovariances c F ν k| < ε.1) →
        |(∫ ξ, G ξ ∂(μ.1 : Measure ℝ)) - ∫ ξ, G ξ ∂(ν.1 : Measure ℝ)| < δ.1 := by
  let E : C(PaperObservedSpectralCompletion c F, ℝ) :=
    ⟨fun μ => ∫ ξ, G ξ ∂(μ.1 : Measure ℝ),
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction G).comp
        continuous_subtype_val⟩
  obtain ⟨s, hs, ε, h⟩ := exists_paperOffDiagonalFiniteCovarianceControl c F E δ
  refine ⟨s, hs, ε, fun μ ν hμν => ?_⟩
  have hp : dist (∫ ξ, G ξ ∂(μ.1 : Measure ℝ)) (∫ ξ, G ξ ∂(ν.1 : Measure ℝ)) < δ.1 :=
    h μ ν hμν
  simpa only [Real.dist_eq] using hp

/-- The same finite off-diagonal measurements control a complex spectral expectation. -/
theorem exists_paperComplexObservable_finiteCovarianceControl
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℂ) (δ : {r : ℝ // 0 < r}) :
    ∃ s : Finset (LogIndex × LogIndex × Bool), (∀ k ∈ s, k.1 ≠ k.2.1) ∧
      ∃ ε : {r : ℝ // 0 < r}, ∀ μ ν : PaperObservedSpectralCompletion c F,
        (∀ k ∈ s, |paperObservedPhaseCovariances c F μ k -
          paperObservedPhaseCovariances c F ν k| < ε.1) →
        ‖(∫ ξ, G ξ ∂(μ.1 : Measure ℝ)) - ∫ ξ, G ξ ∂(ν.1 : Measure ℝ)‖ < δ.1 := by
  let E : C(PaperObservedSpectralCompletion c F, ℂ) :=
    ⟨fun μ => ∫ ξ, G ξ ∂(μ.1 : Measure ℝ), by
      apply continuous_iff_continuousAt.mpr
      intro μ
      exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
        (continuous_subtype_val.tendsto μ) G⟩
  obtain ⟨s, hs, ε, h⟩ := exists_paperOffDiagonalFiniteCovarianceControl c F E δ
  refine ⟨s, hs, ε, fun μ ν hμν => ?_⟩
  have hp : dist (∫ ξ, G ξ ∂(μ.1 : Measure ℝ)) (∫ ξ, G ξ ∂(ν.1 : Measure ℝ)) < δ.1 :=
    h μ ν hμν
  simpa only [dist_eq_norm] using hp

/-- One finite set and one positive precision suffice simultaneously for every
observable in an arbitrary finite complex family. -/
theorem exists_paperFiniteObservables_finiteCovarianceControl
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (n : ℕ)
    (G : Fin n → ℝ →ᵇ ℂ) (δ : {r : ℝ // 0 < r}) :
    ∃ s : Finset (LogIndex × LogIndex × Bool), (∀ k ∈ s, k.1 ≠ k.2.1) ∧
      ∃ ε : {r : ℝ // 0 < r}, ∀ μ ν : PaperObservedSpectralCompletion c F,
        (∀ k ∈ s, |paperObservedPhaseCovariances c F μ k -
          paperObservedPhaseCovariances c F ν k| < ε.1) → ∀ j : Fin n,
        ‖(∫ ξ, G j ξ ∂(μ.1 : Measure ℝ)) - ∫ ξ, G j ξ ∂(ν.1 : Measure ℝ)‖ < δ.1 := by
  let E : C(PaperObservedSpectralCompletion c F, Fin n → ℂ) :=
    ⟨fun μ j => ∫ ξ, G j ξ ∂(μ.1 : Measure ℝ), continuous_pi fun j => by
      apply continuous_iff_continuousAt.mpr
      intro μ
      exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
        (continuous_subtype_val.tendsto μ) (G j)⟩
  obtain ⟨s, hs, ε, h⟩ := exists_paperOffDiagonalFiniteCovarianceControl c F E δ
  refine ⟨s, hs, ε, fun μ ν hμν j => ?_⟩
  have hp : dist (∫ ξ, G j ξ ∂(μ.1 : Measure ℝ))
      (∫ ξ, G j ξ ∂(ν.1 : Measure ℝ)) < δ.1 := (dist_pi_lt_iff δ.2).mp (h μ ν hμν) j
  simpa only [dist_eq_norm] using hp

end RHTower.WeilWorkPBAP
