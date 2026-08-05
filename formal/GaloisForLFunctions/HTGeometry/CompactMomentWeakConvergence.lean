import GaloisForLFunctions.HTGeometry.TorusFourierWeakConvergenceLaw

/-!
# Moments determine and control laws on a compact interval

On a compact interval the monomials span a dense subalgebra of the continuous functions, so two
laws with the same moments coincide, and a family of laws whose moments converge converges weakly.

The density step is used directly rather than through a closed-kernel argument: a continuous
function is uniformly approximated by a polynomial, and the integral of a function against a law is
bounded by its uniform norm, so the difference of the two integral functionals is smaller than any
tolerance.  Weak convergence then follows from compactness of the space of laws on a compact space
together with uniqueness of cluster points.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a b : ℝ}

/-- A continuous function on a compact space is integrable against a finite measure. -/
theorem integrable_continuousMap_of_compactSpace {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (f : C(X, ℝ)) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable (fun x => f x) μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Integration of a continuous function depends continuously on a law over a compact space. -/
theorem continuous_integral_real_continuousMap {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (f : C(X, ℝ)) :
    Continuous fun μ : ProbabilityMeasure X => ∫ x, f x ∂(μ : Measure X) := by
  rw [continuous_iff_continuousAt]
  intro μ
  have hid : Tendsto (fun ν : ProbabilityMeasure X => ν) (𝓝 μ) (𝓝 μ) := tendsto_id
  have hall := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hid
  have h := hall (ContinuousMap.equivBoundedOfCompact X ℝ f)
  have h' : Tendsto (fun i : ProbabilityMeasure X => ∫ ω, f ω ∂(i : Measure X)) (𝓝 μ)
      (𝓝 (∫ ω, f ω ∂(μ : Measure X))) := by simpa using h
  exact h'

/-- The integral of a continuous function against a law is bounded by its uniform norm. -/
theorem abs_integral_continuousMap_le {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X] (f : C(X, ℝ)) (μ : Measure X)
    [IsProbabilityMeasure μ] : |∫ x, f x ∂μ| ≤ ‖f‖ := by
  have hbound : ‖∫ x, f x ∂μ‖ ≤ ‖f‖ * (μ univ).toReal :=
    norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x)
  rw [measure_univ] at hbound
  simpa using hbound

/-- Polynomial integrals are determined by the moments. -/
theorem integral_polynomial_eq_sum (μ : Measure (Icc a b)) [IsFiniteMeasure μ]
    (p : Polynomial ℝ) :
    ∫ y, (p.toContinuousMapOn (Icc a b)) y ∂μ
      = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * ∫ y, ((y : ℝ) ^ k) ∂μ := by
  have hpt : ∀ y : Icc a b, (p.toContinuousMapOn (Icc a b)) y
      = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * ((y : ℝ) ^ k) := by
    intro y
    simpa using p.eval_eq_sum_range (x := (y : ℝ))
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_finsetSum]
  · exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  · intro k _
    exact (Continuous.integrable_of_hasCompactSupport
      (by fun_prop : Continuous fun y : Icc a b => p.coeff k * ((y : ℝ) ^ k))
      (HasCompactSupport.of_compactSpace _))

/-- **Moments determine a law on a compact interval.** -/
theorem probabilityMeasure_ext_of_integral_pow_eq (μ ν : ProbabilityMeasure (Icc a b))
    [Nonempty (Icc a b)]
    (h : ∀ k : ℕ, (∫ y, ((y : ℝ) ^ k) ∂(μ : Measure (Icc a b)))
        = ∫ y, ((y : ℝ) ^ k) ∂(ν : Measure (Icc a b))) :
    μ = ν := by
  have hpoly : ∀ p : Polynomial ℝ,
      (∫ y, (p.toContinuousMapOn (Icc a b)) y ∂(μ : Measure (Icc a b)))
        = ∫ y, (p.toContinuousMapOn (Icc a b)) y ∂(ν : Measure (Icc a b)) := by
    intro p
    rw [integral_polynomial_eq_sum _ p, integral_polynomial_eq_sum _ p]
    exact Finset.sum_congr rfl fun k _ => by rw [h k]
  have hall : ∀ f : C(Icc a b, ℝ),
      (∫ y, f y ∂(μ : Measure (Icc a b))) = ∫ y, f y ∂(ν : Measure (Icc a b)) := by
    intro f
    have hmem : f ∈ (polynomialFunctions (Icc a b)).topologicalClosure := by
      rw [polynomialFunctions_closure_eq_top a b]
      exact Algebra.mem_top
    refine sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add ?_)
      (abs_nonneg _)))
    intro ε hε
    obtain ⟨g, hg, hgdist⟩ := Metric.mem_closure_iff.mp hmem (ε / 3) (by linarith)
    obtain ⟨p, -, hp⟩ := hg
    have hgf : ‖f - g‖ < ε / 3 := by
      rw [← dist_eq_norm]
      exact hgdist
    have hbμ : |∫ y, (f - g) y ∂(μ : Measure (Icc a b))| ≤ ‖f - g‖ :=
      abs_integral_continuousMap_le _ _
    have hbν : |∫ y, (f - g) y ∂(ν : Measure (Icc a b))| ≤ ‖f - g‖ :=
      abs_integral_continuousMap_le _ _
    have hsubμ : (∫ y, (f - g) y ∂(μ : Measure (Icc a b)))
        = (∫ y, f y ∂(μ : Measure (Icc a b))) - ∫ y, g y ∂(μ : Measure (Icc a b)) := by
      simpa using integral_sub (integrable_continuousMap_of_compactSpace f _) (integrable_continuousMap_of_compactSpace g _)
    have hsubν : (∫ y, (f - g) y ∂(ν : Measure (Icc a b)))
        = (∫ y, f y ∂(ν : Measure (Icc a b))) - ∫ y, g y ∂(ν : Measure (Icc a b)) := by
      simpa using integral_sub (integrable_continuousMap_of_compactSpace f _) (integrable_continuousMap_of_compactSpace g _)
    have hgeq : (∫ y, g y ∂(μ : Measure (Icc a b))) = ∫ y, g y ∂(ν : Measure (Icc a b)) := by
      rw [← hp]
      exact hpoly p
    rw [hsubμ, hgeq] at hbμ
    rw [hsubν] at hbν
    rw [abs_sub_comm] at hbν
    have htri := abs_sub_le (∫ y, f y ∂(μ : Measure (Icc a b)))
      (∫ y, g y ∂(ν : Measure (Icc a b))) (∫ y, f y ∂(ν : Measure (Icc a b)))
    linarith
  apply ProbabilityMeasure.toMeasure_injective
  refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  exact hall (ContinuousMap.mk (fun y => f y) f.continuous)

/-- **Weak convergence from moment convergence on a compact interval.** -/
theorem probabilityMeasure_tendsto_of_integral_pow_tendsto {α : Type*} {l : Filter α}
    [Nonempty (Icc a b)] (μs : α → ProbabilityMeasure (Icc a b)) (μ : ProbabilityMeasure (Icc a b))
    (h : ∀ k : ℕ, Tendsto (fun i => ∫ y, ((y : ℝ) ^ k) ∂(μs i : Measure (Icc a b))) l
      (𝓝 (∫ y, ((y : ℝ) ^ k) ∂(μ : Measure (Icc a b))))) :
    Tendsto μs l (𝓝 μ) := by
  refine tendsto_nhds_of_unique_mapClusterPt fun ν hν => ?_
  refine probabilityMeasure_ext_of_integral_pow_eq ν μ fun k => ?_
  have hcontF : Continuous fun ρ : ProbabilityMeasure (Icc a b) =>
      ∫ y, ((y : ℝ) ^ k) ∂(ρ : Measure (Icc a b)) :=
    continuous_integral_real_continuousMap
      (ContinuousMap.mk (fun y : Icc a b => ((y : ℝ) ^ k)) (by fun_prop))
  have hcluster : MapClusterPt (∫ y, ((y : ℝ) ^ k) ∂(ν : Measure (Icc a b))) l
      (fun i => ∫ y, ((y : ℝ) ^ k) ∂(μs i : Measure (Icc a b))) :=
    hν.continuousAt_comp hcontF.continuousAt
  exact eq_of_mapClusterPt_of_tendsto hcluster (h k)

end

end GaloisForLFunctions.HTGeometry
