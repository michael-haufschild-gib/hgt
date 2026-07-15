import GaloisForLFunctions.HTGeometry.NevanlinnaBauerRetract
import Mathlib.Probability.Distributions.Geometric

/-!
# Infinite-support probability laws inside infinite carriers

Every infinite subset of a Borel Hausdorff space carries an infinite-support probability law.
Mixing any carried law with such a reference law gives infinite support at every positive mixing
weight and converges weakly back to the original law as the weight vanishes.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

/-- A fixed nondegenerate geometric parameter. -/
private noncomputable def geometricHalf : unitInterval :=
  ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩

private theorem geometricHalf_ne_zero : geometricHalf ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  norm_num [geometricHalf] at this

private theorem geometricHalf_ne_one : geometricHalf ≠ 1 := by
  intro h
  have := congrArg Subtype.val h
  norm_num [geometricHalf] at this

/-- An infinite subset carries a probability measure with infinite topological support. -/
theorem exists_infiniteSupport_probabilityLawsCarriedBy
    {X : Type*} [TopologicalSpace X] [T1Space X]
    [MeasurableSpace X] [BorelSpace X]
    (K : Set X) (hKclosed : IsClosed K) (hK : K.Infinite) :
    ∃ kappa : ProbabilityMeasure X,
      kappa ∈ probabilityLawsCarriedBy K ∧
        ((kappa : ProbabilityMeasure X) : Measure X).support.Infinite := by
  let e : ℕ ↪ K := hK.natEmbedding
  let f : ℕ → X := fun n => e n
  have hf : Measurable f := measurable_of_countable f
  let kappa : ProbabilityMeasure X :=
    ⟨Measure.map f (geometricMeasure geometricHalf),
      Measure.isProbabilityMeasure_map hf.aemeasurable⟩
  have hkappaK : kappa ∈ probabilityLawsCarriedBy K := by
    change Measure.map f (geometricMeasure geometricHalf) Kᶜ = 0
    rw [Measure.map_apply hf hKclosed.measurableSet.compl]
    have hpre : f ⁻¹' Kᶜ = ∅ := by
      ext n
      simp [f, e]
    rw [hpre, measure_empty]
  have hfinj : Function.Injective f := by
    intro m n h
    exact e.injective (Subtype.ext h)
  have hrange : range f ⊆ (kappa : Measure X).support := by
    rintro x ⟨n, rfl⟩
    rw [Measure.mem_support_iff_forall]
    intro U hU
    have hmem : f n ∈ U := mem_of_mem_nhds hU
    have hsingle : 0 < (kappa : Measure X) {f n} := by
      change 0 < Measure.map f (geometricMeasure geometricHalf) {f n}
      rw [Measure.map_apply hf (measurableSet_singleton (f n))]
      have hpre : f ⁻¹' {f n} = {n} := by
        ext m
        simp only [mem_preimage, mem_singleton_iff]
        constructor
        · exact fun h => hfinj h
        · exact fun h => congrArg f h
      rw [hpre, geometricMeasure_singleton geometricHalf_ne_zero]
      exact ENNReal.ofReal_pos.mpr
        (geometricMeasure_pos geometricHalf_ne_zero geometricHalf_ne_one n)
    exact hsingle.trans_le (measure_mono (singleton_subset_iff.mpr hmem))
  exact ⟨kappa, hkappaK, (Set.infinite_range_of_injective hfinj).mono hrange⟩

/-- A positive coefficient on an infinite-support component forces the mixture to retain
infinite support. -/
theorem probabilityMixture_infiniteSupport_right
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (t : ℝ≥0∞) (ht : t ≤ 1) (hlt : t < 1)
    (mu nu : ProbabilityMeasure X)
    (hnu : ((nu : ProbabilityMeasure X) : Measure X).support.Infinite) :
    ((probabilityMixture t ht mu nu : ProbabilityMeasure X) : Measure X).support.Infinite := by
  have hsub : (nu : Measure X).support ⊆
      (probabilityMixture t ht mu nu : Measure X).support := by
    intro x hx
    rw [Measure.mem_support_iff_forall] at hx ⊢
    intro U hU
    have hnuU : 0 < (nu : Measure X) U := hx U hU
    rw [probabilityMixture_toMeasure, Measure.add_apply,
      Measure.smul_apply, Measure.smul_apply]
    simp only [smul_eq_mul]
    have hweight : 0 < 1 - t := tsub_pos_iff_lt.mpr hlt
    exact lt_of_lt_of_le (ENNReal.mul_pos hweight.ne' hnuU.ne')
      (le_add_left le_rfl)
  exact hnu.mono hsub

/-- Probability mixing is continuous in a real unit-interval weight for the weak topology. -/
theorem continuous_probabilityMixture_realWeight
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X]
    (mu nu : ProbabilityMeasure X) :
    Continuous fun t : Set.Icc (0 : ℝ) 1 =>
      probabilityMixture (ENNReal.ofReal t.1)
        (by simpa using ENNReal.ofReal_le_ofReal t.2.2) mu nu := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro g
  have hmu : Integrable g (mu : Measure X) := g.integrable _
  have hnu : Integrable g (nu : Measure X) := g.integrable _
  have heq : (fun t : Set.Icc (0 : ℝ) 1 =>
      ∫ x, g x ∂(probabilityMixture (ENNReal.ofReal t.1)
        (by simpa using ENNReal.ofReal_le_ofReal t.2.2) mu nu : Measure X)) =
      fun t => t.1 • (∫ x, g x ∂(mu : Measure X)) +
        (1 - t.1) • (∫ x, g x ∂(nu : Measure X)) := by
    funext t
    rw [probabilityMixture_toMeasure, integral_add_measure
      (hmu.smul_measure (by simp))
      (hnu.smul_measure (by
        exact ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top))),
      integral_smul_measure, integral_smul_measure]
    have hsub : (1 - ENNReal.ofReal t.1).toReal = 1 - t.1 := by
      rw [ENNReal.toReal_sub_of_le
        (by simpa using ENNReal.ofReal_le_ofReal t.2.2) (by simp)]
      simp [ENNReal.toReal_ofReal t.2.1]
    rw [hsub, ENNReal.toReal_ofReal t.2.1]
  rw [heq]
  fun_prop

/-- Carried probability laws, with the inherited weak topology. -/
abbrev CarriedProbabilityLaw {X : Type*} [MeasurableSpace X] (K : Set X) :=
  {mu : ProbabilityMeasure X // mu ∈ probabilityLawsCarriedBy K}

/-- Real weights increasing to one while retaining a strictly positive second component. -/
private noncomputable def approachOneWeight (n : ℕ) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - 1 / ((n : ℝ) + 1), by
    constructor
    · have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
        exact (div_le_one (by positivity)).mpr (by norm_num)
      linarith
    · exact sub_le_self _ (by positivity)⟩

private theorem approachOneWeight_lt_one (n : ℕ) :
    (approachOneWeight n : ℝ) < 1 := by
  dsimp [approachOneWeight]
  have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

private theorem approachOneWeight_tendsto :
    Tendsto approachOneWeight atTop
      (nhds (⟨1, by constructor <;> norm_num⟩ : Set.Icc (0 : ℝ) 1)) := by
  rw [tendsto_subtype_rng]
  simpa [approachOneWeight] using
    (tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

/-- Inside the laws carried by an infinite closed set, infinite-support laws are weakly dense. -/
theorem infiniteSupport_carriedProbabilityLaws_dense
    {X : Type*} [TopologicalSpace X] [T1Space X]
    [MeasurableSpace X] [BorelSpace X] [OpensMeasurableSpace X]
    (K : Set X) (hKclosed : IsClosed K) (hK : K.Infinite) :
    Dense {mu : CarriedProbabilityLaw K |
      ((mu.1 : ProbabilityMeasure X) : Measure X).support.Infinite} := by
  rw [dense_iff_closure_eq]
  apply top_unique
  intro eta _
  obtain ⟨kappa, hkappaK, hkappaInfinite⟩ :=
    exists_infiniteSupport_probabilityLawsCarriedBy K hKclosed hK
  let path : Set.Icc (0 : ℝ) 1 → ProbabilityMeasure X := fun t =>
    probabilityMixture (ENNReal.ofReal t.1)
      (by simpa using ENNReal.ofReal_le_ofReal t.2.2) eta.1 kappa
  have hpathContinuous : Continuous path := by
    simpa [path] using continuous_probabilityMixture_realWeight eta.1 kappa
  have hpathOne : path ⟨1, by constructor <;> norm_num⟩ = eta.1 := by
    apply ProbabilityMeasure.toMeasure_injective
    simp [path, probabilityMixture_toMeasure]
  let approx : ℕ → CarriedProbabilityLaw K := fun n =>
    ⟨path (approachOneWeight n), by
      change (path (approachOneWeight n) : Measure X) Kᶜ = 0
      rw [show (path (approachOneWeight n) : Measure X) =
          ENNReal.ofReal (approachOneWeight n : ℝ) • (eta.1 : Measure X) +
            (1 - ENNReal.ofReal (approachOneWeight n : ℝ)) •
              (kappa : Measure X) by
        rfl,
        Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        eta.2, hkappaK]
      simp⟩
  have happInfinite : ∀ n, approx n ∈ {mu : CarriedProbabilityLaw K |
      ((mu.1 : ProbabilityMeasure X) : Measure X).support.Infinite} := by
    intro n
    exact probabilityMixture_infiniteSupport_right
      (ENNReal.ofReal (approachOneWeight n : ℝ))
      (by simpa using ENNReal.ofReal_le_ofReal (approachOneWeight n).2.2)
      (ENNReal.ofReal_lt_one.mpr (approachOneWeight_lt_one n)) eta.1 kappa
      hkappaInfinite
  have happTendsto : Tendsto approx atTop (nhds eta) := by
    rw [tendsto_subtype_rng]
    rw [← hpathOne]
    exact hpathContinuous.continuousAt.tendsto.comp approachOneWeight_tendsto
  exact mem_closure_of_tendsto happTendsto
    (Eventually.of_forall happInfinite)

end

end GaloisForLFunctions.HTGeometry
