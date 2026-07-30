import GaloisForLFunctions.HTGeometry.AtomlessProbabilityLaws
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Singular probability laws as a dense `G_delta`

For a fixed atomless reference probability measure, singular probability laws
form a `G_delta` in the weak topology.  The countable open approximation law
uses summable geometric error thresholds.  Its reverse implication is the
first Borel--Cantelli lemma.

Density is proved independently by measurable quantization: every law can be
pushed through countable-range maps that move every point by an arbitrarily
small amount.  The pushforwards are singular to any atomless Borel reference,
and their Levy--Prokhorov distance from the original law tends to zero.
-/

open MeasureTheory Set Filter Metric Topology
open TopologicalSpace
open scoped ENNReal NNReal Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Summable error thresholds for the singularity approximation law. -/
def singularThreshold (n : ℕ) : ℝ≥0∞ :=
  (2⁻¹ : ℝ≥0∞) ^ (n + 1)

theorem singularThreshold_pos (n : ℕ) : 0 < singularThreshold n := by
  apply ENNReal.pow_pos
  exact ENNReal.inv_pos.mpr (by norm_num)

theorem singularThreshold_tsum : ∑' n, singularThreshold n = 1 := by
  rw [show (fun n => singularThreshold n) =
      fun n => (2⁻¹ : ℝ≥0∞) ^ (n + 1) by rfl]
  rw [ENNReal.tsum_geometric_add_one]
  rw [ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)

variable {X : Type*} [MeasurableSpace X] [MetricSpace X]

/-- At scale `n`, a law and the reference law are almost carried by
complementary sides of an open set. -/
def singularApproximation
    (reference : ProbabilityMeasure X) (n : ℕ) : Set (ProbabilityMeasure X) :=
  {mu | ∃ U : Set X, IsOpen U ∧
    (reference : Measure X) U < singularThreshold n ∧
    (mu : Measure X) Uᶜ < singularThreshold n}

theorem singularApproximation_isOpen
    [OpensMeasurableSpace X]
    (reference : ProbabilityMeasure X) (n : ℕ) :
    IsOpen (singularApproximation reference n) := by
  rw [isOpen_iff_mem_nhds]
  rintro mu ⟨U, hU, href, hmu⟩
  have hnhds := (closedMassBelow_isOpen Uᶜ hU.isClosed_compl
    (singularThreshold n)).mem_nhds hmu
  apply Filter.mem_of_superset hnhds
  intro nu hnu
  exact ⟨U, hU, href, hnu⟩

/-- Laws mutually singular to a fixed reference probability law. -/
def singularProbabilityLaws
    (reference : ProbabilityMeasure X) : Set (ProbabilityMeasure X) :=
  {mu | (mu : Measure X) ⟂ₘ (reference : Measure X)}

theorem mutuallySingular_mem_singularApproximation
    (reference mu : ProbabilityMeasure X)
    [Measure.OuterRegular (reference : Measure X)]
    (h : (mu : Measure X) ⟂ₘ (reference : Measure X)) (n : ℕ) :
    mu ∈ singularApproximation reference n := by
  let S := h.nullSetᶜ
  have hrefS : (reference : Measure X) S = 0 := h.measure_compl_nullSet
  obtain ⟨U, hSU, hU, hrefU⟩ := S.exists_isOpen_lt_of_lt
    (μ := (reference : Measure X)) (singularThreshold n) (by
      rw [hrefS]
      exact singularThreshold_pos n)
  refine ⟨U, hU, hrefU, ?_⟩
  have hzero : (mu : Measure X) Uᶜ = 0 := by
    apply measure_mono_null
    · intro x hx
      by_contra hxs
      exact hx (hSU hxs)
    · exact h.measure_nullSet
  rw [hzero]
  exact singularThreshold_pos n

theorem mutuallySingular_of_mem_all_singularApproximation
    (reference mu : ProbabilityMeasure X)
    (h : ∀ n, mu ∈ singularApproximation reference n) :
    (mu : Measure X) ⟂ₘ (reference : Measure X) := by
  choose U hUopen hrefU hmuU using h
  have hrefSum : (∑' n, (reference : Measure X) (U n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      ∑' n, (reference : Measure X) (U n) ≤ ∑' n, singularThreshold n :=
        ENNReal.tsum_le_tsum fun n => (hrefU n).le
      _ = 1 := singularThreshold_tsum
  have hmuSum : (∑' n, (mu : Measure X) (U n)ᶜ) ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      ∑' n, (mu : Measure X) (U n)ᶜ ≤ ∑' n, singularThreshold n :=
        ENNReal.tsum_le_tsum fun n => (hmuU n).le
      _ = 1 := singularThreshold_tsum
  let A : Set X := limsup U atTop
  let B : Set X := limsup (fun n => (U n)ᶜ) atTop
  have hrefA : (reference : Measure X) A = 0 :=
    measure_limsup_atTop_eq_zero hrefSum
  have hmuB : (mu : Measure X) B = 0 :=
    measure_limsup_atTop_eq_zero hmuSum
  apply Measure.MutuallySingular.mk hmuB hrefA
  intro x hx
  by_cases hfreq : ∃ᶠ n in atTop, x ∈ U n
  · exact Or.inr ((mem_limsup_iff_frequently_mem).2 hfreq)
  · apply Or.inl
    apply (mem_limsup_iff_frequently_mem).2
    exact (not_frequently.mp hfreq).frequently

theorem mem_singularProbabilityLaws_iff_mem_iInter_singularApproximation
    (reference mu : ProbabilityMeasure X)
    [Measure.OuterRegular (reference : Measure X)] :
    mu ∈ singularProbabilityLaws reference ↔
      mu ∈ ⋂ n, singularApproximation reference n := by
  constructor
  · intro h
    exact mem_iInter.2 fun n =>
      mutuallySingular_mem_singularApproximation reference mu h n
  · intro h
    exact mutuallySingular_of_mem_all_singularApproximation
      reference mu (mem_iInter.1 h)

/-- Singularity to an outer-regular reference is a `G_delta` condition in the
weak topology. -/
theorem singularProbabilityLaws_isGdelta
    [OpensMeasurableSpace X]
    (reference : ProbabilityMeasure X)
    [Measure.OuterRegular (reference : Measure X)] :
    IsGδ (singularProbabilityLaws reference) := by
  rw [show singularProbabilityLaws reference =
      ⋂ n, singularApproximation reference n by
    ext mu
    exact mem_singularProbabilityLaws_iff_mem_iInter_singularApproximation
      reference mu]
  exact IsGδ.iInter_of_isOpen fun n => singularApproximation_isOpen reference n

/-- A separable metric space admits arbitrarily fine measurable quantizers
with countable range. -/
theorem exists_countableRange_measurable_close
    [OpensMeasurableSpace X] [SeparableSpace X] [Nonempty X]
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ q : X → X, Measurable q ∧ (Set.range q).Countable ∧
      ∀ x, dist (q x) x ≤ epsilon := by
  classical
  obtain ⟨As, hmeas, hbdd, hdiam, hcover, hpair⟩ :=
    SeparableSpace.exists_measurable_partition_diam_le X hepsilon
  let index : X → ℕ := fun x => Nat.find (show ∃ n, x ∈ As n by
    simp only [← mem_iUnion, hcover, mem_univ])
  have hindex (x : X) : x ∈ As (index x) := by
    exact Nat.find_spec (show ∃ n, x ∈ As n by
      simp only [← mem_iUnion, hcover, mem_univ])
  let representative : ℕ → X := fun n =>
    if hn : (As n).Nonempty then hn.choose else Classical.choice inferInstance
  have hrepresentative (x : X) : representative (index x) ∈ As (index x) := by
    simp only [representative]
    rw [dif_pos (Set.nonempty_of_mem (hindex x))]
    exact Classical.choose_spec (Set.nonempty_of_mem (hindex x))
  have hindex_eq {x : X} {n : ℕ} (hxn : x ∈ As n) : index x = n := by
    by_contra hne
    have hd := hpair hne
    exact Set.disjoint_left.1 hd (hindex x) hxn
  let q : X → X := fun x => representative (index x)
  refine ⟨q, ?_, ?_, ?_⟩
  · intro T hT
    have hpreimage : q ⁻¹' T = ⋃ n, if representative n ∈ T then As n else ∅ := by
      ext x
      constructor
      · intro hx
        have hrep : representative (index x) ∈ T := hx
        apply mem_iUnion.2
        refine ⟨index x, ?_⟩
        rw [if_pos hrep]
        exact hindex x
      · intro hx
        obtain ⟨n, hxn⟩ := mem_iUnion.1 hx
        by_cases hn : representative n ∈ T
        · rw [if_pos hn] at hxn
          change representative (index x) ∈ T
          rw [hindex_eq hxn]
          exact hn
        · rw [if_neg hn] at hxn
          exact hxn.elim
    rw [hpreimage]
    apply MeasurableSet.iUnion
    intro n
    by_cases hn : representative n ∈ T
    · rw [if_pos hn]
      exact hmeas n
    · rw [if_neg hn]
      exact MeasurableSet.empty
  · apply (Set.countable_range representative).mono
    rintro y ⟨x, rfl⟩
    exact ⟨index x, rfl⟩
  · intro x
    exact (dist_le_diam_of_mem (hbdd (index x))
      (hrepresentative x) (hindex x)).trans (hdiam (index x))

theorem map_mutuallySingular_of_countable_range
    [BorelSpace X]
    (reference mu : ProbabilityMeasure X)
    (q : X → X) (hq : Measurable q) (hrange : (Set.range q).Countable)
    [NullSingletonClass (reference : Measure X)] :
    ((mu.map hq.aemeasurable : ProbabilityMeasure X) : Measure X) ⟂ₘ
      (reference : Measure X) := by
  let R : Set X := Set.range q
  have hRmeas : MeasurableSet R := hrange.measurableSet
  have hrefR : (reference : Measure X) R = 0 := hrange.measure_zero _
  refine ⟨Rᶜ, hRmeas.compl, ?_, ?_⟩
  · rw [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_apply hq hRmeas.compl]
    have hpre : q ⁻¹' Rᶜ = ∅ := by
      ext x
      simp [R]
    rw [hpre, measure_empty]
  · simpa only [compl_compl] using hrefR

/-- Uniform pointwise displacement bounds the Levy--Prokhorov distance between
a law and its measurable pushforward. -/
theorem levyProkhorovEDist_map_le_of_forall_dist_le
    [OpensMeasurableSpace X]
    (mu : ProbabilityMeasure X) (q : X → X) (hq : Measurable q)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hclose : ∀ x, dist (q x) x ≤ delta) :
    levyProkhorovEDist
      ((mu.map hq.aemeasurable : ProbabilityMeasure X) : Measure X)
      (mu : Measure X) ≤ ENNReal.ofReal delta := by
  apply levyProkhorovEDist_le_of_forall _ _ _
  intro epsilon B hepsilon hepsilon_top hB
  have hdelta_epsilon : delta < epsilon.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal hdelta hepsilon_top.ne).mp hepsilon
  rw [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply hq hB]
  constructor
  · apply (measure_mono (μ := (mu : Measure X)) ?_).trans
      (le_add_right le_rfl)
    intro x hx
    apply mem_thickening_iff.2
    exact ⟨q x, hx, (dist_comm x (q x)).le.trans_lt
      ((hclose x).trans_lt hdelta_epsilon)⟩
  · rw [Measure.map_apply hq isOpen_thickening.measurableSet]
    apply (measure_mono (μ := (mu : Measure X)) ?_).trans
      (le_add_right le_rfl)
    intro x hx
    apply mem_preimage.2
    apply mem_thickening_iff.2
    exact ⟨x, hx, (hclose x).trans_lt hdelta_epsilon⟩

theorem exists_mutuallySingular_levyProkhorovEDist_le
    [OpensMeasurableSpace X] [SeparableSpace X] [Nonempty X] [BorelSpace X]
    (reference mu : ProbabilityMeasure X)
    [NullSingletonClass (reference : Measure X)]
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ nu : ProbabilityMeasure X,
      (nu : Measure X) ⟂ₘ (reference : Measure X) ∧
      levyProkhorovEDist (nu : Measure X) (mu : Measure X) ≤
        ENNReal.ofReal epsilon := by
  obtain ⟨q, hq, hqrange, hqclose⟩ :=
    exists_countableRange_measurable_close (X := X) hepsilon
  refine ⟨mu.map hq.aemeasurable, ?_, ?_⟩
  · exact map_mutuallySingular_of_countable_range reference mu q hq hqrange
  · exact levyProkhorovEDist_map_le_of_forall_dist_le
      mu q hq hepsilon.le hqclose

/-- Radii used for a convergent sequence of countable-range quantizations. -/
def probabilityQuantizationRadius (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

theorem probabilityQuantizationRadius_pos (n : ℕ) :
    0 < probabilityQuantizationRadius n := by
  simp only [probabilityQuantizationRadius]
  positivity

theorem probabilityQuantizationRadius_tendsto_zero :
    Tendsto probabilityQuantizationRadius atTop (𝓝 0) := by
  simpa only [probabilityQuantizationRadius] using!
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))

/-- Probability laws singular to an atomless Borel reference are dense in the
weak topology. -/
theorem singularProbabilityLaws_dense
    [OpensMeasurableSpace X] [SeparableSpace X] [Nonempty X] [BorelSpace X]
    (reference : ProbabilityMeasure X)
    [NullSingletonClass (reference : Measure X)] :
    Dense (singularProbabilityLaws reference) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro mu
  choose nu hnuSing hnuDist using fun n =>
    exists_mutuallySingular_levyProkhorovEDist_le reference mu
      (probabilityQuantizationRadius_pos n)
  apply mem_closure_of_tendsto (f := nu) (b := atTop)
  · apply (LevyProkhorov.probabilityMeasureHomeomorph
      (Ω := X)).isEmbedding.tendsto_nhds_iff.mpr
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun n => dist_nonneg)
      (Eventually.of_forall fun n => ?_)
      probabilityQuantizationRadius_tendsto_zero
    rw [LevyProkhorov.dist_probabilityMeasure_def, levyProkhorovDist]
    calc
      (levyProkhorovEDist (nu n : Measure X) (mu : Measure X)).toReal ≤
          (ENNReal.ofReal (probabilityQuantizationRadius n)).toReal := by
        apply (ENNReal.toReal_le_toReal
          (levyProkhorovEDist_ne_top _ _)
          ENNReal.ofReal_ne_top).2
        exact hnuDist n
      _ = probabilityQuantizationRadius n :=
        ENNReal.toReal_ofReal (probabilityQuantizationRadius_pos n).le
  · exact Eventually.of_forall hnuSing

end


end GaloisForLFunctions.HTGeometry
