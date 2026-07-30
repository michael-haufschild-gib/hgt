import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Metrizable.Basic

/-!
# Atomless probability laws as a `G_delta` constraint

This file identifies atomlessness as a countable intersection of open conditions
in the weak topology on probability measures over a compact metric space.  The
open conditions ask for a finite closed cover whose members all have uniformly
small mass.
-/

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal NNReal Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [MeasurableSpace X] [MetricSpace X]
  [OpensMeasurableSpace X]

/-- Probability laws assigning less than `a` mass to a fixed closed test set. -/
def closedMassBelow (K : Set X) (a : ℝ≥0∞) : Set (ProbabilityMeasure X) :=
  {mu | (mu : Measure X) K < a}

theorem closedMassBelow_isOpen (K : Set X) (hK : IsClosed K) (a : ℝ≥0∞) :
    IsOpen (closedMassBelow K a) := by
  rw [isOpen_iff_mem_nhds]
  intro mu hmu
  change (mu : Measure X) K < a at hmu
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    (μ := mu) (μs := fun nu : ProbabilityMeasure X => nu) (L := 𝓝 mu) tendsto_id hK
  have hlt : limsup (fun nu : ProbabilityMeasure X => (nu : Measure X) K) (𝓝 mu) < a :=
    hlim.trans_lt hmu
  exact eventually_lt_of_limsup_lt hlt

/-- Laws admitting a finite closed cover by sets of mass less than `a`. -/
def finiteClosedCoverMassBelow (a : ℝ≥0∞) : Set (ProbabilityMeasure X) :=
  {mu | ∃ S : Finset (Set X),
    (⋃ K ∈ S, K) = Set.univ ∧
    (∀ K ∈ S, IsClosed K) ∧
    ∀ K ∈ S, (mu : Measure X) K < a}

theorem finiteClosedCoverMassBelow_isOpen (a : ℝ≥0∞) :
    IsOpen (finiteClosedCoverMassBelow (X := X) a) := by
  rw [isOpen_iff_mem_nhds]
  rintro mu ⟨S, hcover, hclosed, hmass⟩
  have hnhds : (⋂ K ∈ S, closedMassBelow K a) ∈ 𝓝 mu := by
    rw [Filter.biInter_finset_mem]
    intro K hK
    exact (closedMassBelow_isOpen K (hclosed K hK) a).mem_nhds (hmass K hK)
  apply Filter.mem_of_superset hnhds
  intro nu hnu
  simp only [Set.mem_iInter] at hnu
  refine ⟨S, hcover, hclosed, ?_⟩
  intro K hK
  exact hnu K hK

/-- The weak-topological set of atomless probability laws. -/
def atomlessProbabilityLaws : Set (ProbabilityMeasure X) :=
  {mu | NullSingletonClass (mu : Measure X)}

/-- The reciprocal thresholds used in the countable atomlessness test. -/
def diffuseThreshold (n : ℕ) : ℝ≥0∞ :=
  ((n + 1 : ℕ) : ℝ≥0∞)⁻¹

theorem diffuseThreshold_pos (n : ℕ) : 0 < diffuseThreshold n := by
  simp [diffuseThreshold]

theorem diffuseThreshold_tendsto_zero :
    Tendsto diffuseThreshold atTop (𝓝 0) := by
  exact ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)

theorem atomless_exists_small_closedBall
    (mu : ProbabilityMeasure X) (hmu : NullSingletonClass (mu : Measure X))
    (x : X) {a : ℝ≥0∞} (ha : 0 < a) :
    ∃ r : ℝ, 0 < r ∧ (mu : Measure X) (closedBall x r) < a := by
  let s : ℕ → Set X := fun n => closedBall x (1 / ((n : ℝ) + 1))
  have hs : ∀ n, NullMeasurableSet (s n) (mu : Measure X) :=
    fun n => isClosed_closedBall.measurableSet.nullMeasurableSet
  have hanti : Antitone s := by
    intro n m hnm
    apply closedBall_subset_closedBall
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hinter : ⋂ n, s n = {x} := by
    ext y
    simp only [s, mem_iInter, mem_closedBall, mem_singleton_iff]
    constructor
    · intro hy
      have hle : dist y x ≤ 0 :=
        ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat (fun n => hy n)
      exact dist_eq_zero.mp (le_antisymm hle dist_nonneg)
    · rintro rfl n
      simp only [dist_self]
      positivity
  have hlim : Tendsto (fun n => (mu : Measure X) (s n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop hs hanti
      ⟨0, measure_ne_top (mu : Measure X) (s 0)⟩
    rwa [hinter, hmu.measure_singleton x] at h
  have hev : ∀ᶠ n in atTop, (mu : Measure X) (s n) < a :=
    hlim.eventually_lt_const ha
  obtain ⟨n, hn⟩ := eventually_atTop.1 hev
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_⟩
  exact hn n le_rfl

theorem atomless_mem_finiteClosedCoverMassBelow
    [CompactSpace X] (mu : ProbabilityMeasure X)
    (hmu : NullSingletonClass (mu : Measure X))
    {a : ℝ≥0∞} (ha : 0 < a) :
    mu ∈ finiteClosedCoverMassBelow (X := X) a := by
  choose r hrpos hrmass using fun x => atomless_exists_small_closedBall mu hmu x ha
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => ball x (r x)) (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.2 ⟨x, mem_ball_self (hrpos x)⟩)
  let S : Finset (Set X) := t.image fun x => closedBall x (r x)
  refine ⟨S, ?_, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · exact Set.subset_univ (⋃ K ∈ S, K)
    intro y hy
    obtain ⟨x, hx⟩ := mem_iUnion.1 (ht hy)
    obtain ⟨hxt, hyx⟩ := mem_iUnion.1 hx
    apply mem_iUnion.2
    refine ⟨closedBall x (r x), mem_iUnion.2 ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.2 ⟨x, hxt, rfl⟩
    · exact ball_subset_closedBall hyx
  · intro K hK
    obtain ⟨x, hxt, rfl⟩ := Finset.mem_image.1 hK
    exact isClosed_closedBall
  · intro K hK
    obtain ⟨x, hxt, rfl⟩ := Finset.mem_image.1 hK
    exact hrmass x

theorem mem_atomlessProbabilityLaws_iff_mem_iInter_finiteClosedCoverMassBelow
    [CompactSpace X] (mu : ProbabilityMeasure X) :
    mu ∈ atomlessProbabilityLaws (X := X) ↔
      mu ∈ ⋂ n, finiteClosedCoverMassBelow (X := X) (diffuseThreshold n) := by
  constructor
  · intro hmu
    exact mem_iInter.2 fun n => atomless_mem_finiteClosedCoverMassBelow mu hmu
      (diffuseThreshold_pos n)
  · intro hmu
    have hall : ∀ n, mu ∈ finiteClosedCoverMassBelow (X := X) (diffuseThreshold n) :=
      mem_iInter.1 hmu
    refine ⟨fun x => ?_⟩
    have hbound : ∀ n, (mu : Measure X) {x} ≤ diffuseThreshold n := by
      intro n
      obtain ⟨S, hcover, hclosed, hmass⟩ := hall n
      have hx : x ∈ ⋃ K ∈ S, K := by rw [hcover]; trivial
      simp only [mem_iUnion] at hx
      obtain ⟨K, hKS, hxK⟩ := hx
      exact (measure_mono (singleton_subset_iff.2 hxK)).trans (hmass K hKS).le
    apply le_antisymm
    · exact ge_of_tendsto' diffuseThreshold_tendsto_zero hbound
    · exact bot_le

/-- Atomlessness is a `G_delta` condition in the weak topology. -/
theorem atomlessProbabilityLaws_isGdelta
    [CompactSpace X] :
    IsGδ (atomlessProbabilityLaws (X := X)) := by
  rw [show atomlessProbabilityLaws (X := X) =
      ⋂ n, finiteClosedCoverMassBelow (X := X) (diffuseThreshold n) by
    ext mu
    exact mem_atomlessProbabilityLaws_iff_mem_iInter_finiteClosedCoverMassBelow mu]
  exact IsGδ.iInter_of_isOpen fun n => finiteClosedCoverMassBelow_isOpen (diffuseThreshold n)

/-- A sequence of probability laws concentrating eventually in every
neighbourhood of `x` converges weakly to the Dirac law at `x`. -/
theorem tendsto_diracProba_of_eventually_measure_nhds_eq_one
    {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    (mu : ι → ProbabilityMeasure X) (x : X)
    (hconcentrates : ∀ U ∈ 𝓝 x, ∀ᶠ i in L, (mu i : Measure X) U = 1) :
    Tendsto mu L (𝓝 (diracProba x)) := by
  apply tendsto_of_forall_isOpen_le_liminf'
  intro G hG
  rw [show (diracProba x : Measure X) G = G.indicator 1 x by
    exact Measure.dirac_apply' x hG.measurableSet]
  by_cases hx : x ∈ G
  · rw [Set.indicator_of_mem hx]
    apply le_liminf_of_le (hf := by isBoundedDefault)
    filter_upwards [hconcentrates G (hG.mem_nhds hx)] with i hi
    simp [hi]
  · rw [Set.indicator_of_notMem hx]
    exact bot_le

end

end GaloisForLFunctions.HTGeometry
