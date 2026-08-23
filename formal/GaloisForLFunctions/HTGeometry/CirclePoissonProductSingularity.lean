import GaloisForLFunctions.HTGeometry.CirclePoissonFiniteProduct
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ModulusDivergence
import GaloisForLFunctions.HTGeometry.ProductOccupancyDichotomy
import GaloisForLFunctions.HTGeometry.RobbinsMonroRecursion
import Mathlib.Probability.BorelCantelli

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

local instance : MeasurableSpace Circle :=
  instMeasurableSpaceCircle_galoisForLFunctions

/-- Product of circle Poisson laws over a natural-number index. -/
def natCirclePoissonProductMeasure (a : ℕ → CirclePoissonParameter) :
    Measure (ℕ → Circle) :=
  Measure.infinitePi fun n => circlePoissonMeasure (a n)

instance (a : ℕ → CirclePoissonParameter) :
    IsProbabilityMeasure (natCirclePoissonProductMeasure a) := by
  unfold natCirclePoissonProductMeasure
  infer_instance

/-- Hellinger affinity of the first `N` local pairs. -/
def circlePoissonPrefixAffinity
    (a b : ℕ → CirclePoissonParameter) (N : ℕ) : ℝ :=
  ∏ n ∈ Finset.range N, circlePoissonHellingerAffinity (a n) (b n)

theorem circlePoissonPrefixAffinity_nonneg
    (a b : ℕ → CirclePoissonParameter) (N : ℕ) :
    0 ≤ circlePoissonPrefixAffinity a b N :=
  Finset.prod_nonneg fun n _ => circlePoissonHellingerAffinity_nonneg (a n) (b n)

/-- Pullback of the finite likelihood-comparison event to the infinite circle product. -/
def circlePoissonPrefixDecisionEvent
    (a b : ℕ → CirclePoissonParameter) (N : ℕ) : Set (ℕ → Circle) :=
  (Finset.range N).restrict ⁻¹'
    finiteCirclePoissonDecisionEvent
      (fun n : ↑(Finset.range N) => a n) (fun n : ↑(Finset.range N) => b n)

theorem measurableSet_circlePoissonPrefixDecisionEvent
    (a b : ℕ → CirclePoissonParameter) (N : ℕ) :
    MeasurableSet (circlePoissonPrefixDecisionEvent a b N) := by
  exact (measurableSet_finiteCirclePoissonDecisionEvent
    (fun n : ↑(Finset.range N) => a n) (fun n : ↑(Finset.range N) => b n)).preimage
      (Finset.range N).measurable_restrict

private theorem prod_attach_circlePoissonHellingerAffinity
    (a b : ℕ → CirclePoissonParameter) (N : ℕ) :
    (∏ n : ↑(Finset.range N), circlePoissonHellingerAffinity (a n) (b n)) =
      circlePoissonPrefixAffinity a b N := by
  exact Finset.prod_attach (Finset.range N)
    (fun n => circlePoissonHellingerAffinity (a n) (b n))

theorem natCirclePoissonProductMeasure_prefixDecision_le_affinity
    (a b : ℕ → CirclePoissonParameter) (N : ℕ) :
    natCirclePoissonProductMeasure b (circlePoissonPrefixDecisionEvent a b N) ≤
      ENNReal.ofReal (circlePoissonPrefixAffinity a b N) := by
  let I := Finset.range N
  let E : Set (↑I → Circle) := finiteCirclePoissonDecisionEvent
    (fun n : ↑I => a n) (fun n : ↑I => b n)
  have hE : MeasurableSet E := measurableSet_finiteCirclePoissonDecisionEvent _ _
  have hmap : Measure.map I.restrict (natCirclePoissonProductMeasure b) =
      Measure.pi fun n : ↑I => circlePoissonMeasure (b n) := by
    exact Measure.infinitePi_map_restrict (fun n => circlePoissonMeasure (b n))
  calc
    natCirclePoissonProductMeasure b (circlePoissonPrefixDecisionEvent a b N) =
        Measure.map I.restrict (natCirclePoissonProductMeasure b) E := by
      rw [Measure.map_apply I.measurable_restrict hE]
      rfl
    _ = (Measure.pi fun n : ↑I => circlePoissonMeasure (b n)) E := by rw [hmap]
    _ ≤ ENNReal.ofReal
        (∏ n : ↑I, circlePoissonHellingerAffinity (a n) (b n)) := by
      exact measure_pi_circlePoissonMeasure_decision_le_overlap _ _
    _ = ENNReal.ofReal (circlePoissonPrefixAffinity a b N) := by
      rw [prod_attach_circlePoissonHellingerAffinity]

theorem natCirclePoissonProductMeasure_prefixDecision_compl_le_affinity
    (a b : ℕ → CirclePoissonParameter) (N : ℕ) :
    natCirclePoissonProductMeasure a (circlePoissonPrefixDecisionEvent a b N)ᶜ ≤
      ENNReal.ofReal (circlePoissonPrefixAffinity a b N) := by
  let I := Finset.range N
  let E : Set (↑I → Circle) := finiteCirclePoissonDecisionEvent
    (fun n : ↑I => a n) (fun n : ↑I => b n)
  have hE : MeasurableSet E := measurableSet_finiteCirclePoissonDecisionEvent _ _
  have hmap : Measure.map I.restrict (natCirclePoissonProductMeasure a) =
      Measure.pi fun n : ↑I => circlePoissonMeasure (a n) := by
    exact Measure.infinitePi_map_restrict (fun n => circlePoissonMeasure (a n))
  calc
    natCirclePoissonProductMeasure a (circlePoissonPrefixDecisionEvent a b N)ᶜ =
        Measure.map I.restrict (natCirclePoissonProductMeasure a) Eᶜ := by
      rw [Measure.map_apply I.measurable_restrict hE.compl]
      rfl
    _ = (Measure.pi fun n : ↑I => circlePoissonMeasure (a n)) Eᶜ := by rw [hmap]
    _ ≤ ENNReal.ofReal
        (∏ n : ↑I, circlePoissonHellingerAffinity (a n) (b n)) := by
      exact measure_pi_circlePoissonMeasure_decision_compl_le_overlap _ _
    _ = ENNReal.ofReal (circlePoissonPrefixAffinity a b N) := by
      rw [prod_attach_circlePoissonHellingerAffinity]

private theorem tendsto_finset_range_atTop :
    Tendsto Finset.range atTop (atTop : Filter (Finset ℕ)) := by
  refine tendsto_atTop.2 fun s => ?_
  refine Filter.eventually_atTop.2 ⟨s.sup id + 1, fun N hN => ?_⟩
  intro n hn
  rw [Finset.mem_range]
  exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)) hN

/-- Divergence of the sum of local Hellinger defects forces finite-prefix affinity to vanish. -/
theorem tendsto_circlePoissonPrefixAffinity_zero_of_not_summable
    (a b : ℕ → CirclePoissonParameter)
    (hdiv : ¬ Summable (fun n =>
      1 - circlePoissonHellingerAffinity (a n) (b n))) :
    Tendsto (circlePoissonPrefixAffinity a b) atTop (𝓝 0) := by
  let d : ℕ → ℝ := fun n => 1 - circlePoissonHellingerAffinity (a n) (b n)
  have hd0 : ∀ n, 0 ≤ d n := fun n => by
    dsimp only [d]
    exact sub_nonneg.mpr (circlePoissonHellingerAffinity_le_one (a n) (b n))
  have hd1 : ∀ n, d n ≤ 1 := fun n => by
    dsimp only [d]
    linarith [circlePoissonHellingerAffinity_nonneg (a n) (b n)]
  have hsumFinset : Tendsto (fun s : Finset ℕ => ∑ n ∈ s, d n) atTop atTop :=
    tendsto_finsetSum_atTop_of_not_summable hd0 (by simpa [d] using hdiv)
  have hsum : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, d n) atTop atTop :=
    hsumFinset.comp tendsto_finset_range_atTop
  have hneg : Tendsto (fun N : ℕ => -(∑ n ∈ Finset.range N, d n)) atTop atBot := by
    rw [← tendsto_neg_atTop_iff]
    simpa using hsum
  have hexp : Tendsto (fun N : ℕ => Real.exp (-(∑ n ∈ Finset.range N, d n)))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hupper : ∀ N : ℕ, circlePoissonPrefixAffinity a b N ≤
      Real.exp (-(∑ n ∈ Finset.range N, d n)) := by
    intro N
    have h := prod_one_sub_le_exp_neg (κ := (1 : ℝ)) (lam := d) 0 N
      (fun n => by simpa using hd0 n) (fun n => by simpa using hd1 n)
    simpa [circlePoissonPrefixAffinity, d] using h
  exact squeeze_zero'
    (Eventually.of_forall fun N => circlePoissonPrefixAffinity_nonneg a b N)
    (Eventually.of_forall hupper) hexp

/-- Divergent local Hellinger defect makes the two natural-index circle products mutually
singular.  The separating set is built from a summably accurate subsequence of finite likelihood
tests and the first Borel--Cantelli lemma. -/
theorem natCirclePoissonProductMeasure_mutuallySingular_of_not_summable_hellingerDefect
    (a b : ℕ → CirclePoissonParameter)
    (hdiv : ¬ Summable (fun n =>
      1 - circlePoissonHellingerAffinity (a n) (b n))) :
    (natCirclePoissonProductMeasure a).MutuallySingular
      (natCirclePoissonProductMeasure b) := by
  classical
  have htend := tendsto_circlePoissonPrefixAffinity_zero_of_not_summable a b hdiv
  have hsmall : ∀ k : ℕ, ∃ N : ℕ,
      circlePoissonPrefixAffinity a b N ≤ (1 / 2 : ℝ) ^ k := by
    intro k
    have heps : 0 < (1 / 2 : ℝ) ^ k := pow_pos (by norm_num) _
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 htend) _ heps
    refine ⟨N, ?_⟩
    have hdist := hN N le_rfl
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (circlePoissonPrefixAffinity_nonneg a b N)] at hdist
    exact hdist.le
  let N : ℕ → ℕ := fun k => Classical.choose (hsmall k)
  have hN (k : ℕ) : circlePoissonPrefixAffinity a b (N k) ≤ (1 / 2 : ℝ) ^ k :=
    Classical.choose_spec (hsmall k)
  let E : ℕ → Set (ℕ → Circle) := fun k => circlePoissonPrefixDecisionEvent a b (N k)
  have hEmeas : ∀ k, MeasurableSet (E k) := fun k =>
    measurableSet_circlePoissonPrefixDecisionEvent a b (N k)
  have hprefixSummable : Summable (fun k => circlePoissonPrefixAffinity a b (N k)) := by
    exact Summable.of_nonneg_of_le
      (fun k => circlePoissonPrefixAffinity_nonneg a b (N k)) hN
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1))
  have hprefixENN :
      (∑' k, ENNReal.ofReal (circlePoissonPrefixAffinity a b (N k))) ≠ ∞ :=
    (tsum_ofReal_ne_top_iff_summable _
      (fun k => circlePoissonPrefixAffinity_nonneg a b (N k))).2 hprefixSummable
  have hsumB : (∑' k, natCirclePoissonProductMeasure b (E k)) ≠ ∞ := by
    apply ne_top_of_le_ne_top hprefixENN
    exact ENNReal.tsum_le_tsum fun k =>
      natCirclePoissonProductMeasure_prefixDecision_le_affinity a b (N k)
  have hsumA : (∑' k, natCirclePoissonProductMeasure a (E k)ᶜ) ≠ ∞ := by
    apply ne_top_of_le_ne_top hprefixENN
    exact ENNReal.tsum_le_tsum fun k =>
      natCirclePoissonProductMeasure_prefixDecision_compl_le_affinity a b (N k)
  have hlimsupB : natCirclePoissonProductMeasure b (Filter.limsup E atTop) = 0 :=
    measure_limsup_atTop_eq_zero hsumB
  have hlimsupA : natCirclePoissonProductMeasure a
      (Filter.limsup (fun k => (E k)ᶜ) atTop) = 0 :=
    measure_limsup_atTop_eq_zero hsumA
  have hliminfMeas : MeasurableSet (Filter.liminf E atTop) :=
    MeasurableSet.measurableSet_liminf hEmeas
  refine ⟨(Filter.liminf E atTop)ᶜ, hliminfMeas.compl, ?_, ?_⟩
  · rw [Filter.liminf_compl]
    simpa [Function.comp_def] using hlimsupA
  · rw [compl_compl]
    exact measure_mono_null Filter.liminf_le_limsup hlimsupB

theorem not_summable_circlePoissonHellingerDefect_of_not_summable_normSq
    (a b : ℕ → CirclePoissonParameter)
    (hdiv : ¬ Summable (fun n => ‖(a n : ℂ) - (b n : ℂ)‖ ^ 2)) :
    ¬ Summable (fun n => 1 - circlePoissonHellingerAffinity (a n) (b n)) := by
  intro hsum
  apply hdiv
  have hscaled : Summable (fun n =>
      8 * (1 - circlePoissonHellingerAffinity (a n) (b n))) :=
    hsum.mul_left 8
  exact Summable.of_nonneg_of_le (fun n => sq_nonneg _)
    (fun n => by
      have h := norm_sq_div_eight_le_one_sub_circlePoissonHellingerAffinity (a n) (b n)
      linarith)
    hscaled

/-- Divergent squared parameter displacement is the concrete singular side of the circle-Poisson
Kakutani classification. -/
theorem natCirclePoissonProductMeasure_mutuallySingular_of_not_summable_normSq
    (a b : ℕ → CirclePoissonParameter)
    (hdiv : ¬ Summable (fun n => ‖(a n : ℂ) - (b n : ℂ)‖ ^ 2)) :
    (natCirclePoissonProductMeasure a).MutuallySingular
      (natCirclePoissonProductMeasure b) :=
  natCirclePoissonProductMeasure_mutuallySingular_of_not_summable_hellingerDefect a b
    (not_summable_circlePoissonHellingerDefect_of_not_summable_normSq a b hdiv)

end

end GaloisForLFunctions.HTGeometry
