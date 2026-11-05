import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.ArchimedeanTailsHaveBoundedOffDiagonalAction

/-!
Cutoff archimedean differences define a continuous mixed form on the completed
arithmetic graph. For positive-level tests, this form is bounded above by the
full edge pairing: every omitted archimedean and prime-power product is nonnegative.
-/

open MeasureTheory Set Filter
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

open _root_.RHTower _root_.RHTower.CHMDDoobGraph _root_.RHTower.CHMDPolar

/-- Delete only short archimedean edges from the literal completed graph. -/
def archTailEdge (δ : ℝ) : SourceGraph →L[ℝ] Lp ℝ 2 archMeasure :=
  (lpSetCutoffCLM (F := ℝ) (𝕜 := ℝ) archMeasure 2
    {e : ℝ × ℝ | δ ≤ e.1} (measurableSet_le measurable_const measurable_fst)).comp
      (((WithLp.sndL 2 ℝ _ _).comp ArchGraph.subtypeL).comp
        graphArchEquiv.toContinuousLinearMap)

theorem archTailEdge_ae (δ : ℝ) (p : SourceGraph) :
    archTailEdge δ p =ᵐ[archMeasure]
      ({e : ℝ × ℝ | δ ≤ e.1}).indicator (difference p.val.fst) := by
  have he : (graphArchEquiv p).val.snd =ᵐ[archMeasure]
      difference (graphArchEquiv p).val.fst := (graphArchEquiv p).property
  rw [graphArchEquiv_source] at he
  filter_upwards [lpSetCutoffCLM_coeFn (F := ℝ) (𝕜 := ℝ) archMeasure 2
      {e : ℝ × ℝ | δ ≤ e.1} (measurableSet_le measurable_const measurable_fst)
        (graphArchEquiv p).val.snd, he] with e hc he
  change archTailEdge δ p e = _ at hc
  rw [hc]
  by_cases hδ : e ∈ {e : ℝ × ℝ | δ ≤ e.1}
  · simp only [indicator_of_mem hδ, he]
  · simp only [indicator_of_notMem hδ]

/-- Mixed energy of archimedean jumps whose length is at least the cutoff. -/
def archTailPair (δ : ℝ) (p q : SourceGraph) : ℝ :=
  inner ℝ (archTailEdge δ p) (archTailEdge δ q)

theorem continuous_archTailPair_left (δ : ℝ) (q : SourceGraph) :
    Continuous (fun p => archTailPair δ p q) :=
  (archTailEdge δ).continuous.inner continuous_const

theorem continuous_archTailPair_right (δ : ℝ) (p : SourceGraph) :
    Continuous (archTailPair δ p) :=
  continuous_const.inner (archTailEdge δ).continuous

theorem integrable_full_difference_mul (p q : SourceGraph) :
    Integrable (fun e => difference p.val.fst e * difference q.val.fst e) edgeMeasure := by
  refine (L2.integrable_inner p.val.snd q.val.snd).congr ?_
  filter_upwards [p.property, q.property] with e hp hq
  rw [hp, hq]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm, difference]

theorem full_edge_pair_eq_integral (p q : SourceGraph) :
    inner ℝ p.val.snd q.val.snd =
      ∫ e, difference p.val.fst e * difference q.val.fst e ∂edgeMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [p.property, q.property] with e hp hq
  rw [hp, hq]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm, difference]

theorem archTailPair_eq_integral (δ : ℝ) (p q : SourceGraph) :
    archTailPair δ p q =
      ∫ e in {e : ℝ × ℝ | δ ≤ e.1},
        difference p.val.fst e * difference q.val.fst e ∂archMeasure := by
  rw [archTailPair, L2.inner_def, ← integral_indicator
    (measurableSet_le measurable_const measurable_fst)]
  apply integral_congr_ae
  filter_upwards [archTailEdge_ae δ p, archTailEdge_ae δ q] with e hp hq
  rw [hp, hq]
  by_cases hδ : e ∈ {e : ℝ × ℝ | δ ≤ e.1}
  · simp only [indicator_of_mem hδ, RCLike.inner_apply, conj_trivial, mul_comm]
  · simp only [indicator_of_notMem hδ, inner_zero_left]

/-- Removing short archimedean edges keeps a lower bound on a positive-level test. -/
theorem archTailPair_positiveLevel_le (δ : ℝ) (p : SourceGraph) (t : ℝ) :
    archTailPair δ p (positiveLevelGraph p t) ≤
      inner ℝ p.val.snd (positiveLevelGraph p t).val.snd := by
  let q := positiveLevelGraph p t
  let f := fun e => difference p.val.fst e * difference q.val.fst e
  have hi : Integrable f edgeMeasure := integrable_full_difference_mul p q
  have hn : ∀ᵐ e ∂edgeMeasure, 0 ≤ f e := by
    filter_upwards [positiveLevelGraph_edge_nonneg_ae p t, p.property, q.property]
      with e he hp hq
    change 0 ≤ difference p.val.fst e * difference q.val.fst e
    rwa [hp, hq] at he
  have hi' : Integrable f (archMeasure + Measure.sum primeMeasure) := hi
  have hn' : ∀ᵐ e ∂(archMeasure + Measure.sum primeMeasure), 0 ≤ f e := hn
  rw [ae_add_measure_iff] at hn'
  rw [archTailPair_eq_integral, full_edge_pair_eq_integral]
  change (∫ e in {e : ℝ × ℝ | δ ≤ e.1}, f e ∂archMeasure) ≤ ∫ e, f e ∂edgeMeasure
  calc
    _ ≤ ∫ e, f e ∂archMeasure := setIntegral_le_integral hi'.left_of_add_measure hn'.1
    _ ≤ ∫ e, f e ∂edgeMeasure := by
      rw [edgeMeasure, integral_add_measure hi'.left_of_add_measure hi'.right_of_add_measure]
      exact le_add_of_nonneg_right (integral_nonneg_of_ae hn'.2)

#print axioms archTailPair_positiveLevel_le

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
