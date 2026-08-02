import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Box dimension from covering numbers

The Minkowski (box) dimension of a set is the limit of `log N_ε / log (1/ε)`, where `N_ε` is the
covering number at resolution `ε`.  Mathlib has covering numbers and Hausdorff dimension but not
box dimension, so the definition and its two basic tools are given here:

* a set whose covering numbers are trapped between two constant multiples of `ε^{-k}` has box
  dimension `k`;
* a Lipschitz image needs no more balls than the source at the rescaled resolution;
* a measure whose balls are small forces many balls (the mass distribution principle).
-/

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [PseudoMetricSpace X]

/-- The covering number as a real number; it is `0` on sets which admit no finite cover. -/
def coveringCard (ε : ℝ≥0) (A : Set X) : ℝ :=
  ((Metric.externalCoveringNumber ε A).toENNReal).toReal

theorem coveringCard_nonneg (ε : ℝ≥0) (A : Set X) : 0 ≤ coveringCard ε A := ENNReal.toReal_nonneg

/-- A set has box dimension `k` when the normalized logarithmic covering profile converges to
`k`. -/
def HasBoxDim (A : Set X) (k : ℝ) : Prop :=
  Tendsto (fun ε : ℝ => Real.log (coveringCard ε.toNNReal A) / Real.log (1 / ε)) (𝓝[>] 0) (𝓝 k)

/-- **Lipschitz images need no more balls.**  If `f` is `L`-Lipschitz then an `ε/L`-cover of the
source maps to an `ε`-cover of the image. -/
theorem externalCoveringNumber_image_le {Y : Type*} [PseudoMetricSpace Y] {f : X → Y} {L : ℝ≥0}
    (hf : LipschitzWith L f) (A : Set X) (δ : ℝ≥0) :
    Metric.externalCoveringNumber (L * δ) (f '' A) ≤ Metric.externalCoveringNumber δ A := by
  refine le_iInf₂ fun C hC => ?_
  have hcover : Metric.IsCover (L * δ) (f '' A) (f '' C) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hxc⟩ := hC hx
    refine ⟨f c, ⟨c, hc, rfl⟩, ?_⟩
    calc edist (f x) (f c) ≤ (L : ℝ≥0∞) * edist x c := hf.edist_le_mul x c
      _ ≤ (L : ℝ≥0∞) * (δ : ℝ≥0∞) := mul_le_mul' le_rfl hxc
      _ = ((L * δ : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_mul]
  exact le_trans (iInf₂_le_of_le (f '' C) hcover le_rfl) (Set.encard_image_le f C)

/-- **Mass distribution principle.**  If every closed `ε`-ball has measure at most `m`, then any
`ε`-cover of `A` has at least `μ A / m` elements. -/
theorem le_encard_of_isCover_of_measure_le [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) {A C : Set X} {ε : ℝ≥0} {m : ℝ≥0∞} (hC : Metric.IsCover ε A C)
    (hballs : ∀ x : X, μ (Metric.closedBall x ε) ≤ m) (hCfin : C.Finite) :
    μ A ≤ C.encard * m := by
  classical
  have hsub : A ⊆ ⋃ c ∈ hCfin.toFinset, Metric.closedBall c ε := by
    have hraw := (Metric.isCover_iff_subset_iUnion_closedBall).mp hC
    simpa using hraw
  have hcard : ((C.encard : ℕ∞) : ℝ≥0∞) = (hCfin.toFinset.card : ℝ≥0∞) := by
    rw [hCfin.encard_eq_coe_toFinset_card]
    simp
  calc μ A ≤ μ (⋃ c ∈ hCfin.toFinset, Metric.closedBall c ε) := measure_mono hsub
    _ ≤ ∑ c ∈ hCfin.toFinset, μ (Metric.closedBall c ε) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _c ∈ hCfin.toFinset, m := Finset.sum_le_sum fun c _ => hballs c
    _ = (hCfin.toFinset.card : ℝ≥0∞) * m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = C.encard * m := by rw [hcard]

theorem tendsto_log_one_div_atTop :
    Tendsto (fun ε : ℝ => Real.log (1 / ε)) (𝓝[>] (0 : ℝ)) atTop := by
  have h1 : Tendsto (fun ε : ℝ => 1 / ε) (𝓝[>] (0 : ℝ)) atTop := by
    simpa [one_div] using (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
  exact Real.tendsto_log_atTop.comp h1

/-- **Two-sided covering bounds pin the box dimension.**  A set whose covering numbers are trapped
between constant multiples of `ε^{-k}` has box dimension `k`. -/
theorem hasBoxDim_of_covering_bounds {A : Set X} {k : ℕ} {c₁ c₂ ε₀ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hε₀ : 0 < ε₀)
    (hlow : ∀ ε : ℝ, 0 < ε → ε < ε₀ → c₁ * (1 / ε) ^ k ≤ coveringCard ε.toNNReal A)
    (hupp : ∀ ε : ℝ, 0 < ε → ε < ε₀ → coveringCard ε.toNNReal A ≤ c₂ * (1 / ε) ^ k) :
    HasBoxDim A (k : ℝ) := by
  have hlog := tendsto_log_one_div_atTop
  have hzero₁ : Tendsto (fun ε : ℝ => Real.log c₁ / Real.log (1 / ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hlog
  have hzero₂ : Tendsto (fun ε : ℝ => Real.log c₂ / Real.log (1 / ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hlog
  have hlow' : Tendsto (fun ε : ℝ => Real.log c₁ / Real.log (1 / ε) + (k : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (k : ℝ)) := by
    simpa using hzero₁.add (tendsto_const_nhds (x := (k : ℝ)))
  have hupp' : Tendsto (fun ε : ℝ => Real.log c₂ / Real.log (1 / ε) + (k : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (k : ℝ)) := by
    simpa using hzero₂.add (tendsto_const_nhds (x := (k : ℝ)))
  have hmem : Set.Ioo (0 : ℝ) (min ε₀ 1) ∈ 𝓝[>] (0 : ℝ) := by
    refine Ioo_mem_nhdsGT ?_
    exact lt_min hε₀ one_pos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow' hupp' ?_ ?_
  · filter_upwards [hmem] with ε hε
    have hε0 : 0 < ε := hε.1
    have hεε₀ : ε < ε₀ := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hε1 : ε < 1 := lt_of_lt_of_le hε.2 (min_le_right _ _)
    have hL : 0 < Real.log (1 / ε) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hε0]
      linarith
    have hpow : (0 : ℝ) < (1 / ε) ^ k := by positivity
    have hNpos : 0 < c₁ * (1 / ε) ^ k := by positivity
    have hlogN : Real.log c₁ + (k : ℝ) * Real.log (1 / ε)
        ≤ Real.log (coveringCard ε.toNNReal A) := by
      have hmono := Real.log_le_log hNpos (hlow ε hε0 hεε₀)
      calc Real.log c₁ + (k : ℝ) * Real.log (1 / ε)
          = Real.log (c₁ * (1 / ε) ^ k) := by
            rw [Real.log_mul (ne_of_gt hc₁) (ne_of_gt hpow), Real.log_pow]
        _ ≤ Real.log (coveringCard ε.toNNReal A) := hmono
    rw [div_add' _ _ _ (ne_of_gt hL), div_le_div_iff_of_pos_right hL]
    linarith [hlogN]
  · filter_upwards [hmem] with ε hε
    have hε0 : 0 < ε := hε.1
    have hεε₀ : ε < ε₀ := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hε1 : ε < 1 := lt_of_lt_of_le hε.2 (min_le_right _ _)
    have hL : 0 < Real.log (1 / ε) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hε0]
      linarith
    have hpow : (0 : ℝ) < (1 / ε) ^ k := by positivity
    have hNpos : 0 < c₁ * (1 / ε) ^ k := by positivity
    have hCpos : 0 < coveringCard ε.toNNReal A := lt_of_lt_of_le hNpos (hlow ε hε0 hεε₀)
    have hlogN : Real.log (coveringCard ε.toNNReal A)
        ≤ Real.log c₂ + (k : ℝ) * Real.log (1 / ε) := by
      have hmono := Real.log_le_log hCpos (hupp ε hε0 hεε₀)
      calc Real.log (coveringCard ε.toNNReal A) ≤ Real.log (c₂ * (1 / ε) ^ k) := hmono
        _ = Real.log c₂ + (k : ℝ) * Real.log (1 / ε) := by
            rw [Real.log_mul (ne_of_gt hc₂) (ne_of_gt hpow), Real.log_pow]
    rw [div_add' _ _ _ (ne_of_gt hL), div_le_div_iff_of_pos_right hL]
    linarith [hlogN]

end

end GaloisForLFunctions.HTGeometry
