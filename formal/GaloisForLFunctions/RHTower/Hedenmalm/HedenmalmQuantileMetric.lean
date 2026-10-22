import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmQuantileNormalForm
import GaloisForLFunctions.HTGeometry.BoundedMultiplierHilbert

/-!
# The canonical singular source metric

In the quantile coordinate the reciprocal quantile speed

`1/q(t) = k(Q t) / M`

is the canonical source metric.  For a bounded source density it is a bounded, positive, injective
multiplication operator with dense range, but it has no positive lower bound as soon as the density
decays: the metric degenerates at the two endpoints of the interval.  Its associated quadratic form
pulls the weighted source inner product back to ordinary Lebesgue `L²`, rescaled by the total mass.

The bounded pointwise multipliers used by the local-metric rigidity theorem are exactly the
multiplication operators of bounded measurable symbols, so a metric whose composite coefficient
`w q` is bounded is covered by that theorem.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmQuantile

variable (S : PositiveDensitySource)

/-- The canonical source metric symbol `1/q(t) = k(Q t)/M`. -/
def metricSymbol (t : ℝ) : ℂ := ((S.k (S.quantileFun t) / S.mass : ℝ) : ℂ)

theorem metricSymbol_eq_inv_quantileSpeed (t : ℝ) :
    metricSymbol S t = (((quantileSpeed S t)⁻¹ : ℝ) : ℂ) := by
  rw [metricSymbol, inv_quantileSpeed]

theorem measurable_metricSymbol : Measurable (metricSymbol S) :=
  Complex.measurable_ofReal.comp
    (((S.continuous_k.measurable).comp S.measurable_quantileFun).div_const _)

theorem metricSymbol_pos (t : ℝ) : 0 < S.k (S.quantileFun t) / S.mass :=
  div_pos (S.pos_k _) S.mass_pos

theorem metricSymbol_ne_zero (t : ℝ) : metricSymbol S t ≠ 0 := by
  rw [metricSymbol]
  exact_mod_cast (metricSymbol_pos S t).ne'

theorem starRingEnd_metricSymbol (t : ℝ) :
    (starRingEnd ℂ) (metricSymbol S t) = metricSymbol S t := by
  rw [metricSymbol, Complex.conj_ofReal]

theorem norm_metricSymbol (t : ℝ) : ‖metricSymbol S t‖ = S.k (S.quantileFun t) / S.mass := by
  rw [metricSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (metricSymbol_pos S t).le]

theorem norm_metricSymbol_le {C : ℝ} (hC : ∀ x, S.k x ≤ C) (t : ℝ) :
    ‖metricSymbol S t‖ ≤ C / S.mass := by
  rw [norm_metricSymbol]
  exact div_le_div_of_nonneg_right (hC _) S.mass_pos.le

/-- The canonical singular source metric `G = M_{1/q}` on `L²(0,1)`. -/
def metricOperator {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖metricSymbol S t‖ ≤ C) :
    Lp ℂ 2 unitIntervalMeasure →L[ℂ] Lp ℂ 2 unitIntervalMeasure :=
  lpBoundedMulCLM (p := 2) (μ := unitIntervalMeasure) (measurable_metricSymbol S) hC0 hC

theorem metricOperator_coeFn {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖metricSymbol S t‖ ≤ C)
    (f : Lp ℂ 2 unitIntervalMeasure) :
    (metricOperator S hC0 hC f : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
      fun t => metricSymbol S t * f t :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := unitIntervalMeasure) (measurable_metricSymbol S) hC0 hC f

theorem norm_metricOperator_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖metricSymbol S t‖ ≤ C) :
    ‖metricOperator S hC0 hC‖ ≤ C :=
  norm_lpBoundedMulCLM_le (p := 2) (μ := unitIntervalMeasure) (measurable_metricSymbol S) hC0 hC

/-- The canonical metric is injective: its symbol vanishes nowhere. -/
theorem metricOperator_injective {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖metricSymbol S t‖ ≤ C) :
    Function.Injective (metricOperator S hC0 hC) :=
  lpBoundedMulCLM_injective_general (p := 2) (μ := unitIntervalMeasure)
    (measurable_metricSymbol S) hC0 hC (metricSymbol_ne_zero S)

/-- The canonical metric is self-adjoint: its symbol is real. -/
theorem metricOperator_inner {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖metricSymbol S t‖ ≤ C)
    (f g : Lp ℂ 2 unitIntervalMeasure) :
    (inner ℂ (metricOperator S hC0 hC f) g : ℂ) = inner ℂ f (metricOperator S hC0 hC g) :=
  lpBoundedMulCLM_inner_general (μ := unitIntervalMeasure) (measurable_metricSymbol S) hC0 hC
    (starRingEnd_metricSymbol S) f g

/-- The canonical metric has dense range. -/
theorem metricOperator_denseRange {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖metricSymbol S t‖ ≤ C) :
    DenseRange (metricOperator S hC0 hC) :=
  denseRange_lpBoundedMulCLM (μ := unitIntervalMeasure) (measurable_metricSymbol S) hC0 hC
    (starRingEnd_metricSymbol S) (metricSymbol_ne_zero S)

/-- The canonical metric is a bounded pointwise multiplier in the sense used by the
local-metric rigidity theorem. -/
theorem isPinnedPointwiseMultiplier_lpBoundedMulCLM {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ t, ‖φ t‖ ≤ C) :
    IsPinnedPointwiseMultiplier
      (lpBoundedMulCLM (p := 2) (μ := unitIntervalMeasure) hφ hC0 hC) := by
  intro f
  have hone := lpBoundedMulCLM_coeFn (p := 2) (μ := unitIntervalMeasure) hφ hC0 hC pinnedOne
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := unitIntervalMeasure) hφ hC0 hC f,
    hone, pinnedOne_coeFn] with t h1 h2 h3
  rw [h1, h2, h3, mul_one]

theorem isPinnedPointwiseMultiplier_metricOperator {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t, ‖metricSymbol S t‖ ≤ C) :
    IsPinnedPointwiseMultiplier (metricOperator S hC0 hC) :=
  isPinnedPointwiseMultiplier_lpBoundedMulCLM (measurable_metricSymbol S) hC0 hC

/-- **Bounded-composite local-metric rigidity, in multiplier form.**  A bounded measurable
symbol whose multiplication operator symmetrizes the pinned primitive vanishes almost everywhere. -/
theorem eq_zero_of_anticommutator {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t, ‖φ t‖ ≤ C)
    (hanti : pinnedVolterraAdjointCLM.comp
        (lpBoundedMulCLM (p := 2) (μ := unitIntervalMeasure) hφ hC0 hC)
      + (lpBoundedMulCLM (p := 2) (μ := unitIntervalMeasure) hφ hC0 hC).comp
        pinnedVolterraCLM = 0) :
    φ =ᵐ[unitIntervalMeasure] 0 := by
  have hzero := pointwiseMultiplier_anticommutator_eq_zero_imp_eq_zero _
    (isPinnedPointwiseMultiplier_lpBoundedMulCLM hφ hC0 hC) hanti
  have happ : lpBoundedMulCLM (p := 2) (μ := unitIntervalMeasure) hφ hC0 hC pinnedOne = 0 := by
    rw [hzero]
    rfl
  have hae : ((lpBoundedMulCLM (p := 2) (μ := unitIntervalMeasure) hφ hC0 hC pinnedOne :
      Lp ℂ 2 unitIntervalMeasure) : ℝ → ℂ) =ᵐ[unitIntervalMeasure] 0 :=
    Lp.eq_zero_iff_ae_eq_zero.mp happ
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := unitIntervalMeasure) hφ hC0 hC pinnedOne,
    hae, pinnedOne_coeFn] with t h1 h2 h3
  rw [h1, h3, mul_one] at h2
  exact h2

/-! ### The metric pullback -/

theorem conj_mul_self (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq z

/-- **(4a)**  The canonical metric pulls the source inner product back to ordinary Lebesgue `L²`,
rescaled by the total mass. -/
theorem inner_metricOperator_quantileUnitary {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t, ‖metricSymbol S t‖ ≤ C) (f : (SourceSpace S)) :
    (inner ℂ (metricOperator S hC0 hC (quantileUnitary S f)) (quantileUnitary S f) : ℂ)
      = (((∫ x, ‖(f x : ℂ)‖ ^ 2) / S.mass : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def]
  have hpoint : (fun t => (inner ℂ
      ((metricOperator S hC0 hC (quantileUnitary S f) : Lp ℂ 2 unitIntervalMeasure) t)
      ((quantileUnitary S f : Lp ℂ 2 unitIntervalMeasure) t) : ℂ))
      =ᵐ[unitIntervalMeasure]
      fun t => ((((quantileSpeed S t)⁻¹ *
        ‖quantileTransform S (fun x => f x) t‖ ^ 2 : ℝ)) : ℂ) := by
    filter_upwards [metricOperator_coeFn S hC0 hC (quantileUnitary S f),
      quantileUnitary_ae S f] with t h1 h2
    rw [RCLike.inner_apply', h1, h2, map_mul, starRingEnd_metricSymbol,
      metricSymbol_eq_inv_quantileSpeed, mul_assoc, conj_mul_self]
    push_cast
    rfl
  rw [integral_congr_ae hpoint, integral_complex_ofReal, unitIntervalMeasure_eq,
    quantileMetric_pullback S f]

/-! ### The metric degenerates at the endpoints -/

/-- A decaying source density makes the metric symbol take arbitrarily small values. -/
theorem exists_norm_metricSymbol_lt (hdecay : Tendsto S.k atBot (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ Ioo (0 : ℝ) 1, ‖metricSymbol S t‖ < ε := by
  obtain ⟨x, hx⟩ := (hdecay.eventually (eventually_lt_nhds (mul_pos hε S.mass_pos))).exists
  refine ⟨S.cdfFun x, S.cdfFun_mem_Ioo x, ?_⟩
  rw [norm_metricSymbol, S.quantile_cdfFun x, div_lt_iff₀ S.mass_pos]
  exact hx

/-- A subinterval on which the metric symbol is uniformly small. -/
theorem exists_interval_norm_metricSymbol_lt (hdecay : Tendsto S.k atBot (𝓝 0)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ a b : ℝ, a < b ∧ b ≤ 1 ∧ 0 ≤ a ∧
      ∀ t ∈ Ioo a b, ‖metricSymbol S t‖ < ε := by
  obtain ⟨x, hx⟩ := (hdecay.eventually (eventually_lt_nhds (mul_pos hε S.mass_pos))).exists
  have hopen : IsOpen {y : ℝ | S.k y < ε * S.mass} :=
    isOpen_lt S.continuous_k continuous_const
  obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.mp hopen x hx
  refine ⟨S.cdfFun (x - r / 2), S.cdfFun (x + r / 2), S.strictMono_cdfFun (by linarith),
    (S.cdfFun_mem_Ioo _).2.le, (S.cdfFun_mem_Ioo _).1.le, ?_⟩
  intro t ht
  have ht0 : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_trans (S.cdfFun_mem_Ioo _).1 ht.1, lt_trans ht.2 (S.cdfFun_mem_Ioo _).2⟩
  have h1 : x - r / 2 < S.quantileFun t := by
    have := S.strictMonoOn_quantileFun (S.cdfFun_mem_Ioo (x - r / 2)) ht0 ht.1
    rwa [S.quantile_cdfFun] at this
  have h2 : S.quantileFun t < x + r / 2 := by
    have := S.strictMonoOn_quantileFun ht0 (S.cdfFun_mem_Ioo (x + r / 2)) ht.2
    rwa [S.quantile_cdfFun] at this
  have hmem : S.quantileFun t ∈ Metric.ball x r := by
    rw [Real.ball_eq_Ioo]
    constructor <;> [linarith; linarith]
  have hlt : S.k (S.quantileFun t) < ε * S.mass := hball hmem
  rw [norm_metricSymbol, div_lt_iff₀ S.mass_pos]
  exact hlt

/-- **The canonical metric has no positive lower bound.**  It is a singular positive metric, not an
equivalent Hilbert norm. -/
theorem not_boundedBelow_metricOperator (hdecay : Tendsto S.k atBot (𝓝 0))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖metricSymbol S t‖ ≤ C) :
    ¬ ∃ ε : ℝ, 0 < ε ∧
      ∀ f : Lp ℂ 2 unitIntervalMeasure, ε * ‖f‖ ≤ ‖metricOperator S hC0 hC f‖ := by
  rintro ⟨ε, hε, hbound⟩
  obtain ⟨a, b, hab, hb1, ha0, hsmall⟩ :=
    exists_interval_norm_metricSymbol_lt S hdecay (half_pos hε)
  set A : Set ℝ := Ioo a b with hA
  have hAmeas : MeasurableSet A := measurableSet_Ioo
  have hAsub : A ⊆ Icc (0 : ℝ) 1 := fun t ht => ⟨le_of_lt (lt_of_le_of_lt ha0 ht.1),
    le_of_lt (lt_of_lt_of_le ht.2 hb1)⟩
  have hAvol : unitIntervalMeasure A = ENNReal.ofReal (b - a) := by
    rw [unitIntervalMeasure, Measure.restrict_apply hAmeas, Set.inter_eq_self_of_subset_left hAsub,
      Real.volume_Ioo]
  have hAne : unitIntervalMeasure A ≠ ⊤ := by
    rw [hAvol]
    exact ENNReal.ofReal_ne_top
  set f : Lp ℂ 2 unitIntervalMeasure := indicatorConstLp 2 hAmeas hAne (1 : ℂ) with hf
  have hfnorm : ‖f‖ = (unitIntervalMeasure.real A) ^ (1 / (2 : ℝ)) := by
    rw [hf, norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp
  have hAreal : 0 < unitIntervalMeasure.real A := by
    rw [Measure.real, hAvol, ENNReal.toReal_ofReal (by linarith)]
    linarith
  have hfpos : 0 < ‖f‖ := by
    rw [hfnorm]
    positivity
  set ψ : ℝ → ℂ := A.indicator (metricSymbol S) with hψdef
  have hψmeas : Measurable ψ := (measurable_metricSymbol S).indicator hAmeas
  have hψbound : ∀ t, ‖ψ t‖ ≤ ε / 2 := by
    intro t
    by_cases ht : t ∈ A
    · rw [hψdef, Set.indicator_of_mem ht]
      exact (hsmall t ht).le
    · rw [hψdef, Set.indicator_of_notMem ht, norm_zero]
      positivity
  have hεhalf : (0 : ℝ) ≤ ε / 2 := by positivity
  have hcoe : (metricOperator S hC0 hC f : ℝ → ℂ)
      =ᵐ[unitIntervalMeasure]
      ((lpBoundedMulCLM (p := 2) (μ := unitIntervalMeasure) hψmeas hεhalf hψbound f :
        Lp ℂ 2 unitIntervalMeasure) : ℝ → ℂ) := by
    filter_upwards [metricOperator_coeFn S hC0 hC f,
      lpBoundedMulCLM_coeFn (p := 2) (μ := unitIntervalMeasure) hψmeas hεhalf hψbound f,
      indicatorConstLp_coeFn (p := 2) (μ := unitIntervalMeasure) (s := A) (hs := hAmeas)
        (hμs := hAne) (c := (1 : ℂ))] with t h1 h2 h3
    rw [h1, h2]
    by_cases ht : t ∈ A
    · rw [hψdef, Set.indicator_of_mem ht]
    · rw [hψdef, Set.indicator_of_notMem ht, zero_mul,
        show (f : ℝ → ℂ) t = 0 by rw [h3, Set.indicator_of_notMem ht], mul_zero]
  have hnormeq : ‖metricOperator S hC0 hC f‖
      = ‖lpBoundedMulCLM (p := 2) (μ := unitIntervalMeasure) hψmeas hεhalf hψbound f‖ := by
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hcoe]
  have hle : ‖metricOperator S hC0 hC f‖ ≤ (ε / 2) * ‖f‖ := by
    rw [hnormeq]
    refine le_trans (ContinuousLinearMap.le_opNorm _ f) ?_
    exact mul_le_mul_of_nonneg_right
      (norm_lpBoundedMulCLM_le (p := 2) (μ := unitIntervalMeasure) hψmeas hεhalf hψbound)
      (norm_nonneg f)
  have hcontra := hbound f
  nlinarith [hfpos, hle, hcontra]

end HedenmalmQuantile

end

end RHTower
