import GaloisForLFunctions.HTGeometry.QuantileCoupling
import GaloisForLFunctions.HTGeometry.WeightedDensityL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The probability-integral transform of a continuous positive density

A continuous, everywhere positive, integrable density `k` on the line has total mass `M > 0` and
normalized law `dν = M⁻¹ k dx`.  Its distribution function

`p x = M⁻¹ ∫_{-∞}^x k`

is a `C¹` strictly increasing bijection of `ℝ` onto `(0,1)` with derivative `k/M`, and the
generalized inverse `Q = quantile ν` is its genuine two-sided inverse.  Consequently `p` transports
`ν` to the uniform law on `(0,1)` and `Q` transports the uniform law back.

This is the probability-integral transform in the form needed to put a source-derived operator into
its intrinsic quantile coordinate.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A continuous, everywhere positive, integrable density on the line. -/
structure PositiveDensitySource where
  k : ℝ → ℝ
  continuous_k : Continuous k
  pos_k : ∀ x, 0 < k x
  integrable_k : Integrable k

namespace PositiveDensitySource

variable (S : PositiveDensitySource)

/-- Total mass of the source. -/
def mass : ℝ := ∫ x, S.k x

theorem mass_pos : 0 < S.mass := by
  rw [mass, integral_pos_iff_support_of_nonneg (fun x => (S.pos_k x).le) S.integrable_k]
  have hsupp : Function.support S.k = univ := by
    ext x
    simp [Function.mem_support, (S.pos_k x).ne']
  rw [hsupp]
  simp

theorem mass_ne_zero : S.mass ≠ 0 := S.mass_pos.ne'

/-- The normalized probability density of the source. -/
def normalized (x : ℝ) : ℝ := S.k x / S.mass

theorem normalized_pos (x : ℝ) : 0 < S.normalized x := div_pos (S.pos_k x) S.mass_pos

theorem measurable_normalized : Measurable S.normalized :=
  (S.continuous_k.measurable).div_const _

theorem integrable_normalized : Integrable S.normalized :=
  S.integrable_k.div_const _

theorem integral_normalized : ∫ x, S.normalized x = 1 := by
  show ∫ x, S.k x / S.mass = 1
  rw [MeasureTheory.integral_div, ← mass]
  exact div_self S.mass_ne_zero

/-- The source law `dν = M⁻¹ k dx`. -/
def law : Measure ℝ := volume.withDensity (realDensity S.normalized)

instance instIsProbabilityMeasureLaw : IsProbabilityMeasure S.law := by
  constructor
  rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  show ∫⁻ x, ENNReal.ofReal (S.normalized x) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal S.integrable_normalized
    (Filter.Eventually.of_forall fun x => (S.normalized_pos x).le)]
  rw [S.integral_normalized, ENNReal.ofReal_one]

theorem law_ae_eq {β : Type*} {f g : ℝ → β} :
    f =ᵐ[S.law] g ↔ f =ᵐ[volume] g :=
  withDensity_realDensity_ae_eq S.measurable_normalized S.normalized_pos

/-- Integration against the source law is integration against the normalized density. -/
theorem integral_law {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ x, g x ∂S.law = ∫ x, S.normalized x • g x := by
  rw [law, integral_withDensity_eq_integral_toReal_smul
    (measurable_realDensity S.measurable_normalized)
    (Filter.Eventually.of_forall fun x => by simp [realDensity])]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (realDensity S.normalized x).toReal • g x = S.normalized x • g x
  rw [show realDensity S.normalized x = ENNReal.ofReal (S.normalized x) from rfl,
    ENNReal.toReal_ofReal (S.normalized_pos x).le]

/-- Integration against the source law over a set. -/
theorem setIntegral_law {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E)
    {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂S.law = ∫ x in s, S.normalized x • g x := by
  rw [law, restrict_withDensity hs, integral_withDensity_eq_integral_toReal_smul
    (measurable_realDensity S.measurable_normalized)
    (Filter.Eventually.of_forall fun x => by simp [realDensity])]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (realDensity S.normalized x).toReal • g x = S.normalized x • g x
  rw [show realDensity S.normalized x = ENNReal.ofReal (S.normalized x) from rfl,
    ENNReal.toReal_ofReal (S.normalized_pos x).le]

/-! ### The distribution function -/

/-- The distribution function `p x = M⁻¹ ∫_{-∞}^x k` of the source. -/
def cdfFun (x : ℝ) : ℝ := (∫ y in Iic x, S.k y) / S.mass

theorem integral_Iic_eq (x : ℝ) :
    ∫ y in Iic x, S.k y = (∫ y in Iic (0 : ℝ), S.k y) + ∫ y in (0 : ℝ)..x, S.k y := by
  rcases le_total (0 : ℝ) x with hx | hx
  · rw [intervalIntegral.integral_of_le hx, ← MeasureTheory.setIntegral_union
      (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
      (S.integrable_k.integrableOn) (S.integrable_k.integrableOn),
      Iic_union_Ioc_eq_Iic hx]
  · rw [intervalIntegral.integral_of_ge hx]
    have hsplit : ∫ y in Iic (0 : ℝ), S.k y
        = (∫ y in Iic x, S.k y) + ∫ y in Ioc x (0 : ℝ), S.k y := by
      rw [← MeasureTheory.setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
        (S.integrable_k.integrableOn) (S.integrable_k.integrableOn),
        Iic_union_Ioc_eq_Iic hx]
    rw [hsplit]
    ring

theorem hasDerivAt_integral_Iic (x : ℝ) :
    HasDerivAt (fun y => ∫ z in Iic y, S.k z) (S.k x) x := by
  have h : HasDerivAt (fun y => ∫ z in (0 : ℝ)..y, S.k z) (S.k x) x :=
    (S.continuous_k.integral_hasStrictDerivAt 0 x).hasDerivAt
  have h' := h.const_add (∫ z in Iic (0 : ℝ), S.k z)
  refine h'.congr_of_eventuallyEq ?_
  filter_upwards with y
  exact S.integral_Iic_eq y

theorem hasDerivAt_cdfFun (x : ℝ) : HasDerivAt S.cdfFun (S.normalized x) x := by
  have h := (S.hasDerivAt_integral_Iic x).div_const S.mass
  show HasDerivAt (fun y => (∫ z in Iic y, S.k z) / S.mass) (S.k x / S.mass) x
  exact h

theorem continuous_cdfFun : Continuous S.cdfFun :=
  continuous_iff_continuousAt.mpr fun x => (S.hasDerivAt_cdfFun x).continuousAt

theorem strictMono_cdfFun : StrictMono S.cdfFun := by
  refine strictMono_of_deriv_pos fun x => ?_
  rw [(S.hasDerivAt_cdfFun x).deriv]
  exact S.normalized_pos x

/-! ### The distribution function is the mathlib `cdf` of the law -/

theorem law_Iic (x : ℝ) : S.law (Iic x) = ENNReal.ofReal (S.cdfFun x) := by
  rw [law, withDensity_apply _ measurableSet_Iic]
  show ∫⁻ y in Iic x, ENNReal.ofReal (S.normalized y) = _
  rw [← ofReal_integral_eq_lintegral_ofReal
    (S.integrable_normalized.integrableOn)
    ((Filter.Eventually.of_forall fun x => (S.normalized_pos x).le).filter_mono
      MeasureTheory.Measure.restrict_le_self.absolutelyContinuous.ae_le)]
  congr 1
  show ∫ y in Iic x, S.k y / S.mass = (∫ y in Iic x, S.k y) / S.mass
  rw [MeasureTheory.integral_div]

theorem cdf_law_apply (x : ℝ) : cdf S.law x = S.cdfFun x := by
  rw [cdf_eq_real, Measure.real, S.law_Iic]
  refine ENNReal.toReal_ofReal ?_
  rw [cdfFun]
  refine div_nonneg ?_ S.mass_pos.le
  exact MeasureTheory.setIntegral_nonneg measurableSet_Iic fun y _ => (S.pos_k y).le

theorem cdf_law_eq : (cdf S.law : ℝ → ℝ) = S.cdfFun := funext S.cdf_law_apply

theorem tendsto_cdfFun_atBot : Tendsto S.cdfFun atBot (𝓝 0) := by
  rw [← S.cdf_law_eq]
  exact tendsto_cdf_atBot S.law

theorem tendsto_cdfFun_atTop : Tendsto S.cdfFun atTop (𝓝 1) := by
  rw [← S.cdf_law_eq]
  exact tendsto_cdf_atTop S.law

theorem cdfFun_mem_Ioo (x : ℝ) : S.cdfFun x ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · obtain ⟨a, ha⟩ : ∃ a : ℝ, a < x := ⟨x - 1, by linarith⟩
    have h0 : S.cdfFun a ≥ 0 := by
      rw [cdfFun]
      exact div_nonneg (MeasureTheory.setIntegral_nonneg measurableSet_Iic
        fun y _ => (S.pos_k y).le) S.mass_pos.le
    exact lt_of_le_of_lt h0 (S.strictMono_cdfFun ha)
  · obtain ⟨b, hb⟩ : ∃ b : ℝ, x < b := ⟨x + 1, by linarith⟩
    have h1 : S.cdfFun b ≤ 1 := by
      rw [← S.cdf_law_apply]
      exact cdf_le_one S.law b
    exact lt_of_lt_of_le (S.strictMono_cdfFun hb) h1

theorem surjOn_cdfFun : Ioo (0 : ℝ) 1 ⊆ range S.cdfFun := by
  intro t ht
  obtain ⟨a, ha⟩ := ((S.tendsto_cdfFun_atBot).eventually
    (eventually_lt_nhds ht.1)).exists
  obtain ⟨b, hb⟩ := ((S.tendsto_cdfFun_atTop).eventually
    (eventually_gt_nhds ht.2)).exists
  exact intermediate_value_univ a b S.continuous_cdfFun ⟨ha.le, hb.le⟩

/-! ### The quantile is the two-sided inverse -/

/-- The quantile function of the source law. -/
def quantileFun : ℝ → ℝ := quantile S.law

theorem quantile_cdfFun (x : ℝ) : S.quantileFun (S.cdfFun x) = x := by
  have hx := S.cdfFun_mem_Ioo x
  refine le_antisymm ?_ ?_
  · exact (quantile_le_iff hx.1 hx.2).mpr (by rw [S.cdf_law_apply])
  · by_contra hcon
    push Not at hcon
    obtain ⟨y, hy1, hy2⟩ := exists_between hcon
    have hle : S.quantileFun (S.cdfFun x) ≤ y := hy1.le
    have := (quantile_le_iff hx.1 hx.2).mp hle
    rw [S.cdf_law_apply] at this
    exact absurd (S.strictMono_cdfFun hy2) (not_lt.mpr this)

theorem cdfFun_quantile {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    S.cdfFun (S.quantileFun t) = t := by
  obtain ⟨x, hx⟩ := S.surjOn_cdfFun ht
  rw [← hx, S.quantile_cdfFun]

theorem strictMonoOn_quantileFun : StrictMonoOn S.quantileFun (Ioo (0 : ℝ) 1) := by
  intro s hs t ht hst
  have hs' := S.cdfFun_quantile hs
  have ht' := S.cdfFun_quantile ht
  by_contra hcon
  push Not at hcon
  have := S.strictMono_cdfFun.monotone hcon
  rw [hs', ht'] at this
  exact absurd hst (not_lt.mpr this)

theorem measurable_quantileFun : Measurable S.quantileFun := measurable_quantile S.law

/-! ### The two transport laws -/

theorem map_quantileFun_eq :
    Measure.map S.quantileFun (volume.restrict (Ioo (0 : ℝ) 1)) = S.law :=
  map_quantile_eq S.law

theorem measurePreserving_quantileFun :
    MeasurePreserving S.quantileFun (volume.restrict (Ioo (0 : ℝ) 1)) S.law :=
  ⟨S.measurable_quantileFun, S.map_quantileFun_eq⟩

theorem measurePreserving_cdfFun :
    MeasurePreserving S.cdfFun S.law (volume.restrict (Ioo (0 : ℝ) 1)) := by
  refine ⟨S.continuous_cdfFun.measurable, ?_⟩
  rw [← S.map_quantileFun_eq, Measure.map_map S.continuous_cdfFun.measurable
    S.measurable_quantileFun]
  rw [show Measure.map (S.cdfFun ∘ S.quantileFun) (volume.restrict (Ioo (0 : ℝ) 1))
      = Measure.map id (volume.restrict (Ioo (0 : ℝ) 1)) from ?_, Measure.map_id]
  refine Measure.map_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact S.cdfFun_quantile ht

end PositiveDensitySource

end

end GaloisForLFunctions.HTGeometry
