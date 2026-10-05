import GaloisForLFunctions.RHTower.ThetaQuantileOnePortPencil
import GaloisForLFunctions.RHTower.HedenmalmQuantileSliceMoment

/-!
# The flat physical-space normal form of the theta one-port

For `f ∈ L²(0,1)` put `u_f(x) = ρ(x) f(F(x))` with `ρ = k/M` and `F` the theta CDF.  The change
of variables `t = F(x)` gives

`‖f‖_T² = ∫ |u_f|²`, `∫₀¹ f = ∫ u_f`, `∫₀¹ h f = ∫ ρ u_f`, `β(f) = −i ∫₀¹ Q f = −i ∫ x u_f`,

and the whole pencil has the universal weak form `⟨g, A f⟩ = i∫ ū_g ∫_{−∞}^x u_f`,
`⟨g, T f⟩ = ∫ ū_g u_f`, `⟨g, b⟩ = ∫ ū_g ρ`.  The image of `H₀` is dense in `L²(ℝ)`; the output
port is the square-integrable vector `ρ`, the input port is the coordinate `x ∉ L²`, and the
explicit vectors `f_L = 1_{|Q| ≤ L} Q/h` show that `β` has no bounded extension to the metric
energy.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace RHTower

noncomputable section

open HedenmalmThetaSource HedenmalmQuantile HedenmalmHilbertSchmidt GaloisForLFunctions.HTGeometry

local notation "ThetaL2" => Lp ℂ 2 unitIntervalMeasure

/-! ## The change of variables `t = F(x)` -/

theorem integral_unitInterval_eq_cdf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : AEStronglyMeasurable g unitIntervalMeasure) :
    ∫ t, g t ∂unitIntervalMeasure = ∫ x, thetaSource.normalized x • g (thetaSource.cdfFun x) := by
  have hmap := thetaSource.measurePreserving_cdfFun.map_eq
  rw [unitIntervalMeasure_eq] at hg ⊢
  rw [← hmap] at hg ⊢
  rw [integral_map thetaSource.continuous_cdfFun.measurable.aemeasurable hg, thetaSource.integral_law]

theorem metricSymbol_cdfFun (x : ℝ) :
    ‖metricSymbol thetaSource (thetaSource.cdfFun x)‖ = thetaSource.normalized x := by
  rw [norm_metricSymbol, thetaSource.quantile_cdfFun]
  rfl

/-- The flat field `u_f(x) = ρ(x) f(F(x))`. -/
def flatField (f : ThetaL2) (x : ℝ) : ℂ := (thetaSource.normalized x : ℂ) * f (thetaSource.cdfFun x)

theorem continuous_normalized_theta : Continuous thetaSource.normalized :=
  thetaSource.continuous_k.div_const _

theorem stronglyMeasurable_flatField (f : ThetaL2) : StronglyMeasurable (flatField f) :=
  (Complex.continuous_ofReal.comp continuous_normalized_theta).stronglyMeasurable.mul
    ((Lp.stronglyMeasurable f).comp_measurable thetaSource.continuous_cdfFun.measurable)

theorem integrable_unitInterval_iff_cdf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : AEStronglyMeasurable g unitIntervalMeasure) :
    Integrable g unitIntervalMeasure ↔
      Integrable (fun x => thetaSource.normalized x • g (thetaSource.cdfFun x)) volume := by
  have hmap := thetaSource.measurePreserving_cdfFun.map_eq
  rw [unitIntervalMeasure_eq] at hg ⊢
  rw [← hmap] at hg ⊢
  rw [integrable_map_measure hg thetaSource.continuous_cdfFun.measurable.aemeasurable,
    ← thetaSource.integrable_law_iff]
  rfl

theorem flatField_eq_smul (f : ThetaL2) (x : ℝ) :
    flatField f x = thetaSource.normalized x • f (thetaSource.cdfFun x) := by
  rw [flatField, Complex.real_smul]

theorem norm_flatField (f : ThetaL2) (x : ℝ) :
    ‖flatField f x‖ = thetaSource.normalized x * ‖f (thetaSource.cdfFun x)‖ := by
  rw [flatField, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaSource.normalized_pos x)]

theorem aestronglyMeasurable_metric_mul_norm_sq (f : ThetaL2) :
    AEStronglyMeasurable (fun t => ‖metricSymbol thetaSource t‖ * ‖f t‖ ^ 2) unitIntervalMeasure :=
  (integrable_metric_mul_norm_sq f).1

/-- **Flat energy**: `‖f‖_T² = ∫ h|f|² = ∫ |u_f|²`. -/
theorem metricEnergy_eq_integral_flatField (f : ThetaL2) :
    metricEnergy f = ∫ x, ‖flatField f x‖ ^ 2 := by
  rw [metricEnergy, integral_unitInterval_eq_cdf (aestronglyMeasurable_metric_mul_norm_sq f)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [metricSymbol_cdfFun, norm_flatField]
  ring

theorem integrable_norm_sq_flatField (f : ThetaL2) : Integrable (fun x => ‖flatField f x‖ ^ 2) volume := by
  have h := (integrable_unitInterval_iff_cdf (aestronglyMeasurable_metric_mul_norm_sq f)).1
    (integrable_metric_mul_norm_sq f)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [metricSymbol_cdfFun, norm_flatField]
  ring

theorem memLp_flatField (f : ThetaL2) : MemLp (flatField f) 2 volume :=
  (memLp_two_iff_integrable_sq_norm (stronglyMeasurable_flatField f).aestronglyMeasurable).2
    (integrable_norm_sq_flatField f)

theorem integrable_coe_unitInterval (f : ThetaL2) : Integrable (fun t => f t) unitIntervalMeasure :=
  (Lp.memLp f).integrable one_le_two

theorem integrable_flatField (f : ThetaL2) : Integrable (flatField f) volume := by
  have h := (integrable_unitInterval_iff_cdf (integrable_coe_unitInterval f).1).1
    (integrable_coe_unitInterval f)
  exact h.congr (Eventually.of_forall fun x => (flatField_eq_smul f x).symm)

/-- **Flat mass**: `∫₀¹ f = ∫ u_f`. -/
theorem integral_flatField (f : ThetaL2) : ∫ x, flatField f x = ∫ t, f t ∂unitIntervalMeasure := by
  rw [integral_unitInterval_eq_cdf (integrable_coe_unitInterval f).1]
  exact integral_congr_ae (Eventually.of_forall fun x => flatField_eq_smul f x)

theorem coeFn_thetaMetricOperator (f : ThetaL2) :
    (thetaMetricOperator f : ℝ → ℂ) =ᵐ[unitIntervalMeasure] fun t => metricSymbol thetaSource t * f t :=
  metricOperator_coeFn thetaSource thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le f

theorem metricSymbol_eq_norm (t : ℝ) : metricSymbol thetaSource t = (‖metricSymbol thetaSource t‖ : ℂ) := by
  rw [norm_metricSymbol, metricSymbol]

/-- **Flat output port**: `⟨b, f⟩ = ∫₀¹ h f = ∫ ρ u_f` on `H₀`. -/
theorem inner_onePortOutputVector {f : ThetaL2} (hf : f ∈ meanZeroSpace) :
    ⟪onePortOutputVector, f⟫_ℂ = ∫ x, (thetaSource.normalized x : ℂ) * flatField f x := by
  rw [onePortOutputVector, inner_meanZeroProj_left, meanZeroProj_eq_self hf, inner_lp_eq]
  have hae : (fun t => (starRingEnd ℂ) ((thetaMetricOperator constMode : ThetaL2) t) * f t)
      =ᵐ[unitIntervalMeasure] fun t => (‖metricSymbol thetaSource t‖ : ℂ) * f t := by
    filter_upwards [coeFn_thetaMetricOperator constMode, coeFn_unitFourierBasis 0] with t h1 h2
    rw [h1, show (constMode : ThetaL2) = unitFourierBasis 0 from rfl, h2, fourierMode_zero, mul_one,
      starRingEnd_metricSymbol, ← metricSymbol_eq_norm]
  rw [integral_congr_ae hae]
  have hm : AEStronglyMeasurable (fun t => (‖metricSymbol thetaSource t‖ : ℂ) * f t) unitIntervalMeasure :=
    (Complex.continuous_ofReal.measurable.comp (measurable_metricSymbol thetaSource).norm).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)
  rw [integral_unitInterval_eq_cdf hm]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [metricSymbol_cdfFun, flatField, Complex.real_smul]

/-! ## The input port is the physical-position moment -/

theorem quantileFun_half : thetaSource.quantileFun (1 / 2) = 0 := by
  have h := quantileFun_one_sub (s := 1 / 2) ⟨by norm_num, by norm_num⟩
  norm_num at h
  linarith

theorem measurable_quantileSpeed_theta : Measurable (quantileSpeed thetaSource) :=
  measurable_const.div (thetaSource.continuous_k.measurable.comp thetaSource.measurable_quantileFun)

theorem measurable_pinnedKernelSlice_uncurry :
    Measurable (fun p : ℝ × ℝ => pinnedKernelSlice p.2 p.1) := by
  have hset : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} := measurableSet_le measurable_fst measurable_snd
  exact (Measurable.ite hset measurable_const measurable_const).sub measurable_snd

/-- The pinned primitive as a kernel integral. -/
theorem pinnedVolterraFun_eq_integral (f : ThetaL2) (t : ℝ) :
    pinnedVolterraFun f t = ∫ s, (pinnedKernelSlice t s : ℂ) * f s ∂unitIntervalMeasure := by
  have hf := integrable_coe_unitInterval f
  have hind : Integrable (fun s => (Iic t).indicator (fun u => f u) s) unitIntervalMeasure :=
    hf.indicator measurableSet_Iic
  have hpt : (fun s => (pinnedKernelSlice t s : ℂ) * f s) =
      fun s => (Iic t).indicator (fun u => f u) s - (t : ℂ) * f s := by
    funext s
    by_cases hs : s ≤ t
    · rw [indicator_of_mem (show s ∈ Iic t from hs), pinnedKernelSlice, if_pos hs]; push_cast; ring
    · rw [indicator_of_notMem (show s ∉ Iic t from hs), pinnedKernelSlice, if_neg hs]; push_cast; ring
  rw [hpt, integral_sub hind (hf.const_mul _), integral_const_mul, pinnedVolterraFun, pinnedPrefix,
    pinnedMean]

theorem absSliceMoment_le_quantile {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    absSliceMoment thetaSource s ≤ absSliceMoment thetaSource (1 / 2) + |thetaSource.quantileFun s| := by
  have h := absSliceMoment_le thetaSource hasFiniteKernelEnergy_thetaSource hs
    (c := 1 / 2) ⟨by norm_num, by norm_num⟩
  rwa [quantileFun_half, sub_zero] at h

theorem integrable_quantileFun_mul (f : ThetaL2) :
    Integrable (fun s => ‖thetaSource.quantileFun s‖ * ‖f s‖) unitIntervalMeasure := by
  have hQ : Integrable (fun s => thetaSource.quantileFun s ^ (2 : ℕ)) unitIntervalMeasure := by
    rw [unitIntervalMeasure_eq]; exact integrableOn_sq_quantileFun_thetaSource
  have hf2 : Integrable (fun s => ‖f s‖ ^ 2) unitIntervalMeasure :=
    (Lp.memLp f).integrable_norm_pow (by norm_num)
  refine ((hQ.add hf2).div_const 2).mono' ?_ (Eventually.of_forall fun s => ?_)
  · exact (thetaSource.measurable_quantileFun.norm.aestronglyMeasurable).mul (Lp.aestronglyMeasurable f).norm
  · simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs]
    have := sq_nonneg (|thetaSource.quantileFun s| - ‖f s‖)
    have h2 : |thetaSource.quantileFun s| ^ 2 = thetaSource.quantileFun s ^ 2 := sq_abs _
    nlinarith

/-- **The physical-position port** `β(f) = −i ∫₀¹ Q f`. -/
theorem onePortInput_eq_quantile (f : ThetaL2) :
    onePortInput f = -Complex.I * ∫ s, (thetaSource.quantileFun s : ℂ) * f s ∂unitIntervalMeasure := by
  set F : ℝ × ℝ → ℂ := fun p => ((quantileSpeed thetaSource p.2 * pinnedKernelSlice p.2 p.1 : ℝ) : ℂ) * f p.1
  have hFm : AEStronglyMeasurable F (unitIntervalMeasure.prod unitIntervalMeasure) :=
    ((Complex.continuous_ofReal.measurable.comp ((measurable_quantileSpeed_theta.comp measurable_snd).mul
      measurable_pinnedKernelSlice_uncurry)).aestronglyMeasurable).mul
      ((Lp.stronglyMeasurable f).comp_measurable measurable_fst).aestronglyMeasurable
  have hnorm : ∀ s t, ‖F (s, t)‖ = quantileSpeed thetaSource t * |pinnedKernelSlice t s| * ‖f s‖ := by
    intro s t
    simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (quantileSpeed_pos thetaSource t)]
  have hFi : Integrable F (unitIntervalMeasure.prod unitIntervalMeasure) := by
    refine (integrable_prod_iff hFm).2 ⟨?_, ?_⟩
    · filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with s hs
      have h := (integrable_quantileSpeed_mul_pinnedKernelSlice thetaSource
        hasFiniteKernelEnergy_thetaSource hs)
      have hc : Integrable (fun t => ((quantileSpeed thetaSource t * pinnedKernelSlice t s : ℝ) : ℂ)) unitIntervalMeasure :=
        h.ofReal
      exact hc.mul_const (f s)
    · have hint : ∀ s ∈ Ioo (0 : ℝ) 1, ∫ t, ‖F (s, t)‖ ∂unitIntervalMeasure = ‖f s‖ * absSliceMoment thetaSource s := by
        intro s hs
        simp_rw [hnorm]
        rw [integral_mul_const, absSliceMoment, mul_comm]
      refine Integrable.mono' (((integrable_quantileFun_mul f).add
          ((integrable_coe_unitInterval f).norm.const_mul (absSliceMoment thetaSource (1 / 2))))) ?_ ?_
      · exact hFm.norm.integral_prod_right'
      · filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with s hs
        rw [hint s hs, Real.norm_eq_abs, abs_of_nonneg (by
          unfold absSliceMoment; exact mul_nonneg (norm_nonneg _) (integral_nonneg fun t => by
            have := quantileSpeed_pos thetaSource t; positivity))]
        have h := absSliceMoment_le_quantile hs
        have hfs := norm_nonneg (f s)
        simp only [Pi.add_apply, Real.norm_eq_abs] at *
        nlinarith [abs_nonneg (thetaSource.quantileFun s)]
  have hB : onePortInput f = ∫ t, Complex.I * (quantileSpeed thetaSource t : ℂ) * pinnedVolterraFun f t ∂unitIntervalMeasure := by
    rw [onePortInput_apply, inner_constMode_eq_pinnedMean, pinnedMean]
    exact integral_congr_ae (thetaKernelOperator_ae f)
  have h1 : (∫ t, Complex.I * (quantileSpeed thetaSource t : ℂ) * pinnedVolterraFun f t ∂unitIntervalMeasure) =
      Complex.I * ∫ t, ∫ s, F (s, t) ∂unitIntervalMeasure ∂unitIntervalMeasure := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [F]
    rw [pinnedVolterraFun_eq_integral, mul_assoc, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    push_cast; ring
  have h2 : (∫ t, ∫ s, F (s, t) ∂unitIntervalMeasure ∂unitIntervalMeasure) = ∫ s, ∫ t, F (s, t) ∂unitIntervalMeasure ∂unitIntervalMeasure := by
    rw [← integral_prod_symm F hFi, integral_prod F hFi]
  have h3 : (∫ s, ∫ t, F (s, t) ∂unitIntervalMeasure ∂unitIntervalMeasure) = ∫ s, -((thetaSource.quantileFun s : ℂ) * f s) ∂unitIntervalMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with s hs
    simp only [F]
    rw [integral_mul_const, integral_complex_ofReal]
    rw [show (∫ t, quantileSpeed thetaSource t * pinnedKernelSlice t s ∂unitIntervalMeasure) = sliceMoment thetaSource s from rfl,
      sliceMoment_eq_neg_quantileFun hs]
    push_cast; ring
  rw [hB, h1, h2, h3, integral_neg]
  ring

/-- **The flat input port** `β(f) = −i ∫ x u_f(x) dx`. -/
theorem onePortInput_eq_flat (f : ThetaL2) :
    onePortInput f = -Complex.I * ∫ x : ℝ, (x : ℂ) * flatField f x := by
  rw [onePortInput_eq_quantile]
  congr 1
  have hm : AEStronglyMeasurable (fun s => (thetaSource.quantileFun s : ℂ) * f s) unitIntervalMeasure :=
    (Complex.continuous_ofReal.measurable.comp thetaSource.measurable_quantileFun).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)
  rw [integral_unitInterval_eq_cdf hm]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [thetaSource.quantile_cdfFun, flatField, Complex.real_smul]
  ring

/-! ## The universal weak form of the pencil -/

theorem flatField_conj_mul (f g : ThetaL2) (x : ℝ) :
    thetaSource.normalized x • ((starRingEnd ℂ) (g (thetaSource.cdfFun x)) *
      ((‖metricSymbol thetaSource (thetaSource.cdfFun x)‖ : ℂ) * f (thetaSource.cdfFun x))) =
      (starRingEnd ℂ) (flatField g x) * flatField f x := by
  rw [metricSymbol_cdfFun, flatField, flatField, map_mul, Complex.conj_ofReal, Complex.real_smul]
  ring

/-- **Flat metric**: `⟨g, T f⟩ = ∫ ū_g u_f` on `H₀`. -/
theorem inner_onePortMetric_flat {f g : ThetaL2} (hf : f ∈ meanZeroSpace) (hg : g ∈ meanZeroSpace) :
    ⟪g, onePortMetric f⟫_ℂ = ∫ x, (starRingEnd ℂ) (flatField g x) * flatField f x := by
  rw [onePortMetric, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← inner_meanZeroProj_left, meanZeroProj_eq_self hg, meanZeroProj_eq_self hf, inner_lp_eq]
  have hae : (fun t => (starRingEnd ℂ) (g t) * (thetaMetricOperator f : ThetaL2) t)
      =ᵐ[unitIntervalMeasure] fun t => (starRingEnd ℂ) (g t) * ((‖metricSymbol thetaSource t‖ : ℂ) * f t) := by
    filter_upwards [coeFn_thetaMetricOperator f] with t h1
    rw [h1, ← metricSymbol_eq_norm]
  rw [integral_congr_ae hae]
  have hm : AEStronglyMeasurable
      (fun t => (starRingEnd ℂ) (g t) * ((‖metricSymbol thetaSource t‖ : ℂ) * f t)) unitIntervalMeasure :=
    (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable g)).mul
      ((Complex.continuous_ofReal.measurable.comp
        (measurable_metricSymbol thetaSource).norm).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  rw [integral_unitInterval_eq_cdf hm]
  exact integral_congr_ae (Eventually.of_forall fun x => flatField_conj_mul f g x)

/-- **Flat output pairing**: `⟨g, b⟫ = ∫ ū_g ρ` on `H₀`. -/
theorem inner_onePortOutputVector_right {g : ThetaL2} (hg : g ∈ meanZeroSpace) :
    ⟪g, onePortOutputVector⟫_ℂ = ∫ x, (starRingEnd ℂ) (flatField g x) * (thetaSource.normalized x : ℂ) := by
  rw [← inner_conj_symm, inner_onePortOutputVector hg, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [map_mul, Complex.conj_ofReal, mul_comm]

/-- The flat primitive `∫_{−∞}^x u_f`. -/
def flatPrimitive (f : ThetaL2) (x : ℝ) : ℂ := ∫ y in Iic x, flatField f y

/-- The pinned primitive at `F(x)` is the flat primitive. -/
theorem pinnedPrefix_cdfFun (f : ThetaL2) (x : ℝ) :
    pinnedPrefix f (thetaSource.cdfFun x) = flatPrimitive f x := by
  rw [pinnedPrefix, integral_unitInterval_eq_cdf ((Lp.aestronglyMeasurable f).indicator measurableSet_Iic),
    flatPrimitive, ← integral_indicator measurableSet_Iic]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  by_cases hy : y ≤ x
  · rw [indicator_of_mem (show thetaSource.cdfFun y ∈ Iic (thetaSource.cdfFun x) from
      thetaSource.strictMono_cdfFun.monotone hy), indicator_of_mem (show y ∈ Iic x from hy),
      flatField_eq_smul]
  · rw [indicator_of_notMem (show thetaSource.cdfFun y ∉ Iic (thetaSource.cdfFun x) from
      fun h => hy (thetaSource.strictMono_cdfFun.le_iff_le.1 h)), indicator_of_notMem
      (show y ∉ Iic x from hy), smul_zero]

/-- **Flat primitive pairing**: `⟨g, A f⟩ = i ∫ ū_g(x) ∫_{−∞}^x u_f` on `H₀`. -/
theorem inner_onePortPrimitive_flat {f g : ThetaL2} (hf : f ∈ meanZeroSpace) (hg : g ∈ meanZeroSpace) :
    ⟪g, onePortPrimitive f⟫_ℂ =
      Complex.I * ∫ x, (starRingEnd ℂ) (flatField g x) * flatPrimitive f x := by
  rw [onePortPrimitive, smul_apply, inner_smul_right, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, meanZeroProj_eq_self hf, ← inner_meanZeroProj_left,
    meanZeroProj_eq_self hg, inner_lp_eq]
  congr 1
  have hmean : pinnedMean f = 0 := by rw [← inner_constMode_eq_pinnedMean]; exact (mem_meanZeroSpace_iff f).1 hf
  have hae : (fun t => (starRingEnd ℂ) (g t) * (pinnedVolterraCLM f : ThetaL2) t)
      =ᵐ[unitIntervalMeasure] fun t => (starRingEnd ℂ) (g t) * pinnedPrefix f t := by
    filter_upwards [pinnedVolterra_coeFn f] with t h1
    change _ * (pinnedVolterra f) t = _
    rw [h1, pinnedVolterraFun, hmean, mul_zero, sub_zero]
  rw [integral_congr_ae hae]
  have hm : AEStronglyMeasurable (fun t => (starRingEnd ℂ) (g t) * pinnedPrefix f t) unitIntervalMeasure :=
    (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable g)).mul
      (aestronglyMeasurable_pinnedPrefix f)
  rw [integral_unitInterval_eq_cdf hm]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [pinnedPrefix_cdfFun, flatField, map_mul, Complex.conj_ofReal, Complex.real_smul]
  ring

/-! ## Flat test fields and their quantile pull-backs -/

/-- A bounded measurable field of compact support. -/
structure IsFlatTest (u : ℝ → ℂ) : Prop where
  measurable : Measurable u
  bounded : ∃ C, ∀ x, ‖u x‖ ≤ C
  compact : ∃ R, ∀ x, R < |x| → u x = 0

/-- The quantile pull-back `u(Q(t))/h(t)`. -/
def preFlatFun (u : ℝ → ℂ) (t : ℝ) : ℂ := u (thetaSource.quantileFun t) / metricSymbol thetaSource t

theorem metricSymbol_cdfFun_eq (x : ℝ) :
    metricSymbol thetaSource (thetaSource.cdfFun x) = (thetaSource.normalized x : ℂ) := by
  rw [metricSymbol, thetaSource.quantile_cdfFun]
  rfl

theorem preFlatFun_cdfFun (u : ℝ → ℂ) (x : ℝ) :
    preFlatFun u (thetaSource.cdfFun x) = u x / (thetaSource.normalized x : ℂ) := by
  rw [preFlatFun, thetaSource.quantile_cdfFun, metricSymbol_cdfFun_eq]

theorem exists_normalized_ge (R : ℝ) : ∃ c : ℝ, 0 < c ∧ ∀ x, |x| ≤ R → c ≤ thetaSource.normalized x := by
  rcases lt_or_ge R 0 with hR | hR
  · exact ⟨1, one_pos, fun x hx => absurd (abs_nonneg x) (by linarith)⟩
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_Icc (a := -R) (b := R)).exists_isMinOn
    ⟨0, by constructor <;> linarith⟩ continuous_normalized_theta.continuousOn
  refine ⟨thetaSource.normalized x₀, thetaSource.normalized_pos x₀, fun x hx => ?_⟩
  exact hmin (abs_le.1 hx)

theorem measurable_preFlatFun {u : ℝ → ℂ} (hu : Measurable u) : Measurable (preFlatFun u) :=
  (hu.comp thetaSource.measurable_quantileFun).div (measurable_metricSymbol thetaSource)

theorem memLp_preFlatFun {u : ℝ → ℂ} (hu : IsFlatTest u) : MemLp (preFlatFun u) 2 unitIntervalMeasure := by
  obtain ⟨C, hC⟩ := hu.bounded
  obtain ⟨R, hR⟩ := hu.compact
  obtain ⟨c, hc, hcR⟩ := exists_normalized_ge R
  have hm := (measurable_preFlatFun hu.measurable).aestronglyMeasurable (μ := unitIntervalMeasure)
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine (integrable_unitInterval_iff_cdf
    ((measurable_preFlatFun hu.measurable).norm.pow_const 2).aestronglyMeasurable).2 ?_
  have hint : Integrable ((Icc (-R) R).indicator fun _ : ℝ => C ^ 2 / c) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp) (by simp))
  refine hint.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (continuous_normalized_theta.measurable.mul
      ((((measurable_preFlatFun hu.measurable).comp thetaSource.continuous_cdfFun.measurable).norm.pow_const
        2))).aestronglyMeasurable
  · have hρ := thetaSource.normalized_pos x
    have hval : thetaSource.normalized x • ‖preFlatFun u (thetaSource.cdfFun x)‖ ^ 2 =
        ‖u x‖ ^ 2 / thetaSource.normalized x := by
      rw [preFlatFun_cdfFun, smul_eq_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
      field_simp
    show ‖thetaSource.normalized x • ‖preFlatFun u (thetaSource.cdfFun x)‖ ^ 2‖ ≤ _
    rw [hval, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hx : |x| ≤ R
    · rw [indicator_of_mem (show x ∈ Icc (-R) R from abs_le.1 hx)]
      have hcx := hcR x hx
      have hux := hC x
      have hu0 := norm_nonneg (u x)
      have hC0 : 0 ≤ C := hu0.trans hux
      calc ‖u x‖ ^ 2 / thetaSource.normalized x ≤ C ^ 2 / thetaSource.normalized x :=
            div_le_div_of_nonneg_right (pow_le_pow_left₀ hu0 hux 2) hρ.le
        _ ≤ C ^ 2 / c := div_le_div_of_nonneg_left (by positivity) hc hcx
    · rw [hR x (not_le.1 hx), indicator_of_notMem (show x ∉ Icc (-R) R from fun h => hx (abs_le.2 h))]
      simp

/-- The quantile pull-back of a flat test field as a vector of `L²(0,1)`. -/
def preFlat {u : ℝ → ℂ} (hu : IsFlatTest u) : ThetaL2 := (memLp_preFlatFun hu).toLp

theorem flatField_preFlat {u : ℝ → ℂ} (hu : IsFlatTest u) : flatField (preFlat hu) =ᵐ[volume] u := by
  have h1 : (fun t => (preFlat hu : ThetaL2) t) =ᵐ[unitIntervalMeasure] preFlatFun u :=
    MemLp.coeFn_toLp _
  have h1' : (fun t => (preFlat hu : ThetaL2) t) =ᵐ[Measure.map thetaSource.cdfFun thetaSource.law]
      preFlatFun u := by
    rw [thetaSource.measurePreserving_cdfFun.map_eq, ← unitIntervalMeasure_eq]
    exact h1
  have hq : Measure.QuasiMeasurePreserving thetaSource.cdfFun thetaSource.law
      (Measure.map thetaSource.cdfFun thetaSource.law) :=
    ⟨thetaSource.continuous_cdfFun.measurable, Measure.AbsolutelyContinuous.rfl⟩
  have h2 := Measure.QuasiMeasurePreserving.ae_eq_comp hq h1'
  have h3 := thetaSource.law_ae_eq.1 h2
  filter_upwards [h3] with x hx
  simp only [Function.comp_apply] at hx
  rw [flatField, hx, preFlatFun_cdfFun]
  have hρ : (thetaSource.normalized x : ℂ) ≠ 0 := by exact_mod_cast (thetaSource.normalized_pos x).ne'
  field_simp

theorem integral_preFlat {u : ℝ → ℂ} (hu : IsFlatTest u) :
    ∫ t, (preFlat hu : ThetaL2) t ∂unitIntervalMeasure = ∫ x, u x := by
  rw [← integral_flatField, integral_congr_ae (flatField_preFlat hu)]

theorem preFlat_mem_meanZeroSpace {u : ℝ → ℂ} (hu : IsFlatTest u) (h0 : ∫ x, u x = 0) :
    preFlat hu ∈ meanZeroSpace := by
  rw [mem_meanZeroSpace_iff, inner_constMode_eq_pinnedMean, pinnedMean, integral_preFlat, h0]

theorem metricEnergy_preFlat {u : ℝ → ℂ} (hu : IsFlatTest u) :
    metricEnergy (preFlat hu) = ∫ x, ‖u x‖ ^ 2 := by
  rw [metricEnergy_eq_integral_flatField]
  refine integral_congr_ae ?_
  filter_upwards [flatField_preFlat hu] with x hx
  rw [hx]

theorem onePortInput_preFlat {u : ℝ → ℂ} (hu : IsFlatTest u) :
    onePortInput (preFlat hu) = -Complex.I * ∫ x : ℝ, (x : ℂ) * u x := by
  rw [onePortInput_eq_flat]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [flatField_preFlat hu] with x hx
  rw [hx]

/-! ## The input port is unbounded in the metric energy -/

/-- The flat field `x 1_{|x| ≤ L}` of the explicit test vectors. -/
def portTestField (L : ℝ) (x : ℝ) : ℂ := if |x| ≤ L then (x : ℂ) else 0

theorem isFlatTest_portTestField (L : ℝ) : IsFlatTest (portTestField L) where
  measurable := Measurable.ite (measurableSet_le measurable_id.abs measurable_const)
    Complex.measurable_ofReal measurable_const
  bounded := ⟨|L|, fun x => by
    unfold portTestField
    split_ifs with h
    · rw [Complex.norm_real, Real.norm_eq_abs]; exact h.trans (le_abs_self L)
    · simp⟩
  compact := ⟨L, fun x hx => by unfold portTestField; rw [if_neg (not_le.2 hx)]⟩

/-- **The test vectors** `f_L = 1_{|Q| ≤ L} Q/h`. -/
def portTestVector (L : ℝ) : ThetaL2 := preFlat (isFlatTest_portTestField L)

theorem portTestVector_ae (L : ℝ) :
    (fun t => (portTestVector L : ThetaL2) t) =ᵐ[unitIntervalMeasure] fun t =>
      if |thetaSource.quantileFun t| ≤ L then
        (thetaSource.quantileFun t : ℂ) / metricSymbol thetaSource t else 0 := by
  filter_upwards [MemLp.coeFn_toLp (memLp_preFlatFun (isFlatTest_portTestField L))] with t ht
  rw [portTestVector, preFlat, ht, preFlatFun, portTestField]
  split_ifs <;> simp

theorem integral_portTestField_eq_indicator (L : ℝ) {g : ℝ → ℂ} (hg : ∀ x, g x = (x : ℂ)) :
    (fun x => g x * portTestField L x) = (Icc (-L) L).indicator fun x => ((x ^ 2 : ℝ) : ℂ) := by
  funext x
  unfold portTestField
  by_cases h : |x| ≤ L
  · rw [if_pos h, indicator_of_mem (show x ∈ Icc (-L) L from abs_le.1 h), hg]; push_cast; ring
  · rw [if_neg h, indicator_of_notMem (show x ∉ Icc (-L) L from fun h' => h (abs_le.2 h')), mul_zero]

theorem integral_portTestField (L : ℝ) : ∫ x, portTestField L x = 0 := by
  have h : portTestField L = (Icc (-L) L).indicator fun x => ((x : ℝ) : ℂ) := by
    funext x
    unfold portTestField
    by_cases h : |x| ≤ L
    · rw [if_pos h, indicator_of_mem (show x ∈ Icc (-L) L from abs_le.1 h)]
    · rw [if_neg h, indicator_of_notMem (show x ∉ Icc (-L) L from fun h' => h (abs_le.2 h'))]
  rw [h, integral_indicator measurableSet_Icc, integral_complex_ofReal]
  rcases le_or_gt (-L) L with hL | hL
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL, integral_id]
    simp
  · rw [Icc_eq_empty (not_le.2 hL), Measure.restrict_empty, integral_zero_measure]
    simp

theorem integral_sq_portTestField {L : ℝ} (hL : 0 ≤ L) :
    ∫ x : ℝ, (x : ℂ) * portTestField L x = ((2 * L ^ 3 / 3 : ℝ) : ℂ) := by
  rw [integral_portTestField_eq_indicator L (fun x => rfl), integral_indicator measurableSet_Icc,
    integral_complex_ofReal, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), integral_pow]
  congr 1
  ring

theorem integral_norm_sq_portTestField {L : ℝ} (hL : 0 ≤ L) :
    ∫ x, ‖portTestField L x‖ ^ 2 = 2 * L ^ 3 / 3 := by
  have h : (fun x => ‖portTestField L x‖ ^ 2) = (Icc (-L) L).indicator fun x => x ^ 2 := by
    funext x
    unfold portTestField
    by_cases h : |x| ≤ L
    · rw [if_pos h, indicator_of_mem (show x ∈ Icc (-L) L from abs_le.1 h), Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · rw [if_neg h, indicator_of_notMem (show x ∉ Icc (-L) L from fun h' => h (abs_le.2 h'))]; simp
  rw [h, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), integral_pow]
  ring

theorem portTestVector_mem (L : ℝ) : portTestVector L ∈ meanZeroSpace :=
  preFlat_mem_meanZeroSpace _ (integral_portTestField L)

/-- `‖f_L‖_T² = 2L³/3`. -/
theorem metricEnergy_portTestVector {L : ℝ} (hL : 0 ≤ L) : metricEnergy (portTestVector L) = 2 * L ^ 3 / 3 := by
  rw [portTestVector, metricEnergy_preFlat, integral_norm_sq_portTestField hL]

/-- `β(f_L) = −2iL³/3`. -/
theorem onePortInput_portTestVector {L : ℝ} (hL : 0 ≤ L) :
    onePortInput (portTestVector L) = -Complex.I * ((2 * L ^ 3 / 3 : ℝ) : ℂ) := by
  rw [portTestVector, onePortInput_preFlat, integral_sq_portTestField hL]

/-- **The input port has no bounded extension to the metric-energy completion.** -/
theorem not_exists_onePortInput_bounded :
    ¬ ∃ C : ℝ, ∀ f ∈ meanZeroSpace, ‖onePortInput f‖ ≤ C * Real.sqrt (metricEnergy f) := by
  rintro ⟨C, hC⟩
  set L : ℝ := C ^ 2 + 2
  have hL : 0 ≤ L := by positivity
  have h := hC _ (portTestVector_mem L)
  rw [onePortInput_portTestVector hL, metricEnergy_portTestVector hL, norm_mul, norm_neg, Complex.norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
  -- `E = 2L³/3 = s²` with `s = √E`; then `s² ≤ C s` forces `s ≤ C`, impossible for `L ≥ C² + 2`
  set E : ℝ := 2 * L ^ 3 / 3
  have hE : 0 < E := by positivity
  have hs := Real.sq_sqrt hE.le
  have hspos : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hsC : Real.sqrt E ≤ C := by nlinarith
  have hEC : E ≤ C ^ 2 := by
    rw [← hs]; exact pow_le_pow_left₀ hspos.le hsC 2
  have hL2 : 2 ≤ L := by simp only [L]; nlinarith [sq_nonneg C]
  have hL3 : 4 * L ≤ L ^ 3 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ L) (by nlinarith : (0 : ℝ) ≤ L ^ 2 - 4)]
  have hEL : E = 2 * L ^ 3 / 3 := rfl
  have hLC : L = C ^ 2 + 2 := rfl
  nlinarith

/-! ## The flat energy space and its two ports -/

local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)

/-- The flat field as a vector of `L²(ℝ)`. -/
def flatLp (f : ThetaL2) : FlatL2 := (memLp_flatField f).toLp

theorem flatLp_ae (f : ThetaL2) : (flatLp f : ℝ → ℂ) =ᵐ[volume] flatField f := MemLp.coeFn_toLp _

theorem norm_sq_flatLp (f : ThetaL2) : ‖flatLp f‖ ^ 2 = metricEnergy f := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, metricEnergy_eq_integral_flatField]
  have h : (fun a => ⟪(flatLp f : ℝ → ℂ) a, (flatLp f : ℝ → ℂ) a⟫_ℂ) =ᵐ[volume]
      fun a => ((‖flatField f a‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [flatLp_ae f] with a ha
    rw [ha, inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [integral_congr_ae h, integral_complex_ofReal, RCLike.re_to_complex, Complex.ofReal_re]

theorem norm_flatLp (f : ThetaL2) : ‖flatLp f‖ = Real.sqrt (metricEnergy f) := by
  rw [← norm_sq_flatLp, Real.sqrt_sq (norm_nonneg _)]

/-- **The outgoing port is square integrable**: `ρ ∈ L²(ℝ)`. -/
theorem memLp_normalized : MemLp (fun x => (thetaSource.normalized x : ℂ)) 2 volume := by
  have hm : AEStronglyMeasurable (fun x => (thetaSource.normalized x : ℂ)) volume :=
    (Complex.continuous_ofReal.comp continuous_normalized_theta).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  have hint : Integrable thetaSource.normalized volume := thetaSource.integrable_k.div_const _
  refine (hint.const_mul (thetaBound / thetaSource.mass)).mono'
    (hm.norm.pow 2) (Eventually.of_forall fun x => ?_)
  have hρ := thetaSource.normalized_pos x
  have hle : thetaSource.normalized x ≤ thetaBound / thetaSource.mass :=
    div_le_div_of_nonneg_right (thetaSource_le x) thetaSource.mass_pos.le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  nlinarith

/-- The outgoing port vector `ρ` of `L²(ℝ)`. -/
def outPortLp : FlatL2 := memLp_normalized.toLp

/-- **The incoming port is not square integrable**: the coordinate `x ∉ L²(ℝ)`. -/
theorem not_memLp_coordinate : ¬ MemLp (fun x : ℝ => (x : ℂ)) 2 volume := by
  intro h
  have hint := (memLp_two_iff_integrable_sq_norm h.1).1 h
  have hon : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici 1) := by
    refine (hint.integrableOn (s := Ici 1)).mono' aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun x hx => ?_)
    have hx1 : (1 : ℝ) ≤ x := hx
    rw [Real.norm_eq_abs, abs_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    nlinarith
  rw [integrableOn_const_iff] at hon
  rcases hon with h0 | hfin
  · simp at h0
  · rw [Real.volume_Ici] at hfin
    exact lt_irrefl _ hfin

theorem inner_outPortLp_flatLp {f : ThetaL2} (hf : f ∈ meanZeroSpace) :
    ⟪outPortLp, flatLp f⟫_ℂ = ⟪onePortOutputVector, f⟫_ℂ := by
  rw [inner_onePortOutputVector hf, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [flatLp_ae f, MemLp.coeFn_toLp memLp_normalized] with x h1 h2
  rw [h1, show (outPortLp : ℝ → ℂ) = (memLp_normalized.toLp : ℝ → ℂ) from rfl, h2,
    RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

/-- **The output functional is bounded by `‖ρ‖₂`** in the metric energy. -/
theorem norm_inner_onePortOutputVector_le {f : ThetaL2} (hf : f ∈ meanZeroSpace) :
    ‖⟪onePortOutputVector, f⟫_ℂ‖ ≤ ‖outPortLp‖ * Real.sqrt (metricEnergy f) := by
  rw [← inner_outPortLp_flatLp hf, ← norm_flatLp]
  exact norm_inner_le_norm _ _

/-- **The metric-energy completion is flat `L²`**: the image of `H₀` is dense in `L²(ℝ)`. -/
theorem dense_flatLp_meanZeroSpace : Dense (flatLp '' (meanZeroSpace : Set ThetaL2)) := by
  have hD := Lp.dense_hasCompactSupport_contDiff (E := ℝ) (F := ℂ) (μ := volume) (p := 2) (by norm_num)
  rw [Metric.dense_iff] at hD ⊢
  intro w ε hε
  obtain ⟨w', hw'ball, g, hg, hgc, hgs⟩ := hD w (ε / 2) (half_pos hε)
  have hgcont : Continuous g := hgs.continuous
  obtain ⟨Cg, hCg⟩ := hgcont.bounded_above_of_compact_support hgc
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hgc.isCompact.isBounded
  set m : ℂ := ∫ x, g x
  set R : ℝ := (2 * ‖m‖ / ε) ^ 2 + 1
  have hR : 0 < R := by positivity
  have hIcc : volume (Icc (0 : ℝ) R) ≠ ⊤ := measure_Icc_lt_top.ne
  set ind : FlatL2 := indicatorConstLp 2 measurableSet_Icc hIcc (m / R)
  set u : ℝ → ℂ := fun x => g x - (Icc (0 : ℝ) R).indicator (fun _ => m / R) x
  have hum : Measurable u := hgcont.measurable.sub (measurable_const.indicator measurableSet_Icc)
  have hub : ∃ C, ∀ x, ‖u x‖ ≤ C := ⟨Cg + ‖m / R‖, fun x => by
    refine (norm_sub_le _ _).trans (add_le_add (hCg x) ?_)
    exact norm_indicator_le_norm_self _ _⟩
  have huc : ∃ R', ∀ x, R' < |x| → u x = 0 := ⟨max r R, fun x hx => by
    have hxr : x ∉ tsupport g := fun h => by
      have := hr h
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      have := le_max_left r R
      linarith
    have hxR : x ∉ Icc (0 : ℝ) R := fun h => by
      have h1 : |x| ≤ R := by rw [abs_of_nonneg h.1]; exact h.2
      have := le_max_right r R
      linarith
    simp only [u, image_eq_zero_of_notMem_tsupport hxr, indicator_of_notMem hxR, sub_zero]⟩
  have hu : IsFlatTest u := ⟨hum, hub, huc⟩
  have hgi : Integrable g volume := hgcont.integrable_of_hasCompactSupport hgc
  have hu0 : ∫ x, u x = 0 := by
    simp only [u]
    rw [integral_sub hgi ((integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const hIcc (by simp))), integral_indicator_const _ measurableSet_Icc,
      Real.volume_real_Icc_of_le hR.le, sub_zero, Complex.real_smul]
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    field_simp
    ring
  set f := preFlat hu
  have hf : f ∈ meanZeroSpace := preFlat_mem_meanZeroSpace hu hu0
  have hflat : flatLp f = w' - ind := by
    apply Lp.ext
    filter_upwards [flatLp_ae f, flatField_preFlat hu, hg, Lp.coeFn_sub w' ind,
      indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Icc) (hμs := hIcc) (c := m / R)] with
      x h1 h2 h3 h4 h5
    rw [h1, h2, h4, Pi.sub_apply, h3, h5]
  have hind : ‖ind‖ < ε / 2 := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), Real.volume_real_Icc_of_le hR.le, sub_zero]
    have hsq : R ^ (1 / (2 : ENNReal).toReal) = Real.sqrt R := by
      rw [Real.sqrt_eq_rpow]; norm_num
    rw [hsq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
    have hRR : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt hR.le
    have hlt : 2 * ‖m‖ / ε < Real.sqrt R := by
      rw [Real.lt_sqrt (by positivity)]
      simp only [R]; linarith
    rw [div_lt_iff₀ hε] at hlt
    calc ‖m‖ / R * Real.sqrt R = ‖m‖ / Real.sqrt R := by
          rw [div_mul_eq_mul_div, div_eq_div_iff hR.ne' hsR.ne', mul_assoc, hRR]
      _ < ε / 2 := by
          rw [div_lt_iff₀ hsR]; nlinarith
  refine ⟨flatLp f, ?_, f, hf, rfl⟩
  rw [Metric.mem_ball, hflat, dist_eq_norm]
  calc ‖w' - ind - w‖ = ‖(w' - w) - ind‖ := by congr 1; abel
    _ ≤ ‖w' - w‖ + ‖ind‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := by
        refine add_lt_add ?_ hind
        rw [← dist_eq_norm]; exact hw'ball
    _ = ε := by ring

/-- **The output functional has exact norm `‖ρ‖₂`**: every constant below `‖ρ‖₂` is exceeded. -/
theorem exists_inner_onePortOutputVector_gt {c : ℝ} (hc : c < ‖outPortLp‖) :
    ∃ f ∈ meanZeroSpace, c * Real.sqrt (metricEnergy f) < ‖⟪onePortOutputVector, f⟫_ℂ‖ := by
  rcases lt_or_ge c 0 with hc0 | hc0
  · refine ⟨portTestVector 1, portTestVector_mem 1, ?_⟩
    have hE : 0 < Real.sqrt (metricEnergy (portTestVector 1)) := by
      rw [metricEnergy_portTestVector zero_le_one]; positivity
    have := norm_nonneg ⟪onePortOutputVector, portTestVector 1⟫_ℂ
    nlinarith
  · set a := ‖outPortLp‖
    have ha : 0 < a := lt_of_le_of_lt hc0 hc
    set δ := a * (a - c) / (2 * (c + a))
    have hδ : 0 < δ := div_pos (mul_pos ha (by linarith)) (by linarith)
    obtain ⟨_, hball, f, hf, rfl⟩ := Metric.dense_iff.1 dense_flatLp_meanZeroSpace outPortLp δ hδ
    refine ⟨f, hf, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hball
    rw [← inner_outPortLp_flatLp hf, ← norm_flatLp]
    set v := flatLp f
    have h1 : ‖v‖ ≤ a + δ := by
      have := norm_le_insert' v outPortLp
      calc ‖v‖ ≤ ‖outPortLp‖ + ‖v - outPortLp‖ := by
            have := norm_sub_norm_le v outPortLp; linarith
        _ ≤ a + δ := by linarith
    have h2 : a ^ 2 - a * δ ≤ ‖⟪outPortLp, v⟫_ℂ‖ := by
      have hsplit : ⟪outPortLp, v⟫_ℂ = ⟪outPortLp, outPortLp⟫_ℂ + ⟪outPortLp, v - outPortLp⟫_ℂ := by
        rw [inner_sub_right]; ring
      have hself : ‖⟪outPortLp, outPortLp⟫_ℂ‖ = a ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K]; simp [a]
      have hcross : ‖⟪outPortLp, v - outPortLp⟫_ℂ‖ ≤ a * δ :=
        (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hball.le ha.le)
      have := norm_sub_norm_le ⟪outPortLp, outPortLp⟫_ℂ (-⟪outPortLp, v - outPortLp⟫_ℂ)
      rw [sub_neg_eq_add, ← hsplit, norm_neg, hself] at this
      linarith
    have hkey : c * (a + δ) < a ^ 2 - a * δ := by
      have : δ * (c + a) = a * (a - c) / 2 := by
        simp only [δ]; field_simp
      nlinarith
    calc c * ‖v‖ ≤ c * (a + δ) := mul_le_mul_of_nonneg_left h1 hc0
      _ < a ^ 2 - a * δ := hkey
      _ ≤ _ := h2

end

end RHTower
