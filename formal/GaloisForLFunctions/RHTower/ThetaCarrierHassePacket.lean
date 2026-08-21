import GaloisForLFunctions.RHTower.ThetaTiltReflectedWork
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceSpectrumExact
import GaloisForLFunctions.HTGeometry.ConstitutiveFunctionalEquationPacketLift
import GaloisForLFunctions.HTGeometry.ConstitutiveHasseGlobalRenewal
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# The theta-carrier packet with Hasse recovery

The tilted theta laws form an exponential family whose reflection is the functional-equation
action.  Attaching the parameter-independent Hasse geometric recovery kernel produces a packet on
which the reflection lifts canonically and loses no relative-entropy information, while the
symmetric reflected work is `4 a F'(a)` and vanishes only at the critical centre.
-/

open MeasureTheory InformationTheory ProbabilityTheory GaloisForLFunctions.HTGeometry
open scoped ENNReal

namespace RHTower

noncomputable section

/-! ## Reflection of a density measure -/

theorem map_neg_withDensity (g : ℝ → ℝ≥0∞) :
    Measure.map (fun x : ℝ => -x) (volume.withDensity g)
      = volume.withDensity (fun x => g (-x)) := by
  ext s hs
  rw [Measure.map_apply measurable_neg hs, withDensity_apply _ (measurable_neg hs),
    withDensity_apply _ hs]
  rw [← MeasureTheory.lintegral_indicator hs,
    ← MeasureTheory.lintegral_indicator (measurable_neg hs)]
  rw [← MeasureTheory.lintegral_neg_eq_self (fun x => s.indicator (fun y => g (-y)) x)]
  congr 1
  funext x
  by_cases hx : -x ∈ s <;> simp [hx]

/-! ## The theta base measure -/

/-- The finite positive measure carried by the completed theta source. -/
def thetaBaseMeasure : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (thetaCuspFullSource x)

theorem measurable_thetaBaseDensity :
    Measurable (fun x : ℝ => ENNReal.ofReal (thetaCuspFullSource x)) :=
  ENNReal.measurable_ofReal.comp contDiff_thetaCuspFullSource.continuous.measurable

theorem integral_thetaBaseMeasure {f : ℝ → ℝ} :
    ∫ x : ℝ, f x ∂thetaBaseMeasure = ∫ x : ℝ, f x * thetaCuspFullSource x := by
  rw [thetaBaseMeasure,
    integral_withDensity_eq_integral_toReal_smul measurable_thetaBaseDensity
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (thetaCuspFullSource_pos_all _).le, smul_eq_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

theorem integrable_thetaBaseMeasure {f : ℝ → ℝ}
    (hf : Integrable (fun x : ℝ => f x * thetaCuspFullSource x)) :
    Integrable f thetaBaseMeasure := by
  rw [thetaBaseMeasure,
    integrable_withDensity_iff_integrable_smul₀' measurable_thetaBaseDensity.aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (thetaCuspFullSource_pos_all _).le, smul_eq_mul]
  exact hf.congr (Filter.Eventually.of_forall fun x => by ring)

theorem integrable_exp_mul_thetaBase {a : ℝ} (ha : |a| ≤ 1) :
    Integrable (fun x : ℝ => Real.exp (a * x)) thetaBaseMeasure := by
  refine integrable_thetaBaseMeasure ?_
  simpa using integrable_thetaTiltIntegrand ha 0

theorem integral_exp_mul_thetaBase (a : ℝ) :
    ∫ x : ℝ, Real.exp (a * x) ∂thetaBaseMeasure = thetaTiltMoment a 0 := by
  rw [integral_thetaBaseMeasure, thetaTiltMoment]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

theorem integrable_thetaCuspFullSource : Integrable thetaCuspFullSource := by
  simpa using integrable_thetaTiltIntegrand (a := 0) (by norm_num) 0

instance : IsFiniteMeasure thetaBaseMeasure := by
  constructor
  rw [thetaBaseMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal integrable_thetaCuspFullSource
      (Filter.Eventually.of_forall fun x => (thetaCuspFullSource_pos_all x).le)]
  exact ENNReal.ofReal_lt_top

instance : NeZero thetaBaseMeasure := by
  constructor
  intro hzero
  have hpos : 0 < thetaTiltMoment 0 0 := thetaTiltMoment_zero_pos 0 (by norm_num)
  have hint : ∫ x : ℝ, Real.exp (0 * x) ∂thetaBaseMeasure = thetaTiltMoment 0 0 :=
    integral_exp_mul_thetaBase 0
  rw [hzero] at hint
  simp at hint
  linarith [hpos, hint]

/-! ## The tilted theta probability laws -/

/-- The normalized theta law at tilt `a` (FEL.10). -/
def thetaTiltProb (a : ℝ) : Measure ℝ := thetaBaseMeasure.tilted (fun x => a * x)

theorem thetaTiltProb_isProbabilityMeasure {a : ℝ} (ha : |a| ≤ 1) :
    IsProbabilityMeasure (thetaTiltProb a) :=
  isProbabilityMeasure_tilted (integrable_exp_mul_thetaBase ha)

theorem thetaTiltProb_eq_withDensity {a : ℝ} (ha : |a| ≤ 1) :
    thetaTiltProb a =
      volume.withDensity fun x =>
        ENNReal.ofReal (Real.exp (a * x) * thetaCuspFullSource x / thetaTiltMoment a 0) := by
  have hM := thetaTiltMoment_zero_pos a ha
  have hmeas : Measurable
      (fun x : ℝ => ENNReal.ofReal (Real.exp (a * x) / thetaTiltMoment a 0)) :=
    ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).div_const
        (thetaTiltMoment a 0)).measurable
  rw [thetaTiltProb, Measure.tilted, integral_exp_mul_thetaBase a, thetaBaseMeasure,
    ← withDensity_mul _ measurable_thetaBaseDensity hmeas]
  congr 1
  funext x
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (thetaCuspFullSource_pos_all x).le]
  congr 1
  ring

/-- **(FEL.12).**  Reflection carries the tilt `a` to the tilt `-a`. -/
theorem map_neg_thetaTiltProb {a : ℝ} (ha : |a| ≤ 1) :
    Measure.map (fun x : ℝ => -x) (thetaTiltProb a) = thetaTiltProb (-a) := by
  have habs : |(-a)| ≤ 1 := by rwa [abs_neg]
  rw [thetaTiltProb_eq_withDensity ha, thetaTiltProb_eq_withDensity habs, map_neg_withDensity]
  congr 1
  funext x
  rw [thetaCuspFullSource_neg, thetaTiltMoment_zero_neg, show a * -x = -a * x by ring]

/-! ## Integrals against the tilted law -/

theorem thetaTiltDensityToReal {a : ℝ} (ha : |a| ≤ 1) (x : ℝ) :
    (ENNReal.ofReal
      (Real.exp (a * x) * thetaCuspFullSource x / thetaTiltMoment a 0)).toReal
      = Real.exp (a * x) * thetaCuspFullSource x / thetaTiltMoment a 0 := by
  refine ENNReal.toReal_ofReal ?_
  have hM := thetaTiltMoment_zero_pos a ha
  have := thetaCuspFullSource_pos_all x
  positivity

theorem measurable_thetaTiltProbDensity (a : ℝ) :
    Measurable (fun x : ℝ =>
      ENNReal.ofReal (Real.exp (a * x) * thetaCuspFullSource x / thetaTiltMoment a 0)) :=
  ENNReal.measurable_ofReal.comp
    ((((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      contDiff_thetaCuspFullSource.continuous)).div_const (thetaTiltMoment a 0)).measurable

theorem integral_thetaTiltProb {a : ℝ} (ha : |a| ≤ 1) (f : ℝ → ℝ) :
    ∫ x : ℝ, f x ∂thetaTiltProb a
      = (∫ x : ℝ, f x * Real.exp (a * x) * thetaCuspFullSource x) / thetaTiltMoment a 0 := by
  rw [thetaTiltProb_eq_withDensity ha,
    integral_withDensity_eq_integral_toReal_smul (measurable_thetaTiltProbDensity a)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [thetaTiltDensityToReal ha, smul_eq_mul]
  rw [← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

theorem integrable_thetaTiltProb {a : ℝ} (ha : |a| ≤ 1) {f : ℝ → ℝ}
    (hf : Integrable (fun x : ℝ => f x * Real.exp (a * x) * thetaCuspFullSource x)) :
    Integrable f (thetaTiltProb a) := by
  have hM := thetaTiltMoment_zero_pos a ha
  rw [thetaTiltProb_eq_withDensity ha,
    integrable_withDensity_iff_integrable_smul₀' (measurable_thetaTiltProbDensity a).aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [thetaTiltDensityToReal ha, smul_eq_mul]
  refine (hf.div_const (thetaTiltMoment a 0)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  show f x * Real.exp (a * x) * thetaCuspFullSource x / thetaTiltMoment a 0
    = Real.exp (a * x) * thetaCuspFullSource x / thetaTiltMoment a 0 * f x
  ring

theorem integrable_id_thetaTiltProb {a : ℝ} (ha : |a| ≤ 1) :
    Integrable (fun x : ℝ => x) (thetaTiltProb a) := by
  refine integrable_thetaTiltProb ha ?_
  simpa only [pow_one] using integrable_thetaTiltIntegrand ha 1

theorem integral_id_thetaTiltProb {a : ℝ} (ha : |a| ≤ 1) :
    ∫ x : ℝ, x ∂thetaTiltProb a = thetaTiltMean a := by
  rw [integral_thetaTiltProb ha, thetaTiltMean, thetaTiltMoment]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-! ## The reflection tilt and its information -/

theorem thetaTiltProb_tilt {a b : ℝ} (hb : |b| ≤ 1) :
    (thetaTiltProb b).tilted (fun x : ℝ => (a - b) * x) = thetaTiltProb a := by
  rw [thetaTiltProb, thetaTiltProb, tilted_tilted (integrable_exp_mul_thetaBase hb)]
  refine tilted_congr ?_
  filter_upwards with x
  simp only [Pi.add_apply]
  ring

theorem integrable_exp_reflection {a : ℝ} (ha : |a| ≤ 1) :
    Integrable (fun x : ℝ => Real.exp (2 * a * x)) (thetaTiltProb (-a)) := by
  have habs : |(-a)| ≤ 1 := by rwa [abs_neg]
  refine integrable_thetaTiltProb habs ?_
  have hint := integrable_thetaTiltIntegrand ha 0
  refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
  show x ^ 0 * Real.exp (a * x) * thetaCuspFullSource x
    = Real.exp (2 * a * x) * Real.exp (-a * x) * thetaCuspFullSource x
  rw [← Real.exp_add, show 2 * a * x + -a * x = a * x by ring]
  ring

theorem integral_exp_reflection {a : ℝ} (ha : |a| ≤ 1) :
    ∫ x : ℝ, Real.exp (2 * a * x) ∂thetaTiltProb (-a) = 1 := by
  have habs : |(-a)| ≤ 1 := by rwa [abs_neg]
  have hM := thetaTiltMoment_zero_pos a ha
  rw [integral_thetaTiltProb habs, thetaTiltMoment_zero_neg]
  rw [show (∫ x : ℝ, Real.exp (2 * a * x) * Real.exp (-a * x) * thetaCuspFullSource x)
      = thetaTiltMoment a 0 by
    rw [thetaTiltMoment]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Real.exp (2 * a * x) * Real.exp (-a * x) * thetaCuspFullSource x
      = x ^ 0 * Real.exp (a * x) * thetaCuspFullSource x
    rw [← Real.exp_add, show 2 * a * x + -a * x = a * x by ring]
    ring]
  exact div_self hM.ne'

/-- **(FEL.20).**  The reflected log-likelihood ratio of the theta carrier is the linear
statistic. -/
theorem llr_thetaTiltProb_reflection {a : ℝ} (ha : |a| ≤ 1) :
    llr (thetaTiltProb a) (thetaTiltProb (-a)) =ᵐ[thetaTiltProb (-a)]
      fun x : ℝ => 2 * a * x := by
  have habs : |(-a)| ≤ 1 := by rwa [abs_neg]
  haveI := thetaTiltProb_isProbabilityMeasure habs
  have hlog := log_rnDeriv_tilted_left_self (μ := thetaTiltProb (-a))
    (f := fun x : ℝ => 2 * a * x) (integrable_exp_reflection ha)
  rw [integral_exp_reflection ha, Real.log_one] at hlog
  have htilt : (thetaTiltProb (-a)).tilted (fun x : ℝ => 2 * a * x) = thetaTiltProb a := by
    rw [show (fun x : ℝ => 2 * a * x) = fun x : ℝ => (a - -a) * x by funext x; ring]
    exact thetaTiltProb_tilt habs
  rw [htilt] at hlog
  filter_upwards [hlog] with x hx
  show Real.log (((thetaTiltProb a).rnDeriv (thetaTiltProb (-a))) x).toReal = 2 * a * x
  rw [hx]
  ring

theorem thetaTiltProb_absolutelyContinuous {a : ℝ} (ha : |a| ≤ 1) :
    thetaTiltProb a ≪ thetaTiltProb (-a) := by
  have habs : |(-a)| ≤ 1 := by rwa [abs_neg]
  rw [← thetaTiltProb_tilt (a := a) habs]
  exact tilted_absolutelyContinuous _ _

/-- **(FEL.21).**  The directed reflected cost is `2 a F'(a)`. -/
theorem toReal_klDiv_thetaTiltProb_reflection {a : ℝ} (ha : |a| ≤ 1) :
    (klDiv (thetaTiltProb a) (thetaTiltProb (-a))).toReal = 2 * a * thetaTiltMean a := by
  have habs : |(-a)| ≤ 1 := by rwa [abs_neg]
  haveI := thetaTiltProb_isProbabilityMeasure ha
  haveI := thetaTiltProb_isProbabilityMeasure habs
  have hac := thetaTiltProb_absolutelyContinuous ha
  rw [toReal_klDiv_of_measure_eq hac (by simp)]
  rw [integral_congr_ae (hac.ae_le (llr_thetaTiltProb_reflection ha))]
  rw [show (fun x : ℝ => 2 * a * x) = fun x : ℝ => (2 * a) * x by funext x; ring]
  rw [integral_const_mul, integral_id_thetaTiltProb ha]

/-- **(FEL.21).**  The reverse directed reflected cost is the same. -/
theorem toReal_klDiv_thetaTiltProb_reflection_reverse {a : ℝ} (ha : |a| ≤ 1) :
    (klDiv (thetaTiltProb (-a)) (thetaTiltProb a)).toReal = 2 * a * thetaTiltMean a := by
  have habs : |(-a)| ≤ 1 := by rwa [abs_neg]
  have h := toReal_klDiv_thetaTiltProb_reflection habs
  rw [neg_neg] at h
  rw [h, thetaTiltMean_neg]
  ring

/-- **(FEL.24).**  The functional-equation action has zero directed information chirality. -/
theorem klDiv_thetaTiltProb_chirality_zero {a : ℝ} (ha : |a| ≤ 1) :
    (klDiv (thetaTiltProb a) (thetaTiltProb (-a))).toReal
      - (klDiv (thetaTiltProb (-a)) (thetaTiltProb a)).toReal = 0 := by
  rw [toReal_klDiv_thetaTiltProb_reflection ha, toReal_klDiv_thetaTiltProb_reflection_reverse ha]
  ring

/-- **(FEL.22).**  The symmetric reflected work is `4 a F'(a)`. -/
theorem klDiv_thetaTiltProb_jeffreys {a : ℝ} (ha : |a| ≤ 1) :
    (klDiv (thetaTiltProb a) (thetaTiltProb (-a))).toReal
      + (klDiv (thetaTiltProb (-a)) (thetaTiltProb a)).toReal
      = 4 * a * thetaTiltMean a := by
  rw [toReal_klDiv_thetaTiltProb_reflection ha, toReal_klDiv_thetaTiltProb_reflection_reverse ha]
  ring

/-- **(FEL.23).**  The reflected work vanishes exactly at the critical centre. -/
theorem klDiv_thetaTiltProb_jeffreys_eq_zero_iff {a : ℝ} (ha : |a| < 1) :
    (klDiv (thetaTiltProb a) (thetaTiltProb (-a))).toReal
      + (klDiv (thetaTiltProb (-a)) (thetaTiltProb a)).toReal = 0 ↔ a = 0 := by
  rw [klDiv_thetaTiltProb_jeffreys ha.le]
  exact thetaTiltReflectedWork_eq_zero_iff ha

/-! ## The theta carrier with Hasse recovery -/

/-- The Hasse recovery profile on the logarithmic theta coordinate (FEL.13). -/
def thetaHasseProfile : HasseHistoryProfile ℝ where
  scale := Real.exp
  measurable_scale := Real.measurable_exp
  scale_pos := Real.exp_pos

/-- The theta-carrier packet with Hasse recovery (FEL.14). -/
def thetaCarrierPacket (a : ℝ) : Measure (ℝ × ℕ) :=
  splitFormation (thetaTiltProb a) thetaHasseProfile.kernel

/-- **Theorem 5.1** (FEL.16).  The functional-equation lift carries the tilt `a` to `-a`. -/
theorem thetaCarrierPacket_reflect {a : ℝ} (ha : |a| ≤ 1) :
    formationLiftKernel thetaHasseProfile.kernel (fun x : ℝ => -x) measurable_neg
        ∘ₘ thetaCarrierPacket a = thetaCarrierPacket (-a) := by
  haveI := thetaTiltProb_isProbabilityMeasure ha
  rw [thetaCarrierPacket, thetaCarrierPacket,
    formationLiftKernel_naturality (thetaTiltProb a) thetaHasseProfile.kernel
      (fun x : ℝ => -x) measurable_neg, map_neg_thetaTiltProb ha]

/-- **Theorem 5.1** (FEL.16).  The lift is an involution on formed packets. -/
theorem thetaCarrierPacket_reflect_involution {a : ℝ} (ha : |a| ≤ 1) :
    formationLiftKernel thetaHasseProfile.kernel (fun x : ℝ => -x) measurable_neg
        ∘ₘ (formationLiftKernel thetaHasseProfile.kernel (fun x : ℝ => -x) measurable_neg
          ∘ₘ thetaCarrierPacket a) = thetaCarrierPacket a := by
  haveI := thetaTiltProb_isProbabilityMeasure ha
  exact formationLiftKernel_involution_on_formation (thetaTiltProb a) thetaHasseProfile.kernel
    (fun x : ℝ => -x) measurable_neg (fun x => neg_neg x)

/-- **Theorem 5.1** (FEL.17).  The Hasse recovery kernel is information sufficient. -/
theorem klDiv_thetaCarrierPacket {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    klDiv (thetaCarrierPacket a) (thetaCarrierPacket b)
      = klDiv (thetaTiltProb a) (thetaTiltProb b) := by
  haveI := thetaTiltProb_isProbabilityMeasure ha
  haveI := thetaTiltProb_isProbabilityMeasure hb
  exact klDiv_splitFormation (thetaTiltProb a) (thetaTiltProb b) thetaHasseProfile.kernel

/-- **Theorem 5.1** (FEL.18).  The lift is exactly information neutral on the packet. -/
theorem klDiv_thetaCarrierPacket_lift_isometry {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    klDiv
        (formationLiftKernel thetaHasseProfile.kernel (fun x : ℝ => -x) measurable_neg
          ∘ₘ thetaCarrierPacket a)
        (formationLiftKernel thetaHasseProfile.kernel (fun x : ℝ => -x) measurable_neg
          ∘ₘ thetaCarrierPacket b)
      = klDiv (thetaCarrierPacket a) (thetaCarrierPacket b) := by
  haveI := thetaTiltProb_isProbabilityMeasure ha
  haveI := thetaTiltProb_isProbabilityMeasure hb
  exact formationLiftKernel_klDiv_isometry (thetaTiltProb a) (thetaTiltProb b)
    thetaHasseProfile.kernel (fun x : ℝ => -x)
    (measurableEmbedding_of_measurable_involution measurable_neg (fun x => neg_neg x))

/-- **(FEL.22) on the packet.**  The reflected packet work is `4 a F'(a)`, so it vanishes exactly
at the critical centre: information neutrality is an isometry law, not a selection law. -/
theorem klDiv_thetaCarrierPacket_jeffreys_eq_zero_iff {a : ℝ} (ha : |a| < 1) :
    (klDiv (thetaCarrierPacket a) (thetaCarrierPacket (-a))).toReal
      + (klDiv (thetaCarrierPacket (-a)) (thetaCarrierPacket a)).toReal = 0 ↔ a = 0 := by
  have habs : |(-a)| ≤ 1 := by rw [abs_neg]; exact ha.le
  rw [klDiv_thetaCarrierPacket ha.le habs, klDiv_thetaCarrierPacket habs ha.le]
  exact klDiv_thetaTiltProb_jeffreys_eq_zero_iff ha

/-! ## The literal Xi identification -/

/-- **(FEL.9)–(FEL.10).**  The tilt partition of the theta carrier is the centred `Xi` at the
imaginary argument, hence strictly positive on the whole open unit tilt interval. -/
theorem thetaTiltMoment_zero_eq_XiC (a : ℝ) :
    ((thetaTiltMoment a 0 : ℝ) : ℂ) = XiC (Complex.I * (a : ℂ)) := by
  rw [← HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all, thetaCuspFourierLaplace,
    thetaTiltMoment, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  rw [thetaCuspFourierLaplaceIntegrand]
  push_cast
  rw [show -Complex.I * (Complex.I * (a : ℂ)) * (x : ℂ)
      = -(Complex.I * Complex.I) * ((a : ℂ) * (x : ℂ)) by ring, Complex.I_mul_I,
    pow_zero, one_mul]
  norm_num

/-- The centred `Xi` is strictly positive on the imaginary segment of the tilt interval. -/
theorem XiC_imaginary_pos {a : ℝ} (ha : |a| ≤ 1) : 0 < (XiC (Complex.I * (a : ℂ))).re := by
  rw [← thetaTiltMoment_zero_eq_XiC, Complex.ofReal_re]
  exact thetaTiltMoment_zero_pos a ha

end

end RHTower
