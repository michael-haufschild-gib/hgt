import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCollarCurrentBounds
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Original horizon-current remainders and physical cutoff comparison

The unchanged source-current and full-forcing remainders are absolutely integrable
on a product collar in horizon length and ingoing time. Measurability and all
majorants are derived from the original fields and the normalizable radial reader.
The source-current result holds on its Laplace convergence half-plane; the full
forcing result holds at each fixed angular point on the right half-plane.

Static-time cutoffs use `p+L/2<T`; radial cutoffs use `L/2<T`. For each actual
remainder, both exhaust the same product integral and their difference tends to
zero. The nonintegrable leading horizon density is deliberately retained outside
this comparison. Its first temporal moment, the full angular finite part, and
attachment to the complete metric/QNM action remain separate requirements.
-/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalCornerCurrentAdmission
open D4BMJointSource D4BMModularCore D4BMLaplaceRadial D4BMOriginalCausalAdmission
open D4BMOriginalHorizonTimeTrace D4BMOriginalCharacteristicTransform D4BMOriginalCollarCurrentBounds
noncomputable section
set_option autoImplicit false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private theorem reader_re_nonneg (q : XiZeroCopy) :
    0 ≤ (D4BMOriginalCirclePeriod.readerExponent q).re := by
  have hr := (xi_divisor_support_re_mem_open_unit q.1).2
  norm_num [D4BMOriginalCirclePeriod.readerExponent]
  linarith

/-- The actual normalized radial reader in the original collar coordinate. -/
def reader (w chi : ℂ) (L : ℝ) : ℂ :=
  Complex.exp (w*((-L/2:ℝ):ℂ))*tortoiseMode true w chi (-L/2)

def readerTrace (w chi : ℂ) : ℂ := connection w chi/(2*w)*power (-w) 2

/-- The unchanged causal scalar on a fixed physical radius. -/
def scalar (q : XiZeroCopy) (br : Bool) (amp : ℂ) (L p : ℝ) : ℂ :=
  originalScalar q br amp p (p+L)

/-- The actual source-current expression minus its actual horizon expression. -/
def sourceRemainder (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (v : ℝ × ℝ) : ℂ :=
  Complex.exp (-w*(v.2:ℂ))*(reader w (physicalRadialFrequency q) v.1*
    (deriv (scalar q br amp v.1) v.2+w*scalar q br amp v.1 v.2)-
    readerTrace w (physicalRadialFrequency q)*
      (deriv (horizonTrace q br amp) v.2+w*horizonTrace q br amp v.2))

private theorem scalar_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    Continuous (Function.uncurry (scalar q br amp)) := by
  have hV : Continuous (fun v : ℝ × ℝ =>
      collarValue (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q br) amp v.1 v.2) := by
    have hc := (D4BMNativeResponse.radialResponse_continuous
      (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q br) amp).comp
        (show Continuous (fun v : ℝ × ℝ => ((v.2+(v.2+v.1))/2,(v.2-(v.2+v.1))/2)) by fun_prop)
    simpa only [Function.comp_def,collarValue,nullValue] using hc
  have hL : Continuous (fun v : ℝ × ℝ => liftCoefficient (physicalRate q br) amp v.1) := by
    have h : Continuous (radialLift (physicalRate q br) 0 amp 1) :=
      continuous_iff_continuousAt.mpr (fun x => (radialLift_hasDerivAt _ _ _ _ x).continuousAt)
    simpa only [Function.comp_def,liftCoefficient] using
      h.comp (show Continuous (fun v : ℝ × ℝ => -v.1/2) by fun_prop)
  have hO : Continuous (fun v : ℝ × ℝ => timeOnset (2*physicalRate q br) v.2) := by
    have h : Continuous (timeOnset (2*physicalRate q br)) :=
      continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt _ p).continuousAt)
    exact h.comp continuous_snd
  change Continuous (fun v : ℝ × ℝ => originalScalar q br amp v.2 (v.2+v.1))
  simp_rw [original_scalar_on_collar]
  exact (hV.add (hL.mul hO)).const_mul (physicalSelfSourceCoefficient q)

private theorem reader_continuousAt (w chi : ℂ) {L : ℝ} (hL : 0 < L) :
    ContinuousAt (reader w chi) L := by
  have hx : -L/2 < 0 := by linarith
  have hc := (horizonCoordinate_hasDerivAt (-L/2)).continuousAt.comp_of_eq
    (show ContinuousAt (fun l : ℝ => -l/2) L by fun_prop) rfl
  have hn := (normalizable_derivatives_continued (w:=w) (chi:=chi)
    (horizonCoordinate_interior (-L/2) hx)).1.continuousAt.comp_of_eq hc rfl
  have h := (show ContinuousAt (fun l : ℝ => Complex.exp (w*((-l/2:ℝ):ℂ))) L by fun_prop).mul hn
  change ContinuousAt (fun l : ℝ => Complex.exp (w*((-l/2:ℝ):ℂ))*
    normalizable w chi (horizonCoordinate (-l/2))) L
  convert h using 1
  funext l
  rfl

private theorem source_remainder_measurable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    {L0 : ℝ} (hL0 : 0 ≤ L0) :
    AEStronglyMeasurable (sourceRemainder q br amp w)
      (volume.restrict (Ioi L0 ×ˢ Ioi (0:ℝ))) := by
  let S := Ioi L0 ×ˢ Ioi (0:ℝ)
  have hS : MeasurableSet S := measurableSet_Ioi.prod measurableSet_Ioi
  have hm : AEStronglyMeasurable (fun v : ℝ × ℝ => scalar q br amp v.1 v.2) (volume.restrict S) :=
    (scalar_continuous q br amp).aestronglyMeasurable
  have hdm : AEStronglyMeasurable (fun v : ℝ × ℝ => deriv (scalar q br amp v.1) v.2) (volume.restrict S) :=
    (measurable_deriv_with_param (scalar_continuous q br amp)).aestronglyMeasurable
  have hdH : AEStronglyMeasurable (fun v : ℝ × ℝ => deriv (horizonTrace q br amp) v.2) (volume.restrict S) :=
    ((measurable_deriv (horizonTrace q br amp)).comp measurable_snd).aestronglyMeasurable
  have hH : AEStronglyMeasurable (fun v : ℝ × ℝ => horizonTrace q br amp v.2) (volume.restrict S) := by
    apply ContinuousOn.aestronglyMeasurable _ hS
    intro v hv
    exact ((horizon_trace_hasDerivAt q br amp hv.2).continuousAt.comp continuous_snd.continuousAt).continuousWithinAt
  have hn : AEStronglyMeasurable (fun v : ℝ × ℝ => reader w (physicalRadialFrequency q) v.1) (volume.restrict S) := by
    apply ContinuousOn.aestronglyMeasurable _ hS
    intro v hv
    exact ((reader_continuousAt w _ (hL0.trans_lt hv.1)).comp continuous_fst.continuousAt).continuousWithinAt
  have he : AEStronglyMeasurable (fun v : ℝ × ℝ => Complex.exp (-w*(v.2:ℂ))) (volume.restrict S) :=
    (show Continuous (fun v : ℝ × ℝ => Complex.exp (-w*(v.2:ℂ))) by fun_prop).aestronglyMeasurable
  exact he.mul ((hn.mul (hdm.add (hm.const_mul w))).sub
    ((hdH.add (hH.const_mul w)).const_mul (readerTrace w (physicalRadialFrequency q))))

private theorem product_majorant_integrable (a c B L0 : ℝ) (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun v : ℝ × ℝ => B*(Real.exp (-v.1)+Real.exp (-a*v.1))*Real.exp (-c*v.2))
      (Ioi L0 ×ˢ Ioi (0:ℝ)) := by
  have h1 := integrableOn_exp_mul_Ioi (a:=(-1:ℝ)) (by norm_num) L0
  have h2 := integrableOn_exp_mul_Ioi (a:=-a) (neg_neg_of_pos ha) L0
  have hp := integrableOn_exp_mul_Ioi (a:=-c) (neg_neg_of_pos hc) 0
  have h := (((h1.add h2).const_mul B).mul_prod hp)
  simpa only [IntegrableOn,Measure.prod_restrict,Measure.volume_eq_prod,neg_one_mul,Pi.add_apply] using h

private theorem integrable_of_collar_bound (f : ℝ × ℝ → ℂ) (a c : ℝ)
    (ha : 0 < a) (hc : 0 < c)
    (hmeas : ∀ L0 : ℝ, 0 ≤ L0 → AEStronglyMeasurable f (volume.restrict (Ioi L0 ×ˢ Ioi (0:ℝ))))
    (hbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ L : ℝ in atTop, ∀ p : ℝ, 0 < p →
      ‖f (L,p)‖ ≤ B*(Real.exp (-L)+Real.exp (-a*L))*Real.exp (-c*p)) :
    ∃ L0 : ℝ, 0 < L0 ∧ IntegrableOn f (Ioi L0 ×ˢ Ioi (0:ℝ)) := by
  obtain ⟨B,hB,hb⟩ := hbound
  obtain ⟨L1,hL1⟩ := eventually_atTop.mp hb
  let L0 := max L1 1
  have hL0 : 0 < L0 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨L0,hL0,?_⟩
  apply (product_majorant_integrable a c B L0 ha hc).mono' (hmeas L0 hL0.le)
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with v hv
  exact hL1 v.1 ((le_max_left _ _).trans hv.1.le) v.2 hv.2

/-- The original scalar-current horizon remainder is absolutely integrable on a whole
ingoing-time/horizon product collar, with its actual time derivative and physical reader. -/
theorem original_source_remainder_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im ≠ 0) (hwr : (D4BMOriginalCirclePeriod.readerExponent q).re < w.re) :
    ∃ L0 : ℝ, 0 < L0 ∧ IntegrableOn (sourceRemainder q br amp w) (Ioi L0 ×ˢ Ioi (0:ℝ)) := by
  apply integrable_of_collar_bound _ w.re (w.re-(D4BMOriginalCirclePeriod.readerExponent q).re)
    ((reader_re_nonneg q).trans_lt hwr) (sub_pos.mpr hwr)
    (fun L0 hL0 => source_remainder_measurable q br amp w hL0)
  obtain ⟨B,hB,hb⟩ := original_source_reader_current_error q br amp w hw hwr
  refine ⟨B,hB,?_⟩
  filter_upwards [hb] with L h p hp
  unfold sourceRemainder reader readerTrace
  change ‖Complex.exp (-w*(p:ℂ))*(
    Complex.exp (w*((-L/2:ℝ):ℂ))*tortoiseMode true w (physicalRadialFrequency q) (-L/2)*
      (deriv (fun a => originalScalar q br amp a (a+L)) p+w*originalScalar q br amp p (p+L))-
    connection w (physicalRadialFrequency q)/(2*w)*power (-w) 2*
      (deriv (horizonTrace q br amp) p+w*horizonTrace q br amp p))‖ ≤ _
  rw [(horizon_trace_hasDerivAt q br amp hp).deriv]
  exact h p hp

open D4BMOriginalCornerForcing

/-- The original full forcing paired with the same radial reader, minus its horizon trace. -/
def forcingRemainder (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (z : D4BMHorizon.Point) (v : ℝ × ℝ) : ℂ :=
  Complex.exp (-w*(v.2:ℂ))*(reader w (physicalRadialFrequency q) v.1*
    (timeOriginalForcing q br amp (v.2+v.1/2) (-v.1/2) z/(horizonCoordinate (-v.1/2):ℂ))-
    readerTrace w (physicalRadialFrequency q)*
      forcingTrace (physicalRate q br) amp (fullSquarePotential q z) (fullGradientEnergy q z/2) v.2)

private theorem profile_continuous (s amp J K : ℂ) :
    Continuous (fun v : ℝ × ℝ => forcingProfile s amp J K (radialUnit (-v.1/2))) := by
  have hu : Continuous (fun v : ℝ × ℝ => radialUnit (-v.1/2)) :=
    (continuous_iff_continuousAt.mpr (fun x => (radialUnit_hasDerivAt x).continuousAt)).comp
      (show Continuous (fun v : ℝ × ℝ => -v.1/2) by fun_prop)
  have hp : Continuous (fun v : ℝ × ℝ => power (2*s) (1+radialUnit (-v.1/2))) :=
    continuous_iff_continuousAt.mpr (fun v =>
      (power_derivatives (2*s) (radialUnit_add_one_pos (-v.1/2))).1.continuousAt.comp_of_eq
        (continuous_const.add hu).continuousAt rfl)
  unfold forcingProfile
  fun_prop

private theorem forcing_remainder_measurable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (z : D4BMHorizon.Point) {L0 : ℝ} (hL0 : 0 ≤ L0) :
    AEStronglyMeasurable (forcingRemainder q br amp w z)
      (volume.restrict (Ioi L0 ×ˢ Ioi (0:ℝ))) := by
  let S := Ioi L0 ×ˢ Ioi (0:ℝ)
  have hS : MeasurableSet S := measurableSet_Ioi.prod measurableSet_Ioi
  have ho : Continuous (fun v : ℝ × ℝ => timeOnset (2*physicalRate q br) v.2) :=
    (continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt _ p).continuousAt)).comp continuous_snd
  have hprof := (profile_continuous (physicalRate q br) amp (fullSquarePotential q z)
    (fullGradientEnergy q z/2)).mul ho
  have hF : AEStronglyMeasurable (fun v : ℝ × ℝ =>
      timeOriginalForcing q br amp (v.2+v.1/2) (-v.1/2) z/(horizonCoordinate (-v.1/2):ℂ))
      (volume.restrict S) := by
    apply hprof.aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem hS] with v hv
    exact (original_full_forcing_normalized q br amp (hL0.trans_lt hv.1) v.2 z).symm
  have hH : AEStronglyMeasurable (fun v : ℝ × ℝ => forcingTrace (physicalRate q br) amp
      (fullSquarePotential q z) (fullGradientEnergy q z/2) v.2) (volume.restrict S) :=
    ho.aestronglyMeasurable.const_mul _
  have hn : AEStronglyMeasurable (fun v : ℝ × ℝ => reader w (physicalRadialFrequency q) v.1)
      (volume.restrict S) := by
    apply ContinuousOn.aestronglyMeasurable _ hS
    intro v hv
    exact ((reader_continuousAt w _ (hL0.trans_lt hv.1)).comp continuous_fst.continuousAt).continuousWithinAt
  have he : AEStronglyMeasurable (fun v : ℝ × ℝ => Complex.exp (-w*(v.2:ℂ))) (volume.restrict S) :=
    (show Continuous (fun v : ℝ × ℝ => Complex.exp (-w*(v.2:ℂ))) by fun_prop).aestronglyMeasurable
  exact he.mul ((hn.mul hF).sub (hH.const_mul (readerTrace w (physicalRadialFrequency q))))

/-- At each angular point, the unchanged full-forcing remainder is absolutely integrable
on an entire horizon/time collar. Both original angular source channels are retained. -/
theorem original_forcing_remainder_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im ≠ 0) (hwr : 0 < w.re) (z : D4BMHorizon.Point) :
    ∃ L0 : ℝ, 0 < L0 ∧ IntegrableOn (forcingRemainder q br amp w z)
      (Ioi L0 ×ˢ Ioi (0:ℝ)) := by
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  apply integrable_of_collar_bound _ w.re (w.re-(2*physicalRate q br).re) hwr (by linarith)
    (fun L0 hL0 => forcing_remainder_measurable q br amp w z hL0)
  exact original_full_forcing_reader_error q br amp w hw hwr.le z

/-- Static time is `p+L/2` on the unchanged ingoing collar. -/
def staticCut (f : ℝ × ℝ → ℂ) (L0 T : ℝ) : ℂ :=
  ∫ v in Ioi L0 ×ˢ Ioi (0:ℝ), {v : ℝ × ℝ | v.2+v.1/2 < T}.indicator f v

/-- A radial cutoff bounds `-x=L/2` while leaving the ingoing time unbounded. -/
def radialCut (f : ℝ × ℝ → ℂ) (L0 T : ℝ) : ℂ :=
  ∫ v in Ioi L0 ×ˢ Ioi (0:ℝ), {v : ℝ × ℝ | v.1/2 < T}.indicator f v

private theorem cutoff_limit {f : ℝ × ℝ → ℂ} {L0 : ℝ}
    (hf : IntegrableOn f (Ioi L0 ×ˢ Ioi (0:ℝ))) (clock : ℝ × ℝ → ℝ) (hc : Continuous clock) :
    Tendsto (fun T : ℝ => ∫ v in Ioi L0 ×ˢ Ioi (0:ℝ),
      {v : ℝ × ℝ | clock v < T}.indicator f v) atTop
      (𝓝 (∫ v in Ioi L0 ×ˢ Ioi (0:ℝ), f v)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun v => ‖f v‖)
  · exact Eventually.of_forall (fun T => hf.aestronglyMeasurable.indicator
      (measurableSet_lt hc.measurable measurable_const))
  · exact Eventually.of_forall (fun T => ae_of_all _ (fun v => norm_indicator_le_norm_self f v))
  · exact hf.norm
  · exact ae_of_all _ (fun v => tendsto_const_nhds.congr' (by
      filter_upwards [eventually_gt_atTop (clock v)] with T hT
      exact (Set.indicator_of_mem (show v ∈ {u : ℝ × ℝ | clock u < T} from hT) f).symm))

private theorem cutoff_difference_limit {f : ℝ × ℝ → ℂ} {L0 : ℝ}
    (hf : IntegrableOn f (Ioi L0 ×ˢ Ioi (0:ℝ))) :
    Tendsto (fun T => staticCut f L0 T-radialCut f L0 T) atTop (𝓝 (0:ℂ)) := by
  have hs := cutoff_limit hf (fun v => v.2+v.1/2) (by fun_prop)
  have hr := cutoff_limit hf (fun v => v.1/2) (by fun_prop)
  simpa only [staticCut,radialCut,sub_self] using hs.sub hr

/-- The actual source-current remainder has no static-time/radial cutoff discrepancy.
Its proof derives product integrability from the original source and reader. -/
theorem original_source_remainder_cutoff_agreement (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im ≠ 0) (hwr : (D4BMOriginalCirclePeriod.readerExponent q).re < w.re) :
    ∃ L0 : ℝ, 0 < L0 ∧ IntegrableOn (sourceRemainder q br amp w) (Ioi L0 ×ˢ Ioi (0:ℝ)) ∧
      Tendsto (fun T => staticCut (sourceRemainder q br amp w) L0 T-
        radialCut (sourceRemainder q br amp w) L0 T) atTop (𝓝 (0:ℂ)) := by
  obtain ⟨L0,hL0,hf⟩ := original_source_remainder_integrable q br amp w hw hwr
  exact ⟨L0,hL0,hf,cutoff_difference_limit hf⟩

/-- The same cutoff agreement holds for the actual full-forcing remainder at each angular point. -/
theorem original_forcing_remainder_cutoff_agreement (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im ≠ 0) (hwr : 0 < w.re) (z : D4BMHorizon.Point) :
    ∃ L0 : ℝ, 0 < L0 ∧ IntegrableOn (forcingRemainder q br amp w z) (Ioi L0 ×ˢ Ioi (0:ℝ)) ∧
      Tendsto (fun T => staticCut (forcingRemainder q br amp w z) L0 T-
        radialCut (forcingRemainder q br amp w z) L0 T) atTop (𝓝 (0:ℂ)) := by
  obtain ⟨L0,hL0,hf⟩ := original_forcing_remainder_integrable q br amp w hw hwr z
  exact ⟨L0,hL0,hf,cutoff_difference_limit hf⟩

end
end RHTower.D4BMOriginalCornerCurrentAdmission
