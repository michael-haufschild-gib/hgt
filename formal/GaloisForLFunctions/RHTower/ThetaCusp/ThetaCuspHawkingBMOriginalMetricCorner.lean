import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalMetricTimePeriod
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalTemporalCorner

/-!
# Original metric collar and its temporal corner

The complete original metric period, with its prescribed angular subtraction,
is the compact time integral of the unchanged source-plus-forcing collar
current. The exact horizon factor cancels the extra metric radius factors;
the original radial Jacobian fixes the remaining factor one-half.

Subtracting the actual horizon trace gives an integrable remainder on the
unbounded time/horizon product. The moving static-time and time-first radial
cuts of this restored metric collar differ by the negative first temporal
moment and the fixed logarithmic coordinate shift. Their difference equals
the original meromorphic corner candidate on its convergence chamber.

The angular finite part is taken first. Independent cusp/time/horizon limits,
the outer region and the complete action's QNM identification are separate.
-/

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalMetricCorner
open D4BMJointSource D4BMJointWave D4BMModularCore D4BMLaplaceRadial
open D4BMOriginalCausalAdmission D4BMOriginalCausalPeriod D4BMOriginalCharacteristicTransform
open D4BMOriginalHorizonTimeTrace D4BMOriginalCollarCurrentBounds
open D4BMOriginalCornerCurrentAdmission D4BMOriginalCornerForcing D4BMOriginalTemporalCorner
open D4BMOriginalMetricTimePeriod D4BMOriginalReaderEquation D4BMIngoingCoordinates
noncomputable section
set_option autoImplicit false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private abbrev mu (q : XiZeroCopy) : ℂ := physicalAngularParameter q^(2 : ℕ)-1/4
private abbrev gradient (q : XiZeroCopy) (br : Bool) : ℂ :=
  reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1

def collarProfile (q : XiZeroCopy) (br : Bool) (amp : ℂ) (L : ℝ) : ℂ :=
  forcingProfile (physicalRate q br) amp 1 (gradient q br) (radialUnit (-L/2))

/-- The original angular-restored metric current multiplied by the horizon radial factor. -/
def collarDensity (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (v : ℝ×ℝ) : ℂ :=
  mu q*reader w (physicalRadialFrequency q) v.1*Complex.exp (-w*(v.2:ℂ))*
    ((mu q-2)*(deriv (scalar q br amp v.1) v.2+w*scalar q br amp v.1 v.2)+
      w*physicalSelfSourceCoefficient q*collarProfile q br amp v.1*timeOnset (2*physicalRate q br) v.2)

private theorem coordinate_factor (L : ℝ) (hL : 0<L) :
    (horizonCoordinate (-L/2):ℂ)=
      (((tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)/(tortoiseRadius (-L/2):ℂ)^(2 : ℕ)) := by
  have hr := tortoiseRadius_exterior (-L/2) (show -L/2<0 by linarith)
  have hn : (tortoiseRadius (-L/2):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  simp only [horizonCoordinate,radialUnit_inverse_radius,Complex.ofReal_sub,Complex.ofReal_one,
    Complex.ofReal_pow,Complex.ofReal_inv]
  generalize hR : (tortoiseRadius (-L/2):ℂ)=R at hn ⊢
  field_simp [hn]

/-- Exact compact metric period in the original collar; the horizon factor cancels the
extra metric radius factors before any limiting argument. -/
theorem original_metric_collar_period (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (L a b : ℝ) (hL : 0<L) :
    ((tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)*
        restoredMetricTime q br true amp w a b (tortoiseRadius (-L/2))=
      mu q*reader w (physicalRadialFrequency q) L*
        ((mu q-2)*(Complex.exp (-w*(b:ℂ))*scalar q br amp L b-
          Complex.exp (-w*(a:ℂ))*scalar q br amp L a+
          2*w*(∫ p in a..b,Complex.exp (-w*(p:ℂ))*scalar q br amp L p))+
        w*physicalSelfSourceCoefficient q*collarProfile q br amp L*
          ∫ p in a..b,Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p) := by
  have hx : -L/2<0 := by linarith
  have hr := tortoiseRadius_exterior (-L/2) hx
  have hn : (tortoiseRadius (-L/2):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hf : (tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1≠0 := by
    exact_mod_cast (show (tortoiseRadius (-L/2))^(2 : ℕ)-1≠0 by nlinarith)
  have hs (p : ℝ) : originalRadialPeriod q br amp p (p-2*(-L/2))=scalar q br amp L p := by
    rw [show p-2*(-L/2)=p+L by ring]
    rfl
  simp only [restoredMetricTime,readerCoefficient,D4BMPhysicalModeAction.radiusLift,
    tortoise_original_inverse (-L/2) hx,sourcePrefactor,forcingPrefactor,hs,coordinate_factor L hL]
  unfold reader collarProfile
  dsimp only [D4BMLeftModeRadialEquation.eigenvalue,modeProfile]
  generalize hR : (tortoiseRadius (-L/2):ℂ)=R at hn hf ⊢
  field_simp [hn,hf]

/-- The complete original metric angular finite part, in the true collar coordinate. -/
theorem original_metric_collar_finitePart (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (L a b : ℝ) (hL : 0<L) (ha : 0<a) (hab : a≤b) :
    Tendsto (fun k : ℝ => ((tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)*
      metricTimeCut q br true amp w a b (tortoiseRadius (-L/2)) (Real.exp k)) atTop
      (𝓝 (mu q*reader w (physicalRadialFrequency q) L*
        ((mu q-2)*(Complex.exp (-w*(b:ℂ))*scalar q br amp L b-
          Complex.exp (-w*(a:ℂ))*scalar q br amp L a+
          2*w*(∫ p in a..b,Complex.exp (-w*(p:ℂ))*scalar q br amp L p))+
        w*physicalSelfSourceCoefficient q*collarProfile q br amp L*
          ∫ p in a..b,Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p))) := by
  have h := (original_metric_time_finitePart q br true amp w hw a b (tortoiseRadius (-L/2)) ha hab
    (tortoiseRadius_exterior (-L/2) (by linarith))).const_mul ((tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)
  rwa [original_metric_collar_period q br amp w L a b hL] at h

private theorem unit_collar_limit :
    Tendsto (fun L : ℝ => radialUnit (-L/2)) atTop (𝓝 (1:ℝ)) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  have hform (L : ℝ) : radialUnit (-L/2)=(1-Real.exp (-L))/(1+Real.exp (-L)) := by
    apply (eq_div_iff (ne_of_gt (by positivity : 0<1+Real.exp (-L)))).mpr
    have h := radialUnit_one_sub (-L/2)
    rw [show 2*(-L/2) = -L by ring] at h
    nlinarith
  simp_rw [hform]
  convert! (tendsto_const_nhds.sub he).div (tendsto_const_nhds.add he)
    (by norm_num : (1:ℝ)+0≠0) using 1
  norm_num

private theorem profile_error (s amp J K : ℂ) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ L : ℝ in atTop,
      ‖forcingProfile s amp J K (radialUnit (-L/2))-forcingProfile s amp J K 1‖≤B*Real.exp (-L) := by
  have hp := ((power_derivatives (2*s) (by norm_num : 0<1+(1:ℝ))).1.scomp 1
    ((hasDerivAt_id (1:ℝ)).const_add 1)).differentiableAt
  have hd : DifferentiableAt ℝ (forcingProfile s amp J K) 1 := by unfold forcingProfile;fun_prop
  obtain ⟨B,hB,hb⟩ := hd.isBigO_sub.exists_pos
  refine ⟨2*B,by positivity,?_⟩
  filter_upwards [unit_collar_limit.eventually hb.bound,eventually_gt_atTop (0:ℝ)] with L h hL
  have hu := (radialUnit_bounds (-L/2) (by linarith)).2
  have he := radialUnit_one_sub (-L/2)
  rw [show 2*(-L/2) = -L by ring] at he
  have hn : ‖radialUnit (-L/2)-(1:ℝ)‖=1-radialUnit (-L/2) := by
    rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hu.le)]
    ring
  rw [hn,he] at h
  calc
    _ ≤ B*(Real.exp (-L)*(1+radialUnit (-L/2))) := h
    _ ≤ B*(Real.exp (-L)*2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _)) hB.le
    _ = _ := by ring

private theorem profile_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    Continuous (collarProfile q br amp) := by
  have hu : Continuous (fun L : ℝ => radialUnit (-L/2)) :=
    (continuous_iff_continuousAt.mpr (fun x => (radialUnit_hasDerivAt x).continuousAt)).comp
      (show Continuous (fun L : ℝ => -L/2) by fun_prop)
  have hp : Continuous (fun L : ℝ => power (2*physicalRate q br) (1+radialUnit (-L/2))) :=
    continuous_iff_continuousAt.mpr (fun L =>
      (power_derivatives (2*physicalRate q br) (radialUnit_add_one_pos (-L/2))).1.continuousAt.comp_of_eq
        (continuous_const.add hu).continuousAt rfl)
  unfold collarProfile forcingProfile
  fun_prop

private def forcingRadialRemainder (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (L : ℝ) : ℂ :=
  reader w (physicalRadialFrequency q) L*collarProfile q br amp L-
    readerTrace w (physicalRadialFrequency q)*forcingProfile (physicalRate q br) amp 1 (gradient q br) 1

private theorem forcing_radial_error (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0) :
    ∃ B : ℝ,0≤B ∧ ∀ᶠ L : ℝ in atTop,
      ‖forcingRadialRemainder q br amp w L‖≤B*(Real.exp (-L)+Real.exp (-w.re*L)) := by
  obtain ⟨B,hB,hb⟩ := normalizable_reader_collar_error w (physicalRadialFrequency q) hw
  obtain ⟨D,hD,hd⟩ := profile_error (physicalRate q br) amp 1 (gradient q br)
  let P := forcingProfile (physicalRate q br) amp 1 (gradient q br) 1
  let N := readerTrace w (physicalRadialFrequency q)
  let M := ‖P‖+D
  refine ⟨B*M+‖N‖*D,by dsimp [M];positivity,?_⟩
  filter_upwards [hb,hd,eventually_gt_atTop (0:ℝ)] with L hN hP hL
  change ‖reader w (physicalRadialFrequency q) L-N‖≤_ at hN
  change ‖collarProfile q br amp L-P‖≤_ at hP
  have he : Real.exp (-L)≤1 := by simpa using Real.exp_le_exp.mpr (show -L≤0 by linarith)
  have hp : ‖collarProfile q br amp L‖≤M := by
    have hn := norm_sub_norm_le (collarProfile q br amp L) P
    have h := hP.trans (mul_le_mul_of_nonneg_left he hD.le)
    dsimp only [M]
    linarith
  have heq : forcingRadialRemainder q br amp w L=
      (reader w (physicalRadialFrequency q) L-N)*collarProfile q br amp L+
        N*(collarProfile q br amp L-P) := by unfold forcingRadialRemainder;dsimp [P,N];ring
  rw [heq]
  calc
    _ ≤ ‖reader w (physicalRadialFrequency q) L-N‖*‖collarProfile q br amp L‖+
        ‖N‖*‖collarProfile q br amp L-P‖ := by simpa only [norm_mul] using (norm_add_le
          ((reader w (physicalRadialFrequency q) L-N)*collarProfile q br amp L)
          (N*(collarProfile q br amp L-P)))
    _ ≤ (B*(Real.exp (-L)+Real.exp (-w.re*L)))*M+‖N‖*(D*Real.exp (-L)) :=
      add_le_add (mul_le_mul hN hp (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left hP (norm_nonneg _))
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (norm_nonneg N) hD.le) (Real.exp_nonneg (-w.re*L))]

private theorem forcing_radial_continuousOn (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) : ContinuousOn (forcingRadialRemainder q br amp w) (Ioi 0) := by
  intro L hL
  change 0<L at hL
  have hx : -L/2<0 := by linarith
  have hv := ((modeProfile_smooth q w hw true).continuousOn.continuousAt
    (isOpen_Iio.mem_nhds hx)).comp_of_eq
    (show ContinuousAt (fun L : ℝ => -L/2) L by fun_prop) rfl
  have he : ContinuousAt (fun L : ℝ => Complex.exp (w*((-L/2:ℝ):ℂ))) L := by fun_prop
  exact (((he.mul hv).mul (profile_continuous q br amp).continuousAt).sub continuousAt_const).continuousWithinAt

/-- The projected forcing retains its exact radius dependence before the horizon limit. -/
def forcingPeriodRemainder (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (v : ℝ×ℝ) : ℂ :=
  forcingRadialRemainder q br amp w v.1*(Complex.exp (-w*(v.2:ℂ))*timeOnset (2*physicalRate q br) v.2)

private theorem forcing_period_remainder_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : 0<w.re) :
    ∃ L0 : ℝ,0<L0 ∧ IntegrableOn (forcingPeriodRemainder q br amp w) (Ioi L0 ×ˢ Ioi (0:ℝ)) := by
  obtain ⟨B,hB,hb⟩ := forcing_radial_error q br amp w hw
  obtain ⟨L1,hL1⟩ := eventually_atTop.mp hb
  let L0 := max L1 1
  have hL0 : 0<L0 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hm : AEStronglyMeasurable (forcingRadialRemainder q br amp w) (volume.restrict (Ioi L0)) :=
    ((forcing_radial_continuousOn q br amp w hw).mono
    (Ioi_subset_Ioi hL0.le)).aestronglyMeasurable measurableSet_Ioi
  have he1 := integrableOn_exp_mul_Ioi (a:=(-1:ℝ)) (by norm_num) L0
  have he2 := integrableOn_exp_mul_Ioi (a:=-w.re) (by linarith) L0
  have hmajor : IntegrableOn (fun L : ℝ => B*(Real.exp (-L)+Real.exp (-w.re*L))) (Ioi L0) := by
    simpa only [IntegrableOn,neg_one_mul,Pi.add_apply] using (he1.add he2).const_mul B
  have hR : IntegrableOn (forcingRadialRemainder q br amp w) (Ioi L0) := by
    apply hmajor.mono' hm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
    exact hL1 L ((le_max_left _ _).trans hL.le)
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re< -2 at hs
  have hT := timeOnset_integrable (2*physicalRate q br) w (show (2*physicalRate q br).re<w.re by linarith)
  refine ⟨L0,hL0,?_⟩
  unfold forcingPeriodRemainder
  simpa only [IntegrableOn,Measure.prod_restrict,Measure.volume_eq_prod] using hR.mul_prod hT

/-- The entire restored metric collar current minus its actual horizon density. -/
def metricRemainder (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (v : ℝ×ℝ) : ℂ :=
  collarDensity q br amp w v-leadingDensity q br amp w v.2

private theorem metric_remainder_split (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (v : ℝ×ℝ) :
    metricRemainder q br amp w v=mu q*(mu q-2)*D4BMOriginalCornerCurrentAdmission.sourceRemainder q br amp w v+
      mu q*w*physicalSelfSourceCoefficient q*forcingPeriodRemainder q br amp w v := by
  unfold metricRemainder collarDensity leadingDensity D4BMOriginalCornerCurrentAdmission.sourceRemainder
    forcingPeriodRemainder forcingRadialRemainder forcingTrace collarProfile
  ring

/-- Both retained metric slots have one admitted product remainder on the original collar. -/
theorem original_metric_remainder_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : (D4BMOriginalCirclePeriod.readerExponent q).re<w.re) :
    ∃ L0 : ℝ,0<L0 ∧ IntegrableOn (metricRemainder q br amp w) (Ioi L0 ×ˢ Ioi (0:ℝ)) := by
  have hq := (xi_divisor_support_re_mem_open_unit q.1).2
  have hwr0 : 0<w.re := by
    norm_num [D4BMOriginalCirclePeriod.readerExponent] at hwr
    linarith
  obtain ⟨L1,hL1,hS⟩ := original_source_remainder_integrable q br amp w hw hwr
  obtain ⟨L2,hL2,hF⟩ := forcing_period_remainder_integrable q br amp w hw hwr0
  let L0 := max L1 L2
  have hS' := hS.mono_set (Set.prod_mono (Ioi_subset_Ioi (le_max_left L1 L2)) Subset.rfl)
  have hF' := hF.mono_set (Set.prod_mono (Ioi_subset_Ioi (le_max_right L1 L2)) Subset.rfl)
  refine ⟨L0,hL1.trans_le (le_max_left _ _),?_⟩
  have h := (hS'.const_mul (mu q*(mu q-2))).add (hF'.const_mul (mu q*w*physicalSelfSourceCoefficient q))
  apply h.congr
  exact ae_of_all _ (fun v => (metric_remainder_split q br amp w v).symm)

private theorem null_density_continuous (nu s amp : ℂ) :
    Continuous (fun z : ℝ×ℝ => nullDensity nu s amp z.1 z.2) := by
  have h1 := (D4BMJointSource.timeReducedCoefficient_joint_continuous s amp).comp
    (show Continuous (fun z : ℝ×ℝ => ((z.1+z.2)/2,min ((z.1-z.2)/2) 0)) by fun_prop)
  have h2 := (D4BMJointSource.timeReducedCoefficient_joint_continuous s amp).comp
    (show Continuous (fun z : ℝ×ℝ => ((z.1+z.2)/2,min (-((z.1-z.2)/2)) 0)) by fun_prop)
  have hV := (D4BMNativeResponse.radialResponse_continuous nu s amp).comp
    (show Continuous (fun z : ℝ×ℝ => ((z.1+z.2)/2,(z.1-z.2)/2)) by fun_prop)
  have hv : Continuous (fun z : ℝ×ℝ => nu*(nu+1)/(4*(Real.cosh ((z.1-z.2)/2):ℂ)^(2 : ℕ))) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro z
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'))
  exact (continuous_const.mul (h1.sub h2)).add (hv.mul hV)

private theorem scalar_slope_continuousOn (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (L : ℝ) (hL : 0<L) : ContinuousOn (deriv (scalar q br amp L)) (Ioi 0) := by
  let nu := -D4BMOriginalCirclePeriod.readerExponent q
  let s := physicalRate q br
  have hd := null_density_continuous nu s amp
  have h1 : Continuous (fun p : ℝ => nullFirst nu s amp p (p+L)) := by
    change Continuous (fun p : ℝ => ∫ b in (0:ℝ)..(p+L),nullDensity nu s amp p b)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ:=volume) (a₀:=0)
      (f:=fun p : ℝ => fun b => nullDensity nu s amp p b) hd
      (show Continuous (fun p : ℝ => p+L) by fun_prop)
  have h2 : Continuous (fun p : ℝ => nullSecond nu s amp p (p+L)) := by
    change Continuous (fun p : ℝ => ∫ a in (0:ℝ)..p,nullDensity nu s amp a (p+L))
    have hc : Continuous (fun v : ℝ×ℝ => nullDensity nu s amp v.2 (v.1+L)) :=
      Continuous.comp (f:=fun v : ℝ×ℝ => (v.2,v.1+L))
        (g:=fun z : ℝ×ℝ => nullDensity nu s amp z.1 z.2) hd (by fun_prop)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ:=volume) (a₀:=0)
      (f:=fun p : ℝ => fun a => nullDensity nu s amp a (p+L)) hc continuous_id
  have ho : Continuous (timeOnsetFirst (2*s)) :=
    continuous_iff_continuousAt.mpr (fun p => (timeOnsetFirst_hasDerivAt (2*s) p).continuousAt)
  have hc := ((h1.add h2).add (ho.const_mul (liftCoefficient s amp L))).const_mul (physicalSelfSourceCoefficient q)
  apply hc.continuousOn.congr
  intro p hp
  exact (original_collar_hasDerivAt q br amp hL hp).deriv

private theorem scalar_continuousOn (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (L : ℝ) (hL : 0<L) : ContinuousOn (scalar q br amp L) (Ioi 0) :=
  fun _ hp => (original_collar_hasDerivAt q br amp hL hp).continuousAt.continuousWithinAt

private theorem compact_admission {f : ℝ→ℂ} (hf : ContinuousOn f (Ioi 0))
    (a b : ℝ) (ha : 0<a) (hab : a≤b) : IntervalIntegrable f volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact hf.mono (fun p hp => ha.trans_le hp.1)

private theorem source_time_transfer (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (L a b : ℝ) (hL : 0<L) (ha : 0<a) (hab : a≤b) :
    (∫ p in a..b,Complex.exp (-w*(p:ℂ))*(deriv (scalar q br amp L) p+w*scalar q br amp L p))=
      Complex.exp (-w*(b:ℂ))*scalar q br amp L b-Complex.exp (-w*(a:ℂ))*scalar q br amp L a+
        2*w*(∫ p in a..b,Complex.exp (-w*(p:ℂ))*scalar q br amp L p) := by
  let e := fun p : ℝ => Complex.exp (-w*(p:ℂ))
  let m := scalar q br amp L
  have he : Continuous e := by dsimp [e];fun_prop
  have hS := compact_admission (he.continuousOn.mul (scalar_continuousOn q br amp L hL)) a b ha hab
  have hD := compact_admission (he.continuousOn.mul (scalar_slope_continuousOn q br amp L hL)) a b ha hab
  change IntervalIntegrable (fun p => e p*m p) volume a b at hS
  change IntervalIntegrable (fun p => e p*deriv m p) volume a b at hD
  have hint := hD.sub (hS.const_mul w)
  have hder (p : ℝ) (hp : p∈uIcc a b) :
      HasDerivAt (fun p => e p*m p) (e p*deriv m p-w*(e p*m p)) p := by
    have hp' : 0<p := ha.trans_le ((uIcc_of_le hab ▸ hp).1)
    have hE := (((Complex.ofRealCLM.hasDerivAt (x:=p)).const_mul (-w)).cexp)
    have hM := (original_collar_hasDerivAt q br amp hL hp').differentiableAt.hasDerivAt
    apply (hE.mul hM).congr_deriv
    change e p*(-w*1)*m p+e p*deriv m p=_
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  rw [intervalIntegral.integral_sub hD (hS.const_mul w),intervalIntegral.integral_const_mul] at hFTC
  have hpoint (p : ℝ) : e p*(deriv m p+w*m p)=e p*deriv m p+w*(e p*m p) := by ring
  change (∫ p in a..b,e p*(deriv m p+w*m p))=_
  simp_rw [hpoint]
  rw [intervalIntegral.integral_add hD (hS.const_mul w),intervalIntegral.integral_const_mul]
  linear_combination hFTC

/-- The density is identified by its exact compact time integral against the complete
original metric period, before the unbounded collar limits are taken. -/
theorem original_metric_collar_integral (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (L a b : ℝ) (hL : 0<L) (ha : 0<a) (hab : a≤b) :
    (∫ p in a..b,collarDensity q br amp w (L,p))=
      ((tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)*restoredMetricTime q br true amp w a b (tortoiseRadius (-L/2)) := by
  have he : Continuous (fun p : ℝ => Complex.exp (-w*(p:ℂ))) := by fun_prop
  have hc := compact_admission (he.continuousOn.mul
    ((scalar_slope_continuousOn q br amp L hL).add ((scalar_continuousOn q br amp L hL).const_mul w))) a b ha hab
  change IntervalIntegrable (fun p : ℝ => Complex.exp (-w*(p:ℂ))*
    (deriv (scalar q br amp L) p+w*scalar q br amp L p)) volume a b at hc
  have ho : Continuous (timeOnset (2*physicalRate q br)) :=
    continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt _ p).continuousAt)
  have hf : IntervalIntegrable (fun p : ℝ => Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p)
      volume a b := (he.mul ho).intervalIntegrable a b
  have hpoint (p : ℝ) : collarDensity q br amp w (L,p)=
      mu q*reader w (physicalRadialFrequency q) L*
        ((mu q-2)*(Complex.exp (-w*(p:ℂ))*(deriv (scalar q br amp L) p+w*scalar q br amp L p))+
          (w*physicalSelfSourceCoefficient q*collarProfile q br amp L)*
            (Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p)) := by unfold collarDensity;ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hc.const_mul _) (hf.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    source_time_transfer q br amp w L a b hL ha hab,original_metric_collar_period q br amp w L a b hL]

private theorem threshold_cut (A : ℝ→ℂ) (hA : IntegrableOn A (Ioi (0:ℝ)))
    (L0 M : ℝ) (b : ℝ→ℝ) (hb : Continuous b) (hbound : ∀ p : ℝ,0<p → b p≤M) :
    IntegrableOn (fun p : ℝ => ((max (b p-L0) 0:ℝ):ℂ)*A p) (Ioi 0) ∧
    (∫ v in Ioi L0 ×ˢ Ioi (0:ℝ),{v : ℝ×ℝ | v.1<b v.2}.indicator (fun v => A v.2) v)=
      ∫ p in Ioi (0:ℝ),((max (b p-L0) 0:ℝ):ℂ)*A p := by
  let S := {v : ℝ×ℝ | v.1<b v.2}
  have hS : MeasurableSet S := measurableSet_lt measurable_fst (hb.measurable.comp measurable_snd)
  have hbase : IntegrableOn (fun v : ℝ×ℝ => A v.2) (Ioo L0 M ×ˢ Ioi (0:ℝ)) := by
    have h1 : IntegrableOn (fun _ : ℝ => (1:ℂ)) (Ioo L0 M) := integrableOn_const (by simp [Real.volume_Ioo])
    simpa only [IntegrableOn,Measure.prod_restrict,Measure.volume_eq_prod,one_mul] using h1.mul_prod hA
  have hi : IntegrableOn (S.indicator (fun v : ℝ×ℝ => A v.2)) (Ioi L0 ×ˢ Ioi (0:ℝ)) := by
    apply (integrableOn_indicator_iff hS).mpr
    apply hbase.mono_set
    intro v hv
    exact ⟨⟨hv.2.1,hv.1.trans_le (hbound v.2 hv.2.2)⟩,hv.2.2⟩
  have hi' : Integrable (S.indicator (fun v : ℝ×ℝ => A v.2))
      ((volume.restrict (Ioi L0)).prod (volume.restrict (Ioi (0:ℝ)))) := by
    simpa only [IntegrableOn,Measure.prod_restrict,Measure.volume_eq_prod] using hi
  have hinner (p : ℝ) : (∫ L in Ioi L0,S.indicator (fun v : ℝ×ℝ => A v.2) (L,p))=
      ((max (b p-L0) 0:ℝ):ℂ)*A p := by
    change (∫ L in Ioi L0,(Iio (b p)).indicator (fun _ => A p) L)=_
    rw [setIntegral_indicator measurableSet_Iio]
    have hs : Ioi L0 ∩ Iio (b p)=Ioo L0 (b p) := rfl
    rw [hs,setIntegral_const,Real.volume_real_Ioo,Complex.real_smul]
  constructor
  · exact hi'.integral_prod_right.congr (ae_of_all _ hinner)
  · have hp := integral_prod_symm _ hi'
    rw [Measure.prod_restrict,← Measure.volume_eq_prod] at hp
    rw [hp]
    exact integral_congr_ae (ae_of_all _ hinner)

private theorem clock_cut_integrable (A : ℝ→ℂ) (hA : IntegrableOn A (Ioi (0:ℝ)))
    (L0 T : ℝ) (c : ℝ) (hc : 0≤c) :
    IntegrableOn ({v : ℝ×ℝ | c*v.2+v.1/2<T}.indicator (fun v => A v.2))
      (Ioi L0 ×ˢ Ioi (0:ℝ)) := by
  have hbase : IntegrableOn (fun v : ℝ×ℝ => A v.2) (Ioo L0 (2*T) ×ˢ Ioi (0:ℝ)) := by
    have h1 : IntegrableOn (fun _ : ℝ => (1:ℂ)) (Ioo L0 (2*T)) := integrableOn_const (by simp [Real.volume_Ioo])
    simpa only [IntegrableOn,Measure.prod_restrict,Measure.volume_eq_prod,one_mul] using h1.mul_prod hA
  apply (integrableOn_indicator_iff (measurableSet_lt (by fun_prop) measurable_const)).mpr
  apply hbase.mono_set
  intro v hv
  refine ⟨⟨hv.2.1,?_⟩,hv.2.2⟩
  have hp : 0<v.2 := hv.2.2
  have ht : c*v.2+v.1/2<T := hv.1
  nlinarith [mul_nonneg hc hp.le]

private theorem leading_cut_difference (A : ℝ→ℂ) (hA : IntegrableOn A (Ioi (0:ℝ)))
    (L0 T : ℝ) :
    (staticCut (fun v : ℝ×ℝ => A v.2) L0 T-radialCut (fun v : ℝ×ℝ => A v.2) L0 T)/2=
      ∫ p in Ioi (0:ℝ),(((max (2*(T-p)-L0) 0-max (2*T-L0) 0)/2:ℝ):ℂ)*A p := by
  have hs := threshold_cut A hA L0 (2*T) (fun p => 2*(T-p)) (by fun_prop)
    (fun p hp => by linarith)
  have hr := threshold_cut A hA L0 (2*T) (fun _ => 2*T) continuous_const (fun _ _ => le_rfl)
  have hss : {v : ℝ×ℝ | v.1<2*(T-v.2)}={v : ℝ×ℝ | v.2+v.1/2<T} := by
    ext v
    change (v.1<2*(T-v.2))↔(v.2+v.1/2<T)
    constructor <;> intro h <;> linarith
  have hrs : {v : ℝ×ℝ | v.1<2*T}={v : ℝ×ℝ | v.1/2<T} := by
    ext v
    change (v.1<2*T)↔(v.1/2<T)
    constructor <;> intro h <;> linarith
  have hstatic := hs.2
  have hradial := hr.2
  rw [hss] at hstatic
  rw [hrs] at hradial
  rw [staticCut,hstatic,radialCut,hradial,← integral_sub hs.1 hr.1,← integral_div]
  apply integral_congr_ae
  exact ae_of_all _ (fun p => by push_cast;ring)

private theorem leading_cut_difference_limit (A : ℝ→ℂ) (hA : IntegrableOn A (Ioi (0:ℝ)))
    (hM : IntegrableOn (fun p : ℝ => (p:ℂ)*A p) (Ioi 0)) (L0 : ℝ) :
    Tendsto (fun T => (staticCut (fun v : ℝ×ℝ => A v.2) L0 T-
      radialCut (fun v : ℝ×ℝ => A v.2) L0 T)/2) atTop
      (𝓝 (-(∫ p in Ioi (0:ℝ),(p:ℂ)*A p))) := by
  let d := fun T p : ℝ => (max (2*(T-p)-L0) 0-max (2*T-L0) 0)/2
  have hb (T p : ℝ) (hp : 0<p) : |d T p|≤p := by
    dsimp only [d]
    by_cases h0 : 0≤2*T-L0
    · by_cases h1 : 0≤2*(T-p)-L0
      · rw [max_eq_left h1,max_eq_left h0]
        have he : (2*(T-p)-L0-(2*T-L0))/2 = -p := by ring
        rw [he,abs_neg,abs_of_pos hp]
      · rw [max_eq_right (le_of_not_ge h1),max_eq_left h0,abs_of_nonpos (by linarith)]
        linarith
    · rw [max_eq_right (by linarith),max_eq_right (le_of_not_ge h0)]
      simpa using hp.le
  have hlim : Tendsto (fun T : ℝ => ∫ p in Ioi (0:ℝ),(d T p:ℂ)*A p) atTop
      (𝓝 (∫ p in Ioi (0:ℝ),-(p:ℂ)*A p)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun p : ℝ => ‖(p:ℂ)*A p‖)
    · exact Eventually.of_forall (fun T =>
        (show Continuous (fun p : ℝ => (d T p:ℂ)) by dsimp [d];fun_prop).aestronglyMeasurable.mul hA.aestronglyMeasurable)
    · exact Eventually.of_forall (fun T => by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
        change 0<p at hp
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
        exact mul_le_mul_of_nonneg_right (hb T p hp) (norm_nonneg _))
    · exact hM.norm
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
      change 0<p at hp
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (p+L0/2)] with T hT
      have hd : d T p= -p := by
        dsimp [d]
        rw [max_eq_left (by linarith),max_eq_left (by linarith)]
        ring
      rw [hd,Complex.ofReal_neg]
  simp only [neg_mul,integral_neg] at hlim
  simp_rw [leading_cut_difference A hA L0]
  exact hlim

private theorem remainder_cutoff_difference {f : ℝ×ℝ→ℂ} {L0 : ℝ}
    (hf : IntegrableOn f (Ioi L0 ×ˢ Ioi (0:ℝ))) :
    Tendsto (fun T => staticCut f L0 T-radialCut f L0 T) atTop (𝓝 (0:ℂ)) := by
  have h (clock : ℝ×ℝ→ℝ) (hc : Continuous clock) :
      Tendsto (fun T : ℝ => ∫ v in Ioi L0 ×ˢ Ioi (0:ℝ),
        {v : ℝ×ℝ | clock v<T}.indicator f v) atTop
        (𝓝 (∫ v in Ioi L0 ×ˢ Ioi (0:ℝ),f v)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun v => ‖f v‖)
    · exact Eventually.of_forall (fun T => hf.aestronglyMeasurable.indicator
        (measurableSet_lt hc.measurable measurable_const))
    · exact Eventually.of_forall (fun _ => ae_of_all _ (fun v => norm_indicator_le_norm_self f v))
    · exact hf.norm
    · exact ae_of_all _ (fun v => tendsto_const_nhds.congr' (by
        filter_upwards [eventually_gt_atTop (clock v)] with T hT
        exact (Set.indicator_of_mem (show v∈{u : ℝ×ℝ | clock u<T} from hT) f).symm))
  simpa only [staticCut,radialCut,sub_self] using
    (h (fun v => v.2+v.1/2) (by fun_prop)).sub (h (fun v => v.1/2) (by fun_prop))

/-- The original radial Jacobian in collar length, including its factor one-half. -/
theorem original_collar_jacobian (L : ℝ) (hL : 0<L) :
    HasDerivAt (fun L : ℝ => tortoiseRadius (-L/2))
      (-((tortoiseRadius (-L/2))^(2 : ℕ)-1)/2) L := by
  apply ((tortoiseRadius_hasDerivAt (-L/2) (by linarith)).comp L
    ((hasDerivAt_id L).neg.div_const 2)).congr_deriv
  ring

private theorem metric_clock_split (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (L0 T c : ℝ) (hc : 0≤c)
    (hf : IntegrableOn (metricRemainder q br amp w) (Ioi L0 ×ˢ Ioi (0:ℝ)))
    (hA : IntegrableOn (leadingDensity q br amp w) (Ioi (0:ℝ))) :
    (∫ v in Ioi L0 ×ˢ Ioi (0:ℝ),{v : ℝ×ℝ | c*v.2+v.1/2<T}.indicator (collarDensity q br amp w) v)=
      (∫ v in Ioi L0 ×ˢ Ioi (0:ℝ),{v : ℝ×ℝ | c*v.2+v.1/2<T}.indicator (metricRemainder q br amp w) v)+
      ∫ v in Ioi L0 ×ˢ Ioi (0:ℝ),{v : ℝ×ℝ | c*v.2+v.1/2<T}.indicator (fun v => leadingDensity q br amp w v.2) v := by
  have hm : MeasurableSet {v : ℝ×ℝ | c*v.2+v.1/2<T} := measurableSet_lt (by fun_prop) measurable_const
  have he : collarDensity q br amp w=metricRemainder q br amp w+
      (fun v => leadingDensity q br amp w v.2) := by
    funext v
    dsimp [metricRemainder]
    ring
  rw [he]
  simp only [Pi.add_def,Set.indicator_add]
  exact integral_add (hf.indicator hm) (clock_cut_integrable _ hA L0 T c hc)

/-- Difference of the original moving static-time and time-first radial collar cuts,
with their physical Jacobian and the original logarithmic subtraction. -/
def metricCutoffDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (L0 T : ℝ) : ℂ :=
  (staticCut (collarDensity q br amp w) L0 T-radialCut (collarDensity q br amp w) L0 T)/2-
    ((T+Real.log (horizonCoordinate (-T))/2:ℝ):ℂ)*
      ∫ p in Ioi (0:ℝ),leadingDensity q br amp w p

/-- The entire angular-restored metric collar has exactly the original temporal corner.
Both original current remainders are admitted on the unbounded time/horizon product;
they contribute no cutoff-order defect. The unchanged coordinate fixes the logarithmic term. -/
theorem original_metric_collar_cutoff_difference (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2<w.re) (hwi : w.im≠0) :
    ∃ L0 : ℝ,0<L0 ∧ IntegrableOn (metricRemainder q br amp w) (Ioi L0 ×ˢ Ioi (0:ℝ)) ∧
      Tendsto (metricCutoffDifference q br amp w L0) atTop
        (𝓝 (D4BMOriginalCornerForcing.physicalCornerCandidate q br amp w)) := by
  have hq := (xi_divisor_support_re_mem_open_unit q.1).1
  have hwr : (D4BMOriginalCirclePeriod.readerExponent q).re<w.re := by
    norm_num [D4BMOriginalCirclePeriod.readerExponent]
    linarith
  obtain ⟨L0,hL0,hf⟩ := original_metric_remainder_integrable q br amp w hwi hwr
  have hA : IntegrableOn (leadingDensity q br amp w) (Ioi (0:ℝ)) := by
    simpa only [pow_zero,one_mul] using leading_moment_integrable q br amp w 0 hwr
  have hM : IntegrableOn (fun p : ℝ => (p:ℂ)*leadingDensity q br amp w p) (Ioi 0) := by
    simpa only [pow_one] using leading_moment_integrable q br amp w 1 hwr
  have hstatic (T : ℝ) : staticCut (collarDensity q br amp w) L0 T=
      staticCut (metricRemainder q br amp w) L0 T+
        staticCut (fun v : ℝ×ℝ => leadingDensity q br amp w v.2) L0 T := by
    simpa only [staticCut,one_mul] using metric_clock_split q br amp w L0 T 1 (by norm_num) hf hA
  have hradial (T : ℝ) : radialCut (collarDensity q br amp w) L0 T=
      radialCut (metricRemainder q br amp w) L0 T+
        radialCut (fun v : ℝ×ℝ => leadingDensity q br amp w v.2) L0 T := by
    simpa only [radialCut,zero_mul,zero_add] using metric_clock_split q br amp w L0 T 0 (by norm_num) hf hA
  have hraw : Tendsto (fun T => (staticCut (collarDensity q br amp w) L0 T-
      radialCut (collarDensity q br amp w) L0 T)/2) atTop
      (𝓝 (-(∫ p in Ioi (0:ℝ),(p:ℂ)*leadingDensity q br amp w p))) := by
    have h := ((remainder_cutoff_difference hf).div_const (2:ℂ)).add
      (leading_cut_difference_limit _ hA hM L0)
    simp only [zero_div,zero_add] at h
    apply h.congr'
    filter_upwards [] with T
    rw [hstatic,hradial]
    ring
  have hshift := (Complex.continuous_ofReal.continuousAt.tendsto.comp original_radial_log_shift).mul_const
    (∫ p in Ioi (0:ℝ),leadingDensity q br amp w p)
  have h := hraw.sub hshift
  rw [original_corner_moment_eq_candidate q br amp w hw hwi] at h
  exact ⟨L0,hL0,hf,h⟩

/-- The complete original metric finite part is the time integral of the same collar
density used in the unbounded cutoff comparison. All original cusp counterterms remain. -/
theorem original_metric_current_finitePart (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (L a b : ℝ) (hL : 0<L) (ha : 0<a) (hab : a≤b) :
    Tendsto (fun k : ℝ => ((tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)*
      metricTimeCut q br true amp w a b (tortoiseRadius (-L/2)) (Real.exp k)) atTop
      (𝓝 (∫ p in a..b,collarDensity q br amp w (L,p))) := by
  have h := (original_metric_time_finitePart q br true amp w hw a b (tortoiseRadius (-L/2)) ha hab
    (tortoiseRadius_exterior (-L/2) (by linarith))).const_mul ((tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)
  rwa [← original_metric_collar_integral q br amp w L a b hL ha hab] at h

end
end RHTower.D4BMOriginalMetricCorner
