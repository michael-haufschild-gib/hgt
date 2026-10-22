import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalMetricTimePeriod
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalCollarCurrentBounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Original scalar growth and independent temporal endpoint removal in the complete
angular-restored Einstein current at a fixed exterior radius. -/

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalMetricTimeLimit
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMModularCore D4BMLaplaceRadial
open D4BMOriginalCausalAdmission D4BMOriginalCausalPeriod D4BMOriginalCirclePeriod
open D4BMOriginalCharacteristicTransform D4BMOriginalHorizonTimeTrace
open D4BMOriginalCollarCurrentBounds D4BMOriginalMetricTimePeriod D4BMIngoingCoordinates
open D4BMOriginalCornerForcing
noncomputable section
set_option autoImplicit false

private def ray (q : XiZeroCopy) (br : Bool) (amp : ℂ) (L p : ℝ) : ℂ :=
  originalScalar q br amp p (p+L)

private theorem reader_positive (q : XiZeroCopy) : 0≤(readerExponent q).re := by
  have h := (xi_divisor_support_re_mem_open_unit q.1).2
  norm_num [readerExponent]
  linarith

private theorem reader_before (q : XiZeroCopy) (w : ℂ) (hw : 3/2<w.re) :
    (readerExponent q).re<w.re := by
  have h := (xi_divisor_support_re_mem_open_unit q.1).1
  norm_num [readerExponent]
  linarith

private theorem source_before (q : XiZeroCopy) (br : Bool) (w : ℂ) (hw : 3/2<w.re) :
    (2*physicalRate q br).re<w.re := by
  have h := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at h
  linarith

private theorem ray_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) (L : ℝ) :
    Continuous (ray q br amp L) := by
  have hV := (D4BMNativeResponse.radialResponse_continuous (-readerExponent q) (physicalRate q br) amp).comp
    (show Continuous (fun p : ℝ => ((p+(p+L))/2,(p-(p+L))/2)) by fun_prop)
  have hC : Continuous (collarValue (-readerExponent q) (physicalRate q br) amp L) := by
    change Continuous (fun p => D4BMNativeResponse.radialResponse (-readerExponent q) (physicalRate q br) amp ((p+(p+L))/2) ((p-(p+L))/2))
    exact hV
  have hT : Continuous (timeOnset (2*physicalRate q br)) :=
    continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt _ p).continuousAt)
  unfold ray
  simp_rw [original_scalar_on_collar]
  exact (hC.add (hT.const_mul (liftCoefficient (physicalRate q br) amp L))).const_mul
    (physicalSelfSourceCoefficient q)

private theorem ray_zero (q : XiZeroCopy) (br : Bool) (amp : ℂ) {L : ℝ} (hL : 0≤L) :
    ray q br amp L 0=0 := by
  rw [ray,original_scalar_on_collar,collarValue_zero _ _ _ hL,timeOnset_zero_of_nonpos _ (le_refl 0)]
  simp

/-- The complete original scalar has a genuine ingoing-time growth bound at every exterior ray. -/
theorem original_ray_growth (q : XiZeroCopy) (br : Bool) (amp : ℂ) {L : ℝ} (hL : 0≤L) :
    ∃ B : ℝ, 0≤B ∧ ∀ p : ℝ, 0≤p →
      ‖originalScalar q br amp p (p+L)‖≤B*Real.exp ((readerExponent q).re*p) := by
  obtain ⟨C,hC,hV⟩ := physical_radialResponse_ingoing_growth q br amp (readerExponent q) (reader_positive q)
  have hr := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hr
  obtain ⟨A,hA,hT⟩ := timeOnset_pair_bound (2*physicalRate q br) 0 (by linarith)
  have hT' (p : ℝ) : ‖timeOnset (2*physicalRate q br) p‖≤A := by
    have h := (le_add_of_nonneg_right (norm_nonneg (timeOnsetFirst (2*physicalRate q br) p))).trans (hT p)
    simpa using h
  let K := ‖liftCoefficient (physicalRate q br) amp L‖*A
  have hK : 0≤K := mul_nonneg (norm_nonneg _) hA
  refine ⟨‖physicalSelfSourceCoefficient q‖*(C+K),by positivity,?_⟩
  intro p hp
  have hvp : ‖collarValue (-readerExponent q) (physicalRate q br) amp L p‖≤C*Real.exp ((readerExponent q).re*p) := by
    exact hV p (p+L) hp (add_nonneg hp hL)
  have htp : ‖liftCoefficient (physicalRate q br) amp L*timeOnset (2*physicalRate q br) p‖≤K := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hT' p) (norm_nonneg _)
  have he : 1≤Real.exp ((readerExponent q).re*p) := Real.one_le_exp (mul_nonneg (reader_positive q) hp)
  rw [original_scalar_on_collar,norm_mul]
  apply (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hvp htp)) (norm_nonneg _)).trans
  have hke := mul_le_mul_of_nonneg_left he hK
  nlinarith [norm_nonneg (physicalSelfSourceCoefficient q)]

private def dampedRay (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (L p : ℝ) : ℂ :=
  Complex.exp (-w*(p:ℂ))*ray q br amp L p

private theorem damped_ray_bound (q : XiZeroCopy) (br : Bool) (amp w : ℂ) {L : ℝ} (hL : 0≤L) :
    ∃ B : ℝ, 0≤B ∧ ∀ p : ℝ, 0≤p →
      ‖dampedRay q br amp w L p‖≤B*Real.exp (((readerExponent q).re-w.re)*p) := by
  obtain ⟨B,hB,h⟩ := original_ray_growth q br amp hL
  refine ⟨B,hB,?_⟩
  intro p hp
  rw [dampedRay,norm_mul,Complex.norm_exp]
  have hre : (-w*(p:ℂ)).re = -w.re*p := by simp
  rw [hre]
  calc
    _ ≤ Real.exp (-w.re*p)*(B*Real.exp ((readerExponent q).re*p)) :=
      mul_le_mul_of_nonneg_left (h p hp) (Real.exp_pos _).le
    _ = _ := by rw [mul_left_comm,← Real.exp_add];congr 2;ring

private theorem damped_ray_continuous (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (L : ℝ) :
    Continuous (dampedRay q br amp w L) := by
  exact (show Continuous (fun p : ℝ => Complex.exp (-w*(p:ℂ))) by fun_prop).mul (ray_continuous q br amp L)

/-- Both endpoint limits belong to the unchanged original scalar ray, including its onset lift. -/
theorem original_ray_endpoints (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2<w.re) {L : ℝ} (hL : 0≤L) :
    Tendsto (fun p : ℝ => Complex.exp (-w*(p:ℂ))*originalScalar q br amp p (p+L)) (𝓝 0) (𝓝 0) ∧
    Tendsto (fun p : ℝ => Complex.exp (-w*(p:ℂ))*originalScalar q br amp p (p+L)) atTop (𝓝 0) := by
  have hz : dampedRay q br amp w L 0=0 := by simp [dampedRay,ray_zero q br amp hL]
  have hzero := (damped_ray_continuous q br amp w L).tendsto 0
  rw [hz] at hzero
  refine ⟨hzero,?_⟩
  obtain ⟨B,hB,h⟩ := damped_ray_bound q br amp w hL
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall (fun p => norm_nonneg (dampedRay q br amp w L p)))
    (by filter_upwards [eventually_ge_atTop (0:ℝ)] with p hp;exact h p hp)
  have he := tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr (reader_before q w hw))
  simpa using (Real.tendsto_exp_atBot.comp he).const_mul B

private theorem damped_ray_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2<w.re) {L : ℝ} (hL : 0≤L) :
    IntegrableOn (dampedRay q br amp w L) (Ioi (0:ℝ)) := by
  obtain ⟨B,hB,h⟩ := damped_ray_bound q br amp w hL
  have hi := (integrableOn_exp_mul_Ioi (sub_neg.mpr (reader_before q w hw)) (0:ℝ)).const_mul B
  apply hi.mono' (damped_ray_continuous q br amp w L).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  exact h p hp.le

private theorem interval_joint_limit {f : ℝ→ℂ} (hf : Continuous f) (hi : IntegrableOn f (Ioi (0:ℝ))) :
    Tendsto (fun ab : ℝ×ℝ => ∫ p in ab.1..ab.2,f p) ((𝓝 0)×ˢatTop)
      (𝓝 (∫ p in Ioi (0:ℝ),f p)) := by
  have hupper := intervalIntegral_tendsto_integral_Ioi (0:ℝ) hi (tendsto_snd : Tendsto (fun ab : ℝ×ℝ => ab.2) ((𝓝 0)×ˢatTop) atTop)
  have hlower := (intervalIntegral.continuous_primitive (μ:=volume) (fun a b => hf.intervalIntegrable a b) 0).tendsto 0 |>.comp
    (tendsto_fst : Tendsto (fun ab : ℝ×ℝ => ab.1) ((𝓝 0)×ˢatTop) (𝓝 0))
  have h := hupper.sub hlower
  simp only [intervalIntegral.integral_same,sub_zero] at h
  apply h.congr'
  filter_upwards with ab
  have he := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hf.intervalIntegrable 0 ab.1) (hf.intervalIntegrable ab.1 ab.2)
  exact (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using he)).symm

/-- The complete original scalar frequency coefficient, with the retained onset lift. -/
def scalarFrequency (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (x : ℝ) : ℂ :=
  physicalSelfSourceCoefficient q*(continuedReducedGreen w (physicalRadialFrequency q) (physicalRate q br) amp 1 x+
    radialLift (physicalRate q br) w amp (continuedOnset (physicalRate q br) w) x)

private theorem ray_causal (q : XiZeroCopy) (br : Bool) (amp : ℂ) {x p : ℝ}
    (hx : x<0) (hp : p<0) : ray q br amp (-2*x) p=0 := by
  have hz := D4BMNativeResponse.radialResponse_zero_outside (-readerExponent q) (physicalRate q br) amp
    ((p+(p+(-2*x)))/2) ((p-(p+(-2*x)))/2) (by
      rw [show (p-(p+(-2*x)))/2=x by ring,abs_of_neg hx]
      exact max_lt (by linarith) (by linarith))
  simp only [ray,originalScalar,nullValue,hz,D4BMOriginalCausalPotential.nullLift,
    timeOnset_zero_of_nonpos (2*physicalRate q br) hp.le,mul_zero,add_zero]

/-- The original ingoing ray has precisely the static Green normalization dictated by its clock. -/
theorem original_ray_laplace (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2<w.re) (hwi : w.im≠0) {x : ℝ} (hx : x<0) :
    (∫ p in Ioi (0:ℝ),Complex.exp (-w*(p:ℂ))*originalScalar q br amp p (p-2*x))=
      Complex.exp (-w*(x:ℂ))*scalarFrequency q br amp w x := by
  let f := ray q br amp (-2*x)
  have hd := causal_laplace_delay f (fun p hp => ray_causal q br amp hx hp) w x hx.le
  have he (t : ℝ) : f (t+x)=originalScalar q br amp (t+x) (t-x) := by
    dsimp only [f,ray]
    congr 1
    ring
  simp_rw [he] at hd
  rw [original_scalar_timeIntegral_eq_green q br amp w hw hwi hx] at hd
  change scalarFrequency q br amp w x = Complex.exp (w*(x:ℂ))*
    (∫ t in Ioi (0:ℝ),Complex.exp (-w*(t:ℂ))*f t) at hd
  have hcancel : Complex.exp (-w*(x:ℂ))*Complex.exp (w*(x:ℂ))=1 := by
    rw [← Complex.exp_add]
    ring_nf
    exact Complex.exp_zero
  have h := congrArg (fun z : ℂ => Complex.exp (-w*(x:ℂ))*z) hd
  rw [← mul_assoc,hcancel,one_mul] at h
  simpa only [f,ray,sub_eq_add_neg,neg_mul] using h.symm

/-- The complete original forcing in static-frequency variables. -/
def forcingFrequency (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (x : ℝ) : ℂ :=
  physicalSelfSourceCoefficient q*(horizonCoordinate x:ℂ)*Complex.exp (w*(x:ℂ))*
    forcingProfile (physicalRate q br) amp 1
      (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) (radialUnit x)*
    onsetTransform (2*physicalRate q br) w

/-- The source-retaining temporal metric density with its derived angular normalization. -/
def metricFrequencyDensity (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (R : ℝ) : ℂ :=
  let mu := D4BMLeftModeRadialEquation.eigenvalue q;
  let x := tortoise R;
  let g := D4BMOriginalReaderEquation.modeProfile q w outer x;
  -mu * ((-2 * w * (mu - 2) * scalarFrequency q br amp w x * g / ((R:ℂ)^(2 : ℕ) - 1)) -
    (w * (R:ℂ)^(2 : ℕ) * g * forcingFrequency q br amp w x / ((R:ℂ)^(2 : ℕ) - 1)^(2 : ℕ)))

/-- Independent onset and terminal-time removal in the angular-restored original metric.
The resulting density retains the complete forcing and scalar onset lift. -/
theorem original_metric_time_limit (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (hw : 3/2<w.re) (hwi : w.im≠0) {R : ℝ} (hR : 1<R) :
    Tendsto (fun ab : ℝ×ℝ => restoredMetricTime q br outer amp w ab.1 ab.2 R)
      ((𝓝 0)×ˢatTop) (𝓝 (metricFrequencyDensity q br outer amp w R)) := by
  let x := tortoise R
  let L := -2*x
  have hx : x<0 := by
    have h := Real.log_lt_log (show 0<R-1 by linarith) (show R-1<R+1 by linarith)
    dsimp [x,tortoise]
    linarith
  have hL : 0≤L := by dsimp only [L];linarith
  have hperiod (p : ℝ) : originalRadialPeriod q br amp p (p-2*x)=ray q br amp L p := by
    rw [show p-2*x=p+L by dsimp [L];ring]
    rfl
  have hS := interval_joint_limit (damped_ray_continuous q br amp w L) (damped_ray_integrable q br amp w hw hL)
  have hSint : (∫ p in Ioi (0:ℝ),dampedRay q br amp w L p)=Complex.exp (-w*(x:ℂ))*scalarFrequency q br amp w x := by
    simpa only [dampedRay,ray,L,sub_eq_add_neg,neg_mul] using original_ray_laplace q br amp w hw hwi hx
  rw [hSint] at hS
  have hTcont : Continuous (fun p : ℝ => Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p) := by
    apply Continuous.mul
    · fun_prop
    · exact continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt _ p).continuousAt)
  have hT := interval_joint_limit hTcont (timeOnset_integrable (2*physicalRate q br) w (source_before q br w hw))
  rw [timeOnset_laplace] at hT
  obtain ⟨ha,hb⟩ := original_ray_endpoints q br amp w hw hL
  have ha' := ha.comp (tendsto_fst : Tendsto (fun ab : ℝ×ℝ => ab.1) ((𝓝 0)×ˢatTop) (𝓝 0))
  have hb' := hb.comp (tendsto_snd : Tendsto (fun ab : ℝ×ℝ => ab.2) ((𝓝 0)×ˢatTop) atTop)
  let K := (R:ℂ)*readerCoefficient q w outer R
  let J := readerCoefficient q w outer R*(horizonCoordinate x:ℂ)*physicalSelfSourceCoefficient q*
    forcingProfile (physicalRate q br) amp 1
      (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) (radialUnit x)
  have ht := ((((hb'.const_mul K).sub (ha'.const_mul K)).add
    ((hS.const_mul K).const_mul (2*w))).const_mul (sourcePrefactor q R)).add
      ((hT.const_mul J).const_mul (forcingPrefactor q w R))
  have hlim : sourcePrefactor q R*(K*0-K*0+2*w*(K*(Complex.exp (-w*(x:ℂ))*scalarFrequency q br amp w x)))+
      forcingPrefactor q w R*(J*onsetTransform (2*physicalRate q br) w)=metricFrequencyDensity q br outer amp w R := by
    have hR0 : (R:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hf0 : (R:ℂ)^(2 : ℕ)-1≠0 := by exact_mod_cast (show R^(2 : ℕ)-1≠0 by nlinarith)
    have he : Complex.exp (w*(x:ℂ))*Complex.exp (-w*(x:ℂ))=1 := by
      rw [← Complex.exp_add]
      ring_nf
      exact Complex.exp_zero
    have hK : K*Complex.exp (-w*(x:ℂ))=(R:ℂ)^(2 : ℕ)*D4BMOriginalReaderEquation.modeProfile q w outer x := by
      unfold K readerCoefficient D4BMPhysicalModeAction.radiusLift
      calc
        _ = (R:ℂ)^(2 : ℕ)*D4BMOriginalReaderEquation.modeProfile q w outer x*
            (Complex.exp (w*(x:ℂ))*Complex.exp (-w*(x:ℂ))) := by ring
        _ = _ := by rw [he,mul_one]
    rw [show K*(Complex.exp (-w*(x:ℂ))*scalarFrequency q br amp w x)=
      ((R:ℂ)^(2 : ℕ)*D4BMOriginalReaderEquation.modeProfile q w outer x)*scalarFrequency q br amp w x by rw [← mul_assoc,hK]]
    simp only [J,readerCoefficient,sourcePrefactor,forcingPrefactor,metricFrequencyDensity,
      forcingFrequency,D4BMPhysicalModeAction.radiusLift,mul_zero,sub_self,zero_add]
    dsimp only [x]
    field_simp [hR0,hf0]
    ring
  rw [hlim] at ht
  convert! ht using 1
  funext ab
  simp only [restoredMetricTime,hperiod,K,J,dampedRay,ray,x,Function.comp_apply]
  ring

end
end RHTower.D4BMOriginalMetricTimeLimit
