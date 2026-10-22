import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalMetricOuter
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalMetricCorner

/-! Independent original temporal endpoint removal after complete outer integration. -/
open Set Filter Topology MeasureTheory Complex
namespace RHTower.D4BMOriginalMetricOuterTime
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMModularCore D4BMLaplaceRadial
open D4BMJointWave D4BMIngoingCoordinates D4BMOriginalCausalAdmission
open D4BMOriginalCirclePeriod D4BMOriginalCharacteristicTransform D4BMOriginalHorizonTimeTrace
open D4BMOriginalCollarCurrentBounds D4BMOriginalMetricTimePeriod D4BMOriginalCornerForcing
open D4BMOriginalMetricTimeLimit D4BMOriginalMetricOuter
noncomputable section
set_option autoImplicit false

private abbrev mu (q : XiZeroCopy) := D4BMLeftModeRadialEquation.eigenvalue q
private def ray (q : XiZeroCopy) (br : Bool) (amp : ℂ) (x p : ℝ) : ℂ :=
  originalScalar q br amp p (p-2*x)

private theorem ray_eq (q : XiZeroCopy) (br : Bool) (amp : ℂ) (x p : ℝ) :
    ray q br amp x p=physicalSelfSourceCoefficient q*
      (collarValue (-readerExponent q) (physicalRate q br) amp (-2*x) p+
        radialLift (physicalRate q br) 0 amp 1 x*timeOnset (2*physicalRate q br) p) := by
  have h := original_scalar_on_collar q br amp (-2*x) p
  simpa only [ray,liftCoefficient,show p+(-2*x)=p-2*x by ring,
    show -(-2*x)/2=x by ring] using h

private theorem ray_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    Continuous (fun z : ℝ×ℝ => ray q br amp z.1 z.2) := by
  have hC : Continuous (fun z : ℝ×ℝ => collarValue (-readerExponent q) (physicalRate q br) amp (-2*z.1) z.2) := by
    have h := (D4BMNativeResponse.radialResponse_continuous (-readerExponent q) (physicalRate q br) amp).comp
      (show Continuous (fun z : ℝ×ℝ => ((z.2+(z.2+(-2*z.1)))/2,(z.2-(z.2+(-2*z.1)))/2)) by fun_prop)
    simpa only [Function.comp_def,collarValue,nullValue] using! h
  have hL : Continuous (radialLift (physicalRate q br) 0 amp 1) :=
    continuous_iff_continuousAt.mpr (fun x => (radialLift_hasDerivAt _ _ _ _ x).continuousAt)
  have hT : Continuous (timeOnset (2*physicalRate q br)) :=
    continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt _ p).continuousAt)
  simp_rw [ray_eq]
  exact (hC.add ((hL.comp continuous_fst).mul (hT.comp continuous_snd))).const_mul _

private theorem reader_range (q : XiZeroCopy) :
    0 ≤ (readerExponent q).re ∧ (readerExponent q).re<3/2 := by
  obtain ⟨ha,hb⟩ := xi_divisor_support_re_mem_open_unit q.1
  norm_num [readerExponent]
  constructor <;> linarith

/-- The complete original scalar has a time envelope uniform through the outer endpoint. -/
theorem original_outer_ray_growth (q : XiZeroCopy) (br : Bool) (amp : ℂ) (T : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Icc T (0:ℝ), ∀ p : ℝ, 0 ≤ p →
      ‖originalScalar q br amp p (p-2*x)‖ ≤ B*Real.exp ((readerExponent q).re*p) := by
  obtain ⟨D,hD,hV⟩ := physical_radialResponse_ingoing_growth q br amp (readerExponent q) (reader_range q).1
  have hL : Continuous (radialLift (physicalRate q br) 0 amp 1) :=
    continuous_iff_continuousAt.mpr (fun x => (radialLift_hasDerivAt _ _ _ _ x).continuousAt)
  obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (hL.continuousOn (s:=Icc T (0:ℝ)))
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  obtain ⟨A,hA,hT⟩ := timeOnset_pair_bound (2*physicalRate q br) 0 (by linarith)
  have hT' (p : ℝ) : ‖timeOnset (2*physicalRate q br) p‖ ≤ A := by
    have h := (le_add_of_nonneg_right (norm_nonneg (timeOnsetFirst (2*physicalRate q br) p))).trans (hT p)
    simpa using h
  refine ⟨‖physicalSelfSourceCoefficient q‖*(D+max K 0*A),by positivity,?_⟩
  intro x hx p hp
  have hv : ‖collarValue (-readerExponent q) (physicalRate q br) amp (-2*x) p‖ ≤ D*Real.exp ((readerExponent q).re*p) :=
    hV p (p+(-2*x)) hp (by linarith [hx.2])
  have hl : ‖radialLift (physicalRate q br) 0 amp 1 x*timeOnset (2*physicalRate q br) p‖ ≤ max K 0*A := by
    rw [norm_mul]
    exact mul_le_mul ((hK x hx).trans (le_max_left _ _)) (hT' p) (norm_nonneg _) (le_max_right _ _)
  have he : 1 ≤ Real.exp ((readerExponent q).re*p) := Real.one_le_exp (mul_nonneg (reader_range q).1 hp)
  change ‖ray q br amp x p‖ ≤ _
  rw [ray_eq,norm_mul]
  apply (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hv hl)) (norm_nonneg _)).trans
  have hke := mul_le_mul_of_nonneg_left he (mul_nonneg (le_max_right K 0) hA)
  nlinarith [norm_nonneg (physicalSelfSourceCoefficient q)]

private def dampedRay (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (x p : ℝ) : ℂ :=
  Complex.exp (-w*(p:ℂ))*ray q br amp x p
private def onset (q : XiZeroCopy) (br : Bool) (w : ℂ) (p : ℝ) : ℂ :=
  Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p
private def reader (q : XiZeroCopy) (w : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (w*(x:ℂ))*normalizable w (physicalRadialFrequency q) (horizonCoordinate x)
private def profile (q : XiZeroCopy) (br : Bool) (amp : ℂ) (x : ℝ) : ℂ :=
  forcingProfile (physicalRate q br) amp 1
    (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) (radialUnit x)

private theorem damped_continuous (q : XiZeroCopy) (br : Bool) (amp w : ℂ) :
    Continuous (fun z : ℝ×ℝ => dampedRay q br amp w z.1 z.2) := by
  exact (show Continuous (fun z : ℝ×ℝ => Complex.exp (-w*(z.2:ℂ))) by fun_prop).mul
    (ray_continuous q br amp)

private theorem profile_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    Continuous (profile q br amp) := by
  have hu : Continuous radialUnit :=
    continuous_iff_continuousAt.mpr (fun x => (radialUnit_hasDerivAt x).continuousAt)
  have hp : Continuous (fun x : ℝ => power (2*physicalRate q br) (1+radialUnit x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((power_derivatives (2*physicalRate q br) (radialUnit_add_one_pos x)).1.scomp x
      ((radialUnit_hasDerivAt x).const_add 1)).continuousAt
  unfold profile forcingProfile
  fun_prop

private theorem reader_continuousOn (q : XiZeroCopy) (w : ℂ) :
    ContinuousOn (reader q w) (Iio (0:ℝ)) := by
  intro x hx
  have hn := ((normalizable_derivatives_continued (w:=w) (chi:=physicalRadialFrequency q)
    (horizonCoordinate_interior x hx)).1.continuousAt).comp_of_eq
      (horizonCoordinate_hasDerivAt x).continuousAt rfl
  exact ((show Continuous (fun x : ℝ => Complex.exp (w*(x:ℂ))) by fun_prop).continuousAt.mul hn).continuousWithinAt

private theorem interval_bound {f : ℝ→ℂ} {B k a b : ℝ}
    (hB : 0 ≤ B) (hk : k<0) (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : ∀ p : ℝ, 0 ≤ p → ‖f p‖ ≤ B*Real.exp (k*p)) :
    ‖∫ p in a..b,f p‖ ≤ ∫ p in Ioi (0:ℝ),B*Real.exp (k*p) := by
  have hi : IntegrableOn (fun p : ℝ => B*Real.exp (k*p)) (Ioi (0:ℝ)) :=
    (integrableOn_exp_mul_Ioi hk (0:ℝ)).const_mul B
  rw [intervalIntegral.integral_of_le hab]
  apply (norm_integral_le_of_norm_le
    (hi.mono_set (fun p hp => ha.trans_lt hp.1)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with p hp
      exact hf p (ha.trans hp.1.le))).trans
  exact setIntegral_mono_set hi (.of_forall (fun p => mul_nonneg hB (Real.exp_nonneg _)))
    (.of_forall (fun p hp => ha.trans_lt hp.1))

/-- The original angular-restored temporal metric with the physical radial Jacobian. -/
def outerTimeDensity (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b x : ℝ) : ℂ :=
  ((tortoiseRadius x:ℂ)^(2 : ℕ)-1)*restoredMetricTime q br true amp w a b (tortoiseRadius x)

def outerTimeIntegral (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (T a b : ℝ) : ℂ :=
  ∫ x in Ioo T (0:ℝ),outerTimeDensity q br amp w a b x

private def timeKernel (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b x : ℝ) : ℂ :=
  mu q*reader q w x*((mu q-2)*(dampedRay q br amp w x b-dampedRay q br amp w x a+
    2*w*∫ p in a..b,dampedRay q br amp w x p)+
    (w*physicalSelfSourceCoefficient q)*profile q br amp x*∫ p in a..b,onset q br w p)

/-- Exact cancellation of the original radius factors retains both endpoints and forcing. -/
theorem outerTimeDensity_eq (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (a b : ℝ) {x : ℝ} (hx : x<0) :
    outerTimeDensity q br amp w a b x=timeKernel q br amp w a b x := by
  have hr : (tortoiseRadius x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by
    have h := tortoiseRadius_exterior x hx
    linarith)
  have hf : (tortoiseRadius x:ℂ)^(2 : ℕ)-1≠0 := by
    exact_mod_cast (show tortoiseRadius x^(2 : ℕ)-1≠0 by nlinarith [tortoiseRadius_exterior x hx])
  have hz : (horizonCoordinate x:ℂ)=((tortoiseRadius x:ℂ)^(2 : ℕ)-1)/(tortoiseRadius x:ℂ)^(2 : ℕ) := by
    apply (eq_div_iff (pow_ne_zero 2 hr)).mpr
    simpa only [mul_comm] using radius_sq_mul_horizonCoordinate x hx
  have hperiod (p r : ℝ) : D4BMOriginalCausalPeriod.originalRadialPeriod q br amp p r=
      originalScalar q br amp p r := rfl
  simp only [outerTimeDensity,restoredMetricTime,sourcePrefactor,forcingPrefactor,
    readerCoefficient,D4BMPhysicalModeAction.radiusLift,tortoise_original_inverse x hx,
    D4BMOriginalReaderEquation.modeProfile,tortoiseMode,radialMode,if_true,
    timeKernel,dampedRay,ray,reader,profile,onset,hperiod]
  rw [hz]
  field_simp [hf,hr]

private theorem kernel_measurable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (a b T : ℝ) (hab : a ≤ b) :
    AEStronglyMeasurable (timeKernel q br amp w a b) (volume.restrict (Ioo T (0:ℝ))) := by
  have hc := damped_continuous q br amp w
  have hI : StronglyMeasurable (fun x => ∫ p in a..b,dampedRay q br amp w x p) := by
    simp_rw [intervalIntegral.integral_of_le hab]
    exact hc.stronglyMeasurable.integral_prod_right'
  have hm : AEStronglyMeasurable (reader q w) (volume.restrict (Ioo T (0:ℝ))) :=
    ((reader_continuousOn q w).mono (fun _ hx => hx.2)).aestronglyMeasurable measurableSet_Ioo
  have hP := (profile_continuous q br amp).aestronglyMeasurable (μ:=volume.restrict (Ioo T (0:ℝ)))
  have hp (p : ℝ) : AEStronglyMeasurable (fun x => dampedRay q br amp w x p) (volume.restrict (Ioo T (0:ℝ))) :=
    (hc.comp (show Continuous (fun x : ℝ => (x,p)) by fun_prop)).aestronglyMeasurable
  exact (hm.const_mul (mu q)).mul (((hp b |>.sub (hp a) |>.add (hI.aestronglyMeasurable.const_mul (2*w))).const_mul (mu q-2)).add
    ((hP.const_mul (w*physicalSelfSourceCoefficient q)).mul_const _))

private theorem exp_damp_bound (w : ℂ) {u : ℂ} {B G p : ℝ}
    (h : ‖u‖ ≤ B*Real.exp (G*p)) :
    ‖Complex.exp (-w*(p:ℂ))*u‖ ≤ B*Real.exp ((G-w.re)*p) := by
  rw [norm_mul,Complex.norm_exp,show (-w*(p:ℂ)).re= -w.re*p by simp]
  calc
    _  ≤  Real.exp (-w.re*p)*(B*Real.exp (G*p)) := mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
    _ = _ := by rw [mul_left_comm,← Real.exp_add];congr 2;ring

private theorem kernel_bound (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2<w.re) {T : ℝ} (hT : T<0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → ∀ x ∈ Ioo T (0:ℝ),
      ‖timeKernel q br amp w a b x‖ ≤ B := by
  let k := (readerExponent q).re-w.re
  have hk : k<0 := sub_neg.mpr ((reader_range q).2.trans hw)
  obtain ⟨B,hB,hS⟩ := original_outer_ray_growth q br amp T
  have hS' (x : ℝ) (hx : x∈Ioo T (0:ℝ)) (p : ℝ) (hp : 0 ≤ p) :
      ‖dampedRay q br amp w x p‖ ≤ B*Real.exp (k*p) :=
    exp_damp_bound w (hS x ⟨hx.1.le,hx.2.le⟩ p hp)
  have hS0 (x : ℝ) (hx : x∈Ioo T (0:ℝ)) (p : ℝ) (hp : 0 ≤ p) :
      ‖dampedRay q br amp w x p‖ ≤ B :=
    (hS' x hx p hp).trans (mul_le_of_le_one_right hB (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hk.le hp)))
  let I := ∫ p in Ioi (0:ℝ),B*Real.exp (k*p)
  have hI : 0 ≤ I := integral_nonneg (fun p => mul_nonneg hB (Real.exp_nonneg _))
  have hSI (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (x : ℝ) (hx : x∈Ioo T (0:ℝ)) :
      ‖∫ p in a..b,dampedRay q br amp w x p‖ ≤ I :=
    interval_bound hB hk ha hab (hS' x hx)
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  obtain ⟨A,hA,hO⟩ := timeOnset_pair_bound (2*physicalRate q br) 0 (by linarith)
  have hO' (p : ℝ) : ‖timeOnset (2*physicalRate q br) p‖ ≤ A := by
    have h := (le_add_of_nonneg_right (norm_nonneg (timeOnsetFirst (2*physicalRate q br) p))).trans (hO p)
    simpa using h
  have hOn (p : ℝ) (_hp : 0 ≤ p) : ‖onset q br w p‖ ≤ A*Real.exp ((-w.re)*p) := by
    have h := exp_damp_bound (G:=0) (p:=p) w (by simpa using hO' p)
    simpa only [zero_sub,onset] using! h
  let J := ∫ p in Ioi (0:ℝ),A*Real.exp ((-w.re)*p)
  have hJ : 0 ≤ J := integral_nonneg (fun p => mul_nonneg hA (Real.exp_nonneg _))
  have hOI (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : ‖∫ p in a..b,onset q br w p‖ ≤ J :=
    interval_bound hA (by linarith) ha hab hOn
  obtain ⟨N,hN,hNb⟩ := tortoiseNormalizable_outer_uniform_bound w (physicalRadialFrequency q) hT
  have hreader (x : ℝ) (hx : x∈Ioo T (0:ℝ)) : ‖reader q w x‖ ≤ N := by
    have he : ‖Complex.exp (w*(x:ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      apply Real.exp_le_one_iff.mpr
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hx.2.le
    rw [reader,norm_mul]
    exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans (by
      simpa using hNb w (Metric.mem_ball_self (by norm_num)) x hx)
  obtain ⟨P,hP⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((profile_continuous q br amp).continuousOn (s:=Icc T (0:ℝ)))
  let C := ‖mu q‖*N*(‖mu q-2‖*(B+B+‖2*w‖*I)+‖w*physicalSelfSourceCoefficient q‖*max P 0*J)
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro a b ha hab x hx
  have h1 := hS0 x hx b (ha.trans hab)
  have h2 := hS0 x hx a ha
  have h3 := hSI a b ha hab x hx
  have h4 := hOI a b ha hab
  have h5 := (hP x ⟨hx.1.le,hx.2.le⟩).trans (le_max_left P 0)
  have hsum : ‖dampedRay q br amp w x b-dampedRay q br amp w x a+
      2*w*∫ p in a..b,dampedRay q br amp w x p‖ ≤ B+B+‖2*w‖*I := by
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    exact add_le_add ((norm_sub_le _ _).trans (add_le_add h1 h2))
      (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
  have hforce : ‖(w*physicalSelfSourceCoefficient q)*profile q br amp x*
      ∫ p in a..b,onset q br w p‖ ≤ ‖w*physicalSelfSourceCoefficient q‖*max P 0*J := by
    rw [norm_mul,norm_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h5 (norm_nonneg _)) h4 (norm_nonneg _) (by positivity)
  unfold timeKernel
  rw [norm_mul,norm_mul]
  apply mul_le_mul (mul_le_mul_of_nonneg_left (hreader x hx) (norm_nonneg _))
    ((norm_add_le _ _).trans (add_le_add ?_ hforce)) (norm_nonneg _) (by positivity)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hsum (norm_nonneg _)

/-- The original temporal metric density is admitted in the entire outer interval. -/
theorem original_outer_time_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2<w.re) {T a b : ℝ} (hT : T<0) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntegrableOn (outerTimeDensity q br amp w a b) (Ioo T (0:ℝ)) := by
  obtain ⟨B,_,hB⟩ := kernel_bound q br amp w hw hT
  have he : outerTimeDensity q br amp w a b =ᵐ[volume.restrict (Ioo T (0:ℝ))]
      timeKernel q br amp w a b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact outerTimeDensity_eq q br amp w a b hx.2
  apply Integrable.congr ?_ he.symm
  apply (integrable_const B).mono' (kernel_measurable q br amp w a b T hab)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simpa only [Real.norm_eq_abs,abs_of_nonneg (le_trans (norm_nonneg _) (hB a b ha hab x hx))] using hB a b ha hab x hx

/-- Independent removal of original onset and terminal cutoffs commutes with outer integration. -/
theorem original_outer_time_limit (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2<w.re) (hwi : w.im≠0) {T : ℝ} (hT : T<0) :
    Tendsto (fun ab : ℝ×ℝ => outerTimeIntegral q br amp w T ab.1 ab.2)
      ((𝓝[>] (0:ℝ))×ˢatTop) (𝓝 (outerIntegral q br amp T w)) := by
  obtain ⟨B,hB,hbound⟩ := kernel_bound q br amp w hw hT
  have habs : ∀ᶠ ab : ℝ×ℝ in ((𝓝[>] (0:ℝ))×ˢatTop), 0 ≤ ab.1 ∧ ab.1 ≤ ab.2 := by
    have ha : ∀ᶠ a : ℝ in 𝓝[>] (0:ℝ), a<1 := (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin,tendsto_fst.eventually ha,
      tendsto_snd.eventually (eventually_ge_atTop (1:ℝ))] with ab ha ha1 hb
    exact ⟨ha.le,ha1.le.trans hb⟩
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => B)
  · filter_upwards [habs] with ab hab
    exact (original_outer_time_integrable q br amp w hw hT hab.1 hab.2).aestronglyMeasurable
  · filter_upwards [habs] with ab hab
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [outerTimeDensity_eq q br amp w ab.1 ab.2 hx.2]
    exact hbound ab.1 ab.2 hab.1 hab.2 x hx
  · exact integrable_const B
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have h := (original_metric_time_limit q br true amp w hw hwi (tortoiseRadius_exterior x hx.2)).const_mul
      ((tortoiseRadius x:ℂ)^(2 : ℕ)-1)
    exact h.mono_left (Filter.prod_mono nhdsWithin_le_nhds le_rfl)

private theorem shifted_kernel_measurable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (b T : ℝ) : AEStronglyMeasurable (fun x => timeKernel q br amp w 0 (b+x) x)
      (volume.restrict (Ioo T (0:ℝ))) := by
  have hc := damped_continuous q br amp w
  have hI : Continuous (fun x : ℝ => ∫ p in (0:ℝ)..b+x,dampedRay q br amp w x p) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hc (by fun_prop)
  have hO : Continuous (onset q br w) :=
    (show Continuous (fun p : ℝ => Complex.exp (-w*(p:ℂ))) by fun_prop).mul
      (continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt _ p).continuousAt))
  have hOI : Continuous (fun x : ℝ => ∫ p in (0:ℝ)..b+x,onset q br w p) :=
    (intervalIntegral.continuous_primitive (μ:=volume) (fun a c => hO.intervalIntegrable a c) 0).comp (by fun_prop)
  have hB := hc.comp (show Continuous (fun x : ℝ => (x,b+x)) by fun_prop)
  have hA := hc.comp (show Continuous (fun x : ℝ => (x,0)) by fun_prop)
  have hV : Continuous (fun x : ℝ =>
      (mu q-2)*(dampedRay q br amp w x (b+x)-dampedRay q br amp w x 0+
        2*w*∫ p in (0:ℝ)..b+x,dampedRay q br amp w x p)+
      (w*physicalSelfSourceCoefficient q)*profile q br amp x*∫ p in (0:ℝ)..b+x,onset q br w p) :=
    ((hB.sub hA |>.add (hI.const_mul (2*w))).const_mul (mu q-2)).add
      (((profile_continuous q br amp).const_mul (w*physicalSelfSourceCoefficient q)).mul hOI)
  exact (((reader_continuousOn q w).const_mul (mu q)).mul hV.continuousOn |>.mono
    (fun _ (hx : _∈Ioo T (0:ℝ)) => hx.2)).aestronglyMeasurable measurableSet_Ioo

/-- Outer time cutoff expressed in the original static clock `t=p-x`. -/
def outerStaticTimeIntegral (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (T b : ℝ) : ℂ :=
  ∫ x in Ioo T (0:ℝ),outerTimeDensity q br amp w 0 (b+x) x

/-- The genuine static cutoff has the same integrated outer-frequency limit. -/
theorem original_outer_static_time_limit (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2<w.re) (hwi : w.im≠0) {T : ℝ} (hT : T<0) :
    Tendsto (outerStaticTimeIntegral q br amp w T) atTop (𝓝 (outerIntegral q br amp T w)) := by
  obtain ⟨B,hB,hbound⟩ := kernel_bound q br amp w hw hT
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => B)
  · filter_upwards [] with b
    apply (shifted_kernel_measurable q br amp w b T).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (outerTimeDensity_eq q br amp w 0 (b+x) hx.2).symm
  · filter_upwards [eventually_ge_atTop (-T)] with b hb
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [outerTimeDensity_eq q br amp w 0 (b+x) hx.2]
    exact hbound 0 (b+x) le_rfl (by linarith [hx.1]) x hx
  · exact integrable_const B
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have h := (original_metric_time_limit q br true amp w hw hwi (tortoiseRadius_exterior x hx.2)).const_mul
      ((tortoiseRadius x:ℂ)^(2 : ℕ)-1)
    have hc : Tendsto (fun b : ℝ => ((0:ℝ),b+x)) atTop ((𝓝 (0:ℝ))×ˢatTop) :=
      tendsto_const_nhds.prodMk (tendsto_atTop_add_const_right atTop x tendsto_id)
    have ht := h.comp hc
    simpa only [Function.comp_def,outerTimeDensity,outerDensity] using! ht

/-- The original static-minus-radial cutoff comparison on the complete exterior,
with the outer interval and horizon collar sharing the same interface. -/
def exteriorCutoffDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (L0 b : ℝ) : ℂ :=
  D4BMOriginalMetricCorner.metricCutoffDifference q br amp w L0 b+
    (outerStaticTimeIntegral q br amp w (-L0/2) b-outerIntegral q br amp (-L0/2) w)

/-- The bounded outer region contributes no cutoff-change term. The entire
angular-restored exterior therefore retains precisely the original temporal corner. -/
theorem original_exterior_cutoff_difference (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2<w.re) (hwi : w.im≠0) :
    ∃ L0 : ℝ, 0<L0 ∧ Tendsto (exteriorCutoffDifference q br amp w L0) atTop
      (𝓝 (physicalCornerCandidate q br amp w)) := by
  obtain ⟨L0,hL0,_,hC⟩ := D4BMOriginalMetricCorner.original_metric_collar_cutoff_difference q br amp w hw hwi
  have hO := (original_outer_static_time_limit q br amp w hw hwi (T:= -L0/2) (by linarith)).sub_const
    (outerIntegral q br amp (-L0/2) w)
  have h := hC.add hO
  exact ⟨L0,hL0,by simpa only [sub_self,add_zero,exteriorCutoffDifference] using! h⟩

end
end RHTower.D4BMOriginalMetricOuterTime
