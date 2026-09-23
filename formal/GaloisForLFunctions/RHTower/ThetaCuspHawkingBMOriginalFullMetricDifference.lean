import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCanonicalRestoration
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalForcingJointHorizon
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalSourceTailCollar

open Set Filter Topology MeasureTheory Complex
namespace RHTower.D4BMOriginalFullMetricDifference
open D4BMJointSource D4BMJointWave D4BMModularCore D4BMLaplaceRadial D4BMIngoingCoordinates
open D4BMOriginalMetricTimePeriod D4BMOriginalCausalPeriod D4BMOriginalCausalPotential
open D4BMOriginalCornerForcing D4BMOriginalForcingAngularPeriod
open D4BMOriginalCompleteTransfer D4BMOriginalSourceTailCollar D4BMOriginalReaderCuspBounds
noncomputable section
set_option autoImplicit false

private abbrev mu (q : XiZeroCopy) := D4BMLeftModeRadialEquation.eigenvalue q
private abbrev grad (q : XiZeroCopy) (br : Bool) :=
  reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1

/-- The restored source slice already present in the complete original metric time value. -/
def sourceRestoredSlice (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (p R : ℝ) : ℂ :=
  (R:ℂ)*D4BMOriginalMetricTimePeriod.readerCoefficient q w outer R*Complex.exp (-w*(p:ℂ))*
    originalRadialPeriod q br amp p (p-2*tortoise R)

/-- The restored forcing slice, with its original angular coefficient and actual source onset. -/
def forcingRestoredSlice (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (p R : ℝ) : ℂ :=
  D4BMOriginalMetricTimePeriod.readerCoefficient q w outer R*(horizonCoordinate (tortoise R):ℂ)*
    physicalSelfSourceCoefficient q*forcingProfile (physicalRate q br) amp 1 (grad q br) (radialUnit (tortoise R))*
    (Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p)

def sourcePeriodDifference (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (p R Y : ℝ) : ℂ :=
  sourcePeriodCut q br outer amp w p R Y-sourceRestoredSlice q br outer amp w p R

def forcingPeriodDifference (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (p R Y : ℝ) : ℂ :=
  forcingPeriodCut q br outer amp w p R Y-forcingRestoredSlice q br outer amp w p R

private theorem radial_period_time_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) (R : ℝ) :
    Continuous (fun p => originalRadialPeriod q br amp p (p-2*tortoise R)) := by
  have hA := (D4BMNativeResponse.radialResponse_continuous
    (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q br) amp).comp
      (show Continuous (fun p : ℝ => ((p+(p-2*tortoise R))/2,(p-(p-2*tortoise R))/2)) by fun_prop)
  have hL : Continuous (radialLift (physicalRate q br) 0 amp 1) :=
    continuous_iff_continuousAt.mpr (fun x => (radialLift_hasDerivAt _ _ _ _ x).continuousAt)
  have hO : Continuous (timeOnset (2*physicalRate q br)) :=
    continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt _ p).continuousAt)
  have hB := (hL.comp (show Continuous (fun p : ℝ => (p-(p-2*tortoise R))/2) by fun_prop)).mul hO
  exact (hA.add hB).const_mul (physicalSelfSourceCoefficient q)

private theorem source_restored_integrable (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (a b R : ℝ) :
    IntervalIntegrable (fun p => sourceRestoredSlice q br outer amp w p R) volume a b := by
  have h := ((show Continuous (fun p : ℝ => Complex.exp (-w*(p:ℂ))) by fun_prop).const_mul
    ((R:ℂ)*D4BMOriginalMetricTimePeriod.readerCoefficient q w outer R)).mul
      (radial_period_time_continuous q br amp R)
  exact h.intervalIntegrable a b

private theorem forcing_restored_integrable (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (a b R : ℝ) :
    IntervalIntegrable (fun p => forcingRestoredSlice q br outer amp w p R) volume a b := by
  have hO : Continuous (timeOnset (2*physicalRate q br)) :=
    continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt _ p).continuousAt)
  exact (((show Continuous (fun p : ℝ => Complex.exp (-w*(p:ℂ))) by fun_prop).mul hO).const_mul _).intervalIntegrable a b

private theorem restored_metric_slices (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (a b R : ℝ) :
    restoredMetricTime q br outer amp w a b R=
      sourcePrefactor q R*(sourceRestoredSlice q br outer amp w b R-sourceRestoredSlice q br outer amp w a R+
        2*w*(∫ p in a..b,sourceRestoredSlice q br outer amp w p R))+
      forcingPrefactor q w R*(∫ p in a..b,forcingRestoredSlice q br outer amp w p R) := by
  simp only [sourceRestoredSlice,forcingRestoredSlice,restoredMetricTime]
  simp_rw [show ∀ p : ℝ,(R:ℂ)*D4BMOriginalMetricTimePeriod.readerCoefficient q w outer R*Complex.exp (-w*(p:ℂ))*
      originalRadialPeriod q br amp p (p-2*tortoise R)=
      ((R:ℂ)*D4BMOriginalMetricTimePeriod.readerCoefficient q w outer R)*
        (Complex.exp (-w*(p:ℂ))*originalRadialPeriod q br amp p (p-2*tortoise R)) from fun p => by ring]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]

/-- Exact discrepancy of the entire finite metric current. Each integral is
separately admitted before subtraction; both temporal endpoints remain. -/
theorem original_metric_time_difference (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (hY : 4≤Y) :
    metricTimeCut q br outer amp w a b R Y-restoredMetricTime q br outer amp w a b R=
      sourcePrefactor q R*(sourcePeriodDifference q br outer amp w b R Y-sourcePeriodDifference q br outer amp w a R Y+
        2*w*(∫ p in a..b,sourcePeriodDifference q br outer amp w p R Y))+
      forcingPrefactor q w R*(∫ p in a..b,forcingPeriodDifference q br outer amp w p R Y)+
      ((∫ p in a..b,boundarySlice q br outer amp w p R Y)-
        ∑ i : Fin 3,D4BMOriginalCompactBoundary.compactBoundaryCoefficient q q br outer amp w a b R i*
          Complex.exp (D4BMOriginalCuspFlux.fluxExponent q q i*(Real.log Y:ℂ))) := by
  rw [original_metric_time_cut_decomposition q br outer amp w hw a b R Y ha hab hr hY,
    restored_metric_slices]
  unfold sourcePeriodDifference forcingPeriodDifference
  rw [intervalIntegral.integral_sub
    (original_source_cut_time_integrable q br outer amp w a b R Y ha hab hr hY)
    (source_restored_integrable q br outer amp w a b R),
    intervalIntegral.integral_sub (original_forcing_cut_time_integrable q br outer amp w a b R Y)
    (forcing_restored_integrable q br outer amp w a b R)]
  ring

/-- The original forcing discrepancy in the radial measure after all metric radius factors cancel. -/
def forcingPeriodError (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (p L k : ℝ) : ℂ :=
  Complex.exp (-w*(p:ℂ))*D4BMOriginalReaderCuspBounds.reader q w L*timeOnset (2*physicalRate q br) p*
    (profileCut q br amp (radialUnit (-L/2)) (Real.exp k)-
      physicalSelfSourceCoefficient q*forcingProfile (physicalRate q br) amp 1 (grad q br) (radialUnit (-L/2)))

private theorem reader_coefficient_collar (q : XiZeroCopy) (w : ℂ) {L : ℝ} (hL : 0<L) :
    D4BMOriginalMetricTimePeriod.readerCoefficient q w true (tortoiseRadius (-L/2))=
      (tortoiseRadius (-L/2):ℂ)*D4BMOriginalReaderCuspBounds.reader q w L := by
  simp only [D4BMOriginalMetricTimePeriod.readerCoefficient,D4BMPhysicalModeAction.radiusLift,
    tortoise_original_inverse (-L/2) (by linarith),D4BMOriginalReaderEquation.modeProfile,
    D4BMOriginalReaderCuspBounds.reader]
  ring

/-- Literal source discrepancy has exactly its unchanged physical coefficient. -/
theorem original_source_difference_collar (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (p L k : ℝ) (hL : 0<L) :
    ((tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)*sourcePrefactor q (tortoiseRadius (-L/2))*
      sourcePeriodDifference q br true amp w p (tortoiseRadius (-L/2)) (Real.exp k)=
        mu q*(mu q-2)*originalPeriodError q br amp w p L k := by
  let R : ℂ := tortoiseRadius (-L/2)
  have hr : R≠0 := Complex.ofReal_ne_zero.mpr (by have h:=tortoiseRadius_exterior (-L/2) (by linarith : -L/2<0);linarith)
  have hf : R^(2 : ℕ)-1≠0 := by
    change (tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1≠0
    exact_mod_cast (show tortoiseRadius (-L/2)^(2 : ℕ)-1≠0 by nlinarith [tortoiseRadius_exterior (-L/2) (by linarith : -L/2<0)])
  rw [sourcePeriodDifference,original_source_period_cut,sourceRestoredSlice,reader_coefficient_collar q w hL,
    tortoise_original_inverse (-L/2) (by linarith : -L/2<0)]
  simp only [show p-2*(-L/2)=p+L by ring,sourcePrefactor,originalPeriodError]
  change (R^(2 : ℕ)-1)*(mu q*(mu q-2)/(R^(2 : ℕ)*(R^(2 : ℕ)-1)))*(_-_) = _
  dsimp only [R] at *
  simp only [neg_div] at hr hf ⊢
  field_simp [hr,hf]

/-- Literal forcing discrepancy has exactly its unchanged physical coefficient. -/
theorem original_forcing_difference_collar (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (p L k : ℝ) (hL : 0<L) :
    ((tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)*forcingPrefactor q w (tortoiseRadius (-L/2))*
      forcingPeriodDifference q br true amp w p (tortoiseRadius (-L/2)) (Real.exp k)=
        mu q*w*forcingPeriodError q br amp w p L k := by
  let R : ℂ := tortoiseRadius (-L/2)
  have hr : R≠0 := Complex.ofReal_ne_zero.mpr (by have h:=tortoiseRadius_exterior (-L/2) (by linarith : -L/2<0);linarith)
  have hf : R^(2 : ℕ)-1≠0 := by
    change (tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1≠0
    exact_mod_cast (show tortoiseRadius (-L/2)^(2 : ℕ)-1≠0 by nlinarith [tortoiseRadius_exterior (-L/2) (by linarith : -L/2<0)])
  have hz : (horizonCoordinate (-L/2):ℂ)=(R^(2 : ℕ)-1)/R^(2 : ℕ) := by
    apply (eq_div_iff (pow_ne_zero 2 hr)).mpr
    simpa only [R,mul_comm] using radius_sq_mul_horizonCoordinate (-L/2) (by linarith : -L/2<0)
  rw [forcingPeriodDifference,original_forcing_period_cut,forcingRestoredSlice,reader_coefficient_collar q w hL,
    tortoise_original_inverse (-L/2) (by linarith : -L/2<0),hz]
  unfold forcingPrefactor forcingPeriodError
  change (R^(2 : ℕ)-1)*(mu q*R*w/(R^(2 : ℕ)-1)^(2 : ℕ))*(_-_)=_
  dsimp only [R] at *
  simp only [neg_div] at hr hf ⊢
  field_simp [hr,hf]

/-- The entire physical metric difference, in its original radial measure,
is the sum of the actual scalar-period error, forcing-period error and full boundary. -/
theorem original_full_metric_difference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0)
    (a b L k : ℝ) (ha : 0<a) (hab : a≤b) (hL : 0<L) (hk : 4≤Real.exp k) :
    ((tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)*
      (metricTimeCut q br true amp w a b (tortoiseRadius (-L/2)) (Real.exp k)-
        restoredMetricTime q br true amp w a b (tortoiseRadius (-L/2)))=
      mu q*(mu q-2)*(originalPeriodError q br amp w b L k-originalPeriodError q br amp w a L k+
        2*w*(∫ p in a..b,originalPeriodError q br amp w p L k))+
      mu q*w*(∫ p in a..b,forcingPeriodError q br amp w p L k)+radialBoundary q br amp w a b L k := by
  let R := tortoiseRadius (-L/2)
  let f : ℂ := (R:ℂ)^(2 : ℕ)-1
  have hS := original_source_difference_collar q br amp w
  have hF := original_forcing_difference_collar q br amp w
  have hSI : f*sourcePrefactor q R*(∫ p in a..b,sourcePeriodDifference q br true amp w p R (Real.exp k))=
      mu q*(mu q-2)*(∫ p in a..b,originalPeriodError q br amp w p L k) := by
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro p _
    exact hS p L k hL
  have hFI : f*forcingPrefactor q w R*(∫ p in a..b,forcingPeriodDifference q br true amp w p R (Real.exp k))=
      mu q*w*(∫ p in a..b,forcingPeriodError q br amp w p L k) := by
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro p _
    exact hF p L k hL
  rw [original_metric_time_difference q br true amp w hw a b R (Real.exp k) ha hab
    (tortoiseRadius_exterior (-L/2) (by linarith)) hk,Real.log_exp]
  change f*(_+_+_)=_
  rw [mul_add,mul_add,← mul_assoc,← mul_assoc,hFI]
  have hboundary : f*((∫ p in a..b,boundarySlice q br true amp w p R (Real.exp k))-
      ∑ i : Fin 3,D4BMOriginalCompactBoundary.compactBoundaryCoefficient q q br true amp w a b R i*
        Complex.exp (D4BMOriginalCuspFlux.fluxExponent q q i*(k:ℂ)))=radialBoundary q br amp w a b L k := by
    dsimp only [boundarySlice,R,f]
    rw [complete_metric_boundary_products q br amp w hw a b L k ha hab hL]
    exact complete_boundary_radial_density q br amp w a b L k hL
  rw [hboundary]
  have hsa := hS a L k hL
  have hsb := hS b L k hL
  calc
    _ = (f*sourcePrefactor q R*sourcePeriodDifference q br true amp w b R (Real.exp k)-
        f*sourcePrefactor q R*sourcePeriodDifference q br true amp w a R (Real.exp k)+
        2*w*(f*sourcePrefactor q R*∫ p in a..b,sourcePeriodDifference q br true amp w p R (Real.exp k)))+
        mu q*w*(∫ p in a..b,forcingPeriodError q br amp w p L k)+radialBoundary q br amp w a b L k := by ring
    _ = _ := by rw [hsa,hsb,hSI];ring

/-- The forcing error in the complete metric identity is exactly the same
finite-height kernel discrepancy used by canonical joint restoration. -/
theorem original_forcing_error_kernel (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (p L k : ℝ) :
    forcingPeriodError q br amp w p L k=
      Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p*
        (D4BMOriginalForcingJointHorizon.kernelCut q br amp w (Real.exp k) (-L/2)-
          physicalSelfSourceCoefficient q*D4BMOriginalMetricHorizon.forcingKernel q br amp (grad q br) w (-L/2)) := by
  simp only [forcingPeriodError,D4BMOriginalForcingJointHorizon.kernelCut,
    D4BMOriginalMetricHorizon.forcingKernel,D4BMOriginalReaderCuspBounds.reader,tortoiseMode,radialMode,if_true]
  ring

end
end RHTower.D4BMOriginalFullMetricDifference


open Set Filter Topology MeasureTheory Complex Metric
namespace RHTower.D4BMOriginalCanonicalForcingMatch
open D4BMJointSource D4BMModularCore D4BMLaplaceRadial
open D4BMOriginalCornerForcing D4BMOriginalMetricHorizon D4BMOriginalCanonicalHorizon
open D4BMOriginalCanonicalRestoration D4BMOriginalForcingJointHorizon
noncomputable section
set_option autoImplicit false

private abbrev grad (q : XiZeroCopy) (br : Bool) :=
  reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1

def canonicalForcingCounterterm (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) (e : ℝ) : ℂ :=
  D4BMOriginalMetricRadial.forcingCounterterm
    (incomingValue q br amp K) (incomingSlope q br amp K) (oppositeValue q br amp K) w e

/-- The literal finite-height forcing discrepancy and its source-fixed horizon
counterterms. The angular weights remain at the same finite cutoff. -/
def canonicalForcingDifferenceCut (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (b : ℝ) (v : ℝ×ℝ) : ℂ :=
  (∫ x in tortoiseOf v.1..tortoiseOf b,kernelCut q br amp w (Real.exp v.2) x)-
    physicalSelfSourceCoefficient q*(∫ x in tortoiseOf v.1..tortoiseOf b,forcingKernel q br amp (grad q br) w x)-
    ((firstWeight q (Real.exp v.2)-physicalSelfSourceCoefficient q)*canonicalForcingCounterterm q br amp (grad q br) w v.1+
      secondWeight q (Real.exp v.2)*canonicalForcingCounterterm q br amp (grad q br+1) w v.1)

private theorem error_cut_decomposition (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    {b : ℝ} (hb : b∈Ioo (0:ℝ) 1) (v : ℝ×ℝ) (he : v.1∈Ioo (0:ℝ) 1) :
    canonicalForcingDifferenceCut q br amp w b v=
      (firstWeight q (Real.exp v.2)-physicalSelfSourceCoefficient q)*
        ((∫ x in tortoiseOf v.1..tortoiseOf b,forcingKernel q br amp (grad q br) w x)-
          canonicalForcingCounterterm q br amp (grad q br) w v.1)+
      secondWeight q (Real.exp v.2)*
        ((∫ x in tortoiseOf v.1..tortoiseOf b,forcingKernel q br amp (grad q br+1) w x)-
          canonicalForcingCounterterm q br amp (grad q br+1) w v.1) := by
  rw [canonicalForcingDifferenceCut,integral_two_kernels q br amp w _ _ _ (tortoiseOf_neg he) (tortoiseOf_neg hb)]
  dsimp only [D4BMOriginalForcingJointHorizon.gradient,grad]
  ring

/-- The canonical finite-height forcing discrepancy vanishes under independent
cusp and horizon removal throughout the same domain as the full canonical action. -/
theorem canonical_forcing_difference_joint_limit (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) :
    ∃ B : ℝ,0<B ∧ B≤1/2 ∧ ∀ b : ℝ,0<b → b≤B →
      Tendsto (canonicalForcingDifferenceCut q br amp w b)
        ((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  let K := grad q br
  obtain ⟨R1,B1,hR1,hB1,hB1h,h1⟩ := canonical_radial_restoration q br amp K w hw hwr
  obtain ⟨R2,B2,hR2,hB2,hB2h,h2⟩ := canonical_radial_restoration q br amp (K+1) w hw hwr
  refine ⟨min B1 B2,lt_min hB1 hB2,(min_le_left _ _).trans hB1h,?_⟩
  intro b hb hbB
  have hb1 := hbB.trans (min_le_left _ _)
  have hb2 := hbB.trans (min_le_right _ _)
  have hbI : b∈Ioo (0:ℝ) 1 := ⟨hb,by linarith [hb1.trans hB1h]⟩
  have hA := (h1 b hb hb1).2 w (mem_ball_self hR1)
  have hB := (h2 b hb hb2).2 w (mem_ball_self hR2)
  have ht1 : Tendsto (fun e => (∫ x in tortoiseOf e..tortoiseOf b,forcingKernel q br amp K w x)-
      canonicalForcingCounterterm q br amp K w e) (𝓝[>] (0:ℝ))
      (𝓝 (horizonFinitePart q br amp K (incomingValue q br amp K) (incomingSlope q br amp K)
        (oppositeValue q br amp K) b w)) := by
    apply hA.congr'
    filter_upwards [] with e
    unfold canonicalForcingCounterterm D4BMOriginalMetricRadial.forcingCounterterm
    ring
  have ht2 : Tendsto (fun e => (∫ x in tortoiseOf e..tortoiseOf b,forcingKernel q br amp (K+1) w x)-
      canonicalForcingCounterterm q br amp (K+1) w e) (𝓝[>] (0:ℝ))
      (𝓝 (horizonFinitePart q br amp (K+1) (incomingValue q br amp (K+1)) (incomingSlope q br amp (K+1))
        (oppositeValue q br amp (K+1)) b w)) := by
    apply hB.congr'
    filter_upwards [] with e
    unfold canonicalForcingCounterterm D4BMOriginalMetricRadial.forcingCounterterm
    ring
  have hw1 := (weights_limit q).1.sub_const (physicalSelfSourceCoefficient q)
  simp only [sub_self] at hw1
  have ht := ((hw1.comp tendsto_snd).mul (ht1.comp tendsto_fst)).add
    (((weights_limit q).2.comp tendsto_snd).mul (ht2.comp tendsto_fst))
  simp only [zero_mul,zero_add] at ht
  apply ht.congr'
  filter_upwards [(tendsto_fst : Tendsto (Prod.fst : ℝ×ℝ→ℝ)
    ((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝[>] 0)).eventually (Ioo_mem_nhdsGT hb)] with v hv
  exact (error_cut_decomposition q br amp w hbI v ⟨hv.1,hv.2.trans hbI.2⟩).symm

/-- Every actual positive-time interval shares the full source-onset L1 bound. -/
theorem source_onset_interval_bound (q : XiZeroCopy) (br : Bool) (w : ℂ) (hwr : -2<w.re) :
    ∃ C : ℝ,0≤C ∧ ∀ a b : ℝ,0≤a → a≤b →
      ‖∫ p in a..b,Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p‖≤C := by
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  have hi := timeOnset_integrable (2*physicalRate q br) w (hs.trans hwr)
  refine ⟨∫ p in Ioi (0:ℝ),‖Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p‖,
    integral_nonneg (fun _ => norm_nonneg _),?_⟩
  intro a b ha hab
  apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_mono_set hi.norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (Filter.Eventually.of_forall (fun p hp => ha.trans_lt hp.1))

/-- Full source-time factors cannot spoil independent forcing restoration,
even when the positive temporal endpoints vary arbitrarily with the other cuts. -/
theorem canonical_forcing_all_cutoffs (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) :
    ∃ B : ℝ,0<B ∧ B≤1/2 ∧ ∀ b : ℝ,0<b → b≤B →
      ∀ T : ℝ×ℝ→{v : ℝ×ℝ // 0≤v.1 ∧ v.1≤v.2},
        Tendsto (fun v : ℝ×ℝ =>
          (∫ p in (T v).val.1..(T v).val.2,Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p)*
            canonicalForcingDifferenceCut q br amp w b v)
          ((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  obtain ⟨B,hB,hBh,h⟩ := canonical_forcing_difference_joint_limit q br amp w hw hwr
  obtain ⟨C,hC,hbound⟩ := source_onset_interval_bound q br w hwr
  refine ⟨B,hB,hBh,?_⟩
  intro b hb hbB T
  have ht := (h b hb hbB).norm.const_mul C
  simp only [norm_zero,mul_zero] at ht
  apply squeeze_zero_norm (fun v => ?_) ht
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound _ _ (T v).property.1 (T v).property.2) (norm_nonneg _)

end
end RHTower.D4BMOriginalCanonicalForcingMatch
