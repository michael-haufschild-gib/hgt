import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCompactBoundary
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalForcingAngularPeriod

/-!
# Original metric time period

The complete Einstein current is integrated over the original finite modular
cell and a compact interval of ingoing time. Its exact scalar transfer retains
both temporal endpoints, the full forcing contact and the complete cusp flux.

The cusp subtraction is transported from those original terms. Its finite part
is the endpoint difference plus the source and forcing moments, with the
unchanged physical reader and radial coefficients. The temporal frequency
remains independent of the source label and both radial normalizations remain.

The identification holds at every exterior radius and every compact positive
time interval. No infinite-time, horizon or spectral limit is asserted.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry ScalarTwoJet
namespace RHTower.D4BMOriginalMetricTimePeriod
open GaloisForLFunctions.RHTower SelbergMaassMean SelbergMaassTraceStokes SelbergModularDomainSlices
open D4BMJointSource D4BMModularCore D4BMOriginalAngularCurrent D4BMOriginalOrbitCurrent
open D4BMOriginalReaderEquation D4BMOriginalModularOrbit D4BMOriginalCompactBoundary
open D4BMOriginalScalarRestoration D4BMOriginalCausalPeriod D4BMOriginalCircleFlux
open D4BMOriginalForcingAngularPeriod D4BMOriginalCornerForcing D4BMIngoingCoordinates
noncomputable section
set_option autoImplicit false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
private abbrev P := Fin 4 → ℝ
private abbrev F := P → ℂ
private def Smooth (U : F) : Prop := ∀ (z : P),0<z 0 → 1<z 1 → 0<z 3 → ContDiffAt ℝ ∞ U z

private theorem source_smooth (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    Smooth (sourceScalar q br amp) := D4BMOriginalGreenBoundary.sourceScalar_exterior_smooth q br amp
private theorem reader_smooth (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool) :
    Smooth (modeScalar q w outer) := fun z _ hr hy => modeScalar_smooth q w hw outer z hr hy
private theorem partial_smooth (U : F) (hU : Smooth U) (i : Fin 4) : Smooth (coordDeriv i U) :=
  fun z hp hr hy => coordDeriv_contDiffAt (hU z hp hr hy) (by simp) i

private theorem pair_fixed_integrable (U V : F) (hU : Smooth U) (hV : Smooth V)
    (p R Y : ℝ) (hp : 0<p) (hr : 1<R) : IntegrableOn
      (fun z : ℝ×ℝ => U (slice p R (point z.1 z.2))*V (slice p R (point z.1 z.2))/(z.2:ℂ)^2) (domain Y) := by
  apply ContinuousOn.integrableOn_compact (isCompact_domain Y)
  intro z hz
  have hy : 0<z.2 := by linarith [hz.1.2.1]
  have hm : Continuous (fun v : ℝ×ℝ => slice p R (point v.1 v.2)) := by unfold slice point;fun_prop
  have hu := (hU (slice p R (point z.1 z.2)) hp hr (by simpa [slice,point] using hy)).continuousAt.comp
    (f:=fun v : ℝ×ℝ => slice p R (point v.1 v.2)) (x:=z) hm.continuousAt
  have hv := (hV (slice p R (point z.1 z.2)) hp hr (by simpa [slice,point] using hy)).continuousAt.comp
    (f:=fun v : ℝ×ℝ => slice p R (point v.1 v.2)) (x:=z) hm.continuousAt
  have hd : ContinuousAt (fun v : ℝ×ℝ => (v.2:ℂ)^2) z := by fun_prop
  exact ((hu.mul hv).div hd (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hy.ne'))).continuousWithinAt

private theorem pair_product_integrable (U V : F) (hU : Smooth U) (hV : Smooth V)
    (a b R Y : ℝ) (ha : 0<a) (hr : 1<R) :
    Integrable (fun z : ℝ × (ℝ × ℝ) =>
      U (slice z.1 R (point z.2.1 z.2.2))*V (slice z.1 R (point z.2.1 z.2.2))/(z.2.2:ℂ)^2)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (domain Y))) := by
  have hm : Continuous (fun z : ℝ × (ℝ × ℝ) => slice z.1 R (point z.2.1 z.2.2)) := by
    unfold slice point
    fun_prop
  have hc : ContinuousOn (fun z : ℝ × (ℝ × ℝ) =>
      U (slice z.1 R (point z.2.1 z.2.2))*V (slice z.1 R (point z.2.1 z.2.2))/(z.2.2:ℂ)^2)
      ((Icc a b).prod (domain Y)) := by
    intro z hz
    have hp : 0<z.1 := ha.trans_le hz.1.1
    have hy : 0<z.2.2 := by linarith [hz.2.1.2.1]
    have hu := hU (slice z.1 R (point z.2.1 z.2.2)) hp hr (by simpa [slice,point] using hy)
    have hv := hV (slice z.1 R (point z.2.1 z.2.2)) hp hr (by simpa [slice,point] using hy)
    have hu' := hu.continuousAt.comp (f:=fun v : ℝ × (ℝ × ℝ) => slice v.1 R (point v.2.1 v.2.2)) (x:=z) hm.continuousAt
    have hv' := hv.continuousAt.comp (f:=fun v : ℝ × (ℝ × ℝ) => slice v.1 R (point v.2.1 v.2.2)) (x:=z) hm.continuousAt
    have hd : ContinuousAt (fun v : ℝ × (ℝ × ℝ) => (v.2.2:ℂ)^2) z := by fun_prop
    exact ((hu'.mul hv').div hd (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hy.ne'))).continuousWithinAt
  rw [Measure.prod_restrict,← Measure.volume_eq_prod]
  exact (hc.integrableOn_compact (isCompact_Icc.prod (isCompact_domain Y))).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Subset.rfl)

private theorem pair_time_integrable (U V : F) (hU : Smooth U) (hV : Smooth V)
    (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) :
    IntervalIntegrable (fun p => scalarPeriod U V p R Y) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (pair_product_integrable U V hU hV a b R Y ha hr).integral_prod_left

private theorem pair_time_swap (U V : F) (hU : Smooth U) (hV : Smooth V)
    (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) :
    (∫ p in a..b,scalarPeriod U V p R Y)=
      ∫ z in domain Y, ∫ p in a..b,
        U (slice p R (point z.1 z.2))*V (slice p R (point z.1 z.2))/(z.2:ℂ)^2 := by
  simp only [scalarPeriod,intervalIntegral.integral_of_le hab]
  exact integral_integral_swap (pair_product_integrable U V hU hV a b R Y ha hr)

/-- Time integration of the original source-current period retains both original endpoints. -/
theorem original_period_time_transfer (q r : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) :
    let U := sourceScalar q br amp
    let W := modeScalar r w outer
    (∫ p in a..b,scalarPeriod (coordDeriv 0 U) W p R Y+w*scalarPeriod U W p R Y)=
      scalarPeriod U W b R Y-scalarPeriod U W a R Y+
        2*w*(∫ p in a..b,scalarPeriod U W p R Y) := by
  dsimp only
  let U := sourceScalar q br amp
  let W := modeScalar r w outer
  have hU := source_smooth q br amp
  have hW := reader_smooth r w hw outer
  have hD := partial_smooth U hU 0
  have hV : Smooth (fun z => coordDeriv 0 U z+w*U z) :=
    fun z hp hr hy => (hD z hp hr hy).add (contDiffAt_const.mul (hU z hp hr hy))
  have hP (p : ℝ) (hp : 0<p) :
      scalarPeriod (fun z => coordDeriv 0 U z+w*U z) W p R Y=
        scalarPeriod (coordDeriv 0 U) W p R Y+w*scalarPeriod U W p R Y := by
    have hc (A : F) (hA : Smooth A) : IntegrableOn
        (fun z : ℝ×ℝ => A (slice p R (point z.1 z.2))*W (slice p R (point z.1 z.2))/(z.2:ℂ)^2) (domain Y) :=
      pair_fixed_integrable A W hA hW p R Y hp hr
    simp only [scalarPeriod,← integral_const_mul]
    rw [← integral_add (hc _ hD) ((hc U hU).const_mul w)]
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro z _
    dsimp only
    ring
  have he : (∫ p in a..b,scalarPeriod (coordDeriv 0 U) W p R Y+w*scalarPeriod U W p R Y)=
      ∫ p in a..b,scalarPeriod (fun z => coordDeriv 0 U z+w*U z) W p R Y := by
    apply intervalIntegral.integral_congr
    intro p hp
    exact (hP p (ha.trans_le ((uIcc_of_le hab ▸ hp).1))).symm
  rw [he,pair_time_swap _ W hV hW a b R Y ha hab hr,pair_time_swap U W hU hW a b R Y ha hab hr]
  have hpoint (z : ℝ×ℝ) (hz : z∈domain Y) :
      (∫ p in a..b,(coordDeriv 0 U (slice p R (point z.1 z.2))+w*U (slice p R (point z.1 z.2)))*
        W (slice p R (point z.1 z.2))/(z.2:ℂ)^2)=
      (U (slice b R (point z.1 z.2))*W (slice b R (point z.1 z.2))-
        U (slice a R (point z.1 z.2))*W (slice a R (point z.1 z.2))+
          2*w*(∫ p in a..b,U (slice p R (point z.1 z.2))*W (slice p R (point z.1 z.2))))/(z.2:ℂ)^2 := by
    rw [intervalIntegral.integral_div]
    rw [mode_time_transfer q r br outer amp w hw a b R ha hab hr]
    simp only [point,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add]
    linarith [hz.1.2.1]
  rw [setIntegral_congr_fun (isCompact_domain Y).measurableSet hpoint]
  -- The remaining finite-domain integrations are performed after retaining both endpoints.
  have hi (p : ℝ) (hp : 0<p) : IntegrableOn
      (fun z : ℝ×ℝ => U (slice p R (point z.1 z.2))*W (slice p R (point z.1 z.2))/(z.2:ℂ)^2) (domain Y) :=
    pair_fixed_integrable U W hU hW p R Y hp hr
  have hT := (pair_product_integrable U W hU hW a b R Y ha hr).integral_prod_right
  change IntegrableOn (fun z : ℝ×ℝ => ∫ p in Ioc a b,
    U (slice p R (point z.1 z.2))*W (slice p R (point z.1 z.2))/(z.2:ℂ)^2) (domain Y) at hT
  simp only [← intervalIntegral.integral_of_le hab] at hT
  have hn : (fun z : ℝ×ℝ =>
      (U (slice b R (point z.1 z.2))*W (slice b R (point z.1 z.2))-
        U (slice a R (point z.1 z.2))*W (slice a R (point z.1 z.2))+
          2*w*(∫ p in a..b,U (slice p R (point z.1 z.2))*W (slice p R (point z.1 z.2))))/(z.2:ℂ)^2)=
      fun z => U (slice b R (point z.1 z.2))*W (slice b R (point z.1 z.2))/(z.2:ℂ)^2-
        U (slice a R (point z.1 z.2))*W (slice a R (point z.1 z.2))/(z.2:ℂ)^2+
          2*w*(∫ p in a..b,U (slice p R (point z.1 z.2))*W (slice p R (point z.1 z.2))/(z.2:ℂ)^2) := by
    funext z
    rw [intervalIntegral.integral_div]
    ring
  have hsub := (hi b (ha.trans_le hab)).sub (hi a ha)
  simp only [Pi.sub_def] at hsub
  rw [hn,integral_add hsub (hT.const_mul (2*w)),
    integral_sub (hi b (ha.trans_le hab)) (hi a ha),integral_const_mul]
  rfl

/-- The exact time-independent coefficient of the unchanged physical scalar reader. -/
def readerCoefficient (q : XiZeroCopy) (w : ℂ) (outer : Bool) (R : ℝ) : ℂ :=
  Complex.exp (w*(tortoise R:ℂ))*D4BMPhysicalModeAction.radiusLift (modeProfile q w outer) R

private theorem reader_slice (q : XiZeroCopy) (w : ℂ) (outer : Bool) (p R : ℝ) (z : ℂ) :
    modeScalar q w outer (slice p R z)=readerCoefficient q w outer R*Complex.exp (-w*(p:ℂ))*
      D4BMLiteralCusp.scalar (physicalAngularParameter q) ![z.re,z.im] := by
  rw [modeScalar_value]
  simp only [slice,D4BMMetricReconstruction.angularPoint,Matrix.cons_val]
  have he : -w*((p:ℂ)-(tortoise R:ℂ))=w*(tortoise R:ℂ)+(-w*(p:ℂ)) := by ring
  rw [he,Complex.exp_add]
  unfold readerCoefficient
  ring

/-- The source period's prescribed counterterm, with its original reader coefficient. -/
def sourceCounterterm (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (p R Y : ℝ) : ℂ :=
  (R:ℂ)*readerCoefficient q w outer R*Complex.exp (-w*(p:ℂ))*
    principalCounterterm q (D4BMOriginalCuspJets.coefficient q br amp p (p-2*tortoise R)) Y

/-- Original source period after precisely its three cusp subtractions. -/
def sourcePeriodCut (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (p R Y : ℝ) : ℂ :=
  scalarPeriod (sourceScalar q br amp) (modeScalar q w outer) p R Y-
    sourceCounterterm q br outer amp w p R Y

/-- Exact finite-height attachment to the original causal scalar period. -/
theorem original_source_period_cut (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (p R Y : ℝ) :
    sourcePeriodCut q br outer amp w p R Y=
      (R:ℂ)*readerCoefficient q w outer R*Complex.exp (-w*(p:ℂ))*
        originalFiniteHeightPeriod q br amp p (p-2*tortoise R) Y := by
  have h := original_truncatedIntegral_area (fun z =>
    D4BMLiteralCusp.scalar (physicalAngularParameter q) z*
      D4BMOriginalCausalPotential.originalPotential q br amp p (p-2*tortoise R) (z 0) (Real.log (z 1))) Y
  have hP : scalarPeriod (sourceScalar q br amp) (modeScalar q w outer) p R Y=
      (R:ℂ)*readerCoefficient q w outer R*Complex.exp (-w*(p:ℂ))*
        truncatedIntegral (fun z => D4BMLiteralCusp.scalar (physicalAngularParameter q) ![z.re,z.im]*
          D4BMOriginalCausalPotential.originalPotential q br amp p (p-2*tortoise R) z.re (Real.log z.im)) Y := by
    simp only [Matrix.cons_val] at h
    rw [h,scalarPeriod,← integral_const_mul]
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro z _
    dsimp only
    rw [reader_slice]
    simp only [sourceScalar,D4BMActualIngoingCurrent.originalIngoingPotential,slice,Matrix.cons_val,
      point,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_I_re,Complex.mul_I_im,neg_zero,add_zero,zero_add]
    ring
  rw [sourcePeriodCut,hP,sourceCounterterm,originalFiniteHeightPeriod,mul_sub]
  rfl

/-- The full forcing period's original three principal counterterms. -/
def forcingCounterterm (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (p R Y : ℝ) : ℂ :=
  readerCoefficient q w outer R*(D4BMJointSource.horizonCoordinate (tortoise R):ℂ)*
    Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p*
      principalCounterterm q (profilePrincipal q br amp (radialUnit (tortoise R))) Y

def forcingPeriodCut (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (p R Y : ℝ) : ℂ :=
  scalarPeriod (D4BMOriginalSourceContact.originalForcing q br amp) (modeScalar q w outer) p R Y-
    forcingCounterterm q br outer amp w p R Y

private theorem forcing_period_raw (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (p R Y : ℝ) :
    scalarPeriod (D4BMOriginalSourceContact.originalForcing q br amp) (modeScalar q w outer) p R Y=
      readerCoefficient q w outer R*(D4BMJointSource.horizonCoordinate (tortoise R):ℂ)*
        Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p*
          truncatedIntegral (fun z => D4BMLiteralCusp.scalar (physicalAngularParameter q) ![z.re,z.im]*
            forcingProfile (physicalRate q br) amp (fullSquarePotential q ![z.re,z.im])
              (fullGradientEnergy q ![z.re,z.im]/2) (radialUnit (tortoise R))) Y := by
  have h := original_truncatedIntegral_area (fun z => D4BMLiteralCusp.scalar (physicalAngularParameter q) z*
    forcingProfile (physicalRate q br) amp (fullSquarePotential q z)
      (fullGradientEnergy q z/2) (radialUnit (tortoise R))) Y
  rw [h,scalarPeriod,← integral_const_mul]
  apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
  intro z _
  dsimp only
  rw [reader_slice]
  simp only [D4BMOriginalSourceContact.originalForcing,timeOriginalForcing,slice,Matrix.cons_val,
    point,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_I_re,Complex.mul_I_im,neg_zero,add_zero,zero_add,sub_add_cancel]
  rw [original_forcing_factor]
  ring

/-- The original forcing angular period factors before time integration or cusp restoration. -/
theorem original_forcing_period_cut (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (p R Y : ℝ) :
    forcingPeriodCut q br outer amp w p R Y=
      readerCoefficient q w outer R*(D4BMJointSource.horizonCoordinate (tortoise R):ℂ)*
        Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p*
          profileCut q br amp (radialUnit (tortoise R)) Y := by
  rw [forcingPeriodCut,forcing_period_raw,forcingCounterterm,profileCut,mul_sub]
  rfl

private theorem tortoise_negative (R : ℝ) (hr : 1<R) : tortoise R<0 := by
  have h := Real.log_lt_log (show 0<R-1 by linarith) (show R-1<R+1 by linarith)
  dsimp [tortoise]
  linarith

private theorem source_cut_time_integrable (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (hY : 4≤Y) :
    IntervalIntegrable (fun p => sourcePeriodCut q br outer amp w p R Y) volume a b := by
  simp_rw [original_source_period_cut]
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  have h := originalFiniteHeightPeriod_time_continuousOn q br amp a b (tortoise R) Y ha.le hab
    (tortoise_negative R hr).le hY
  exact ((continuous_const.mul (show Continuous (fun p : ℝ => Complex.exp (-w*(p:ℂ))) by fun_prop)).continuousOn).mul h

/-- Fixed-radius time integration commutes with the original source-period cusp subtraction. -/
theorem original_source_period_time_finitePart (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (a b R : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) :
    Tendsto (fun k : ℝ => ∫ p in a..b,sourcePeriodCut q br outer amp w p R (Real.exp k)) atTop
      (𝓝 ((R:ℂ)*readerCoefficient q w outer R*
        ∫ p in a..b,Complex.exp (-w*(p:ℂ))*originalRadialPeriod q br amp p (p-2*tortoise R))) := by
  have h := (original_compact_time_restoration q br amp w a b (tortoise R) ha.le hab
    (tortoise_negative R hr).le).comp Real.tendsto_exp_atTop
  have h' := h.const_mul ((R:ℂ)*readerCoefficient q w outer R)
  apply h'.congr'
  filter_upwards [] with k
  simp only [Function.comp_def,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro p _
  dsimp only
  rw [original_source_period_cut]
  ring

private theorem source_cut_fixed_limit (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (p R : ℝ) (hp : 0≤p) (hr : 1<R) :
    Tendsto (fun k : ℝ => sourcePeriodCut q br outer amp w p R (Real.exp k)) atTop
      (𝓝 ((R:ℂ)*readerCoefficient q w outer R*Complex.exp (-w*(p:ℂ))*
        originalRadialPeriod q br amp p (p-2*tortoise R))) := by
  have h := original_causal_finitePart_radial q br amp ⟨p,hp⟩
    ⟨p-2*tortoise R,by change 0≤p-2*tortoise R;linarith [tortoise_negative R hr]⟩
  change Tendsto (originalFiniteHeightPeriod q br amp p (p-2*tortoise R)) atTop
    (𝓝 (originalRadialPeriod q br amp p (p-2*tortoise R))) at h
  have h' := (h.comp Real.tendsto_exp_atTop).const_mul
    ((R:ℂ)*readerCoefficient q w outer R*Complex.exp (-w*(p:ℂ)))
  simpa only [Function.comp_def,original_source_period_cut] using h'

private theorem onset_continuous (s : ℂ) : Continuous (timeOnset s) :=
  continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt s p).continuousAt)

private theorem forcing_cut_time_integrable (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (a b R Y : ℝ) : IntervalIntegrable (fun p => forcingPeriodCut q br outer amp w p R Y) volume a b := by
  simp_rw [original_forcing_period_cut]
  exact (((show Continuous (fun p : ℝ => Complex.exp (-w*(p:ℂ))) by fun_prop).const_mul _).mul
    (onset_continuous _)|>.mul_const _).intervalIntegrable a b

private theorem forcing_time_integrable (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (a b R Y : ℝ) : IntervalIntegrable
      (fun p => scalarPeriod (D4BMOriginalSourceContact.originalForcing q br amp) (modeScalar q w outer) p R Y) volume a b := by
  simp_rw [forcing_period_raw]
  exact (((show Continuous (fun p : ℝ => Complex.exp (-w*(p:ℂ))) by fun_prop).const_mul _).mul
    (onset_continuous _)|>.mul_const _).intervalIntegrable a b

/-- Full forcing contact after original angular subtraction and finite-time integration. -/
theorem original_forcing_period_time_finitePart (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (a b R : ℝ) :
    Tendsto (fun k : ℝ => ∫ p in a..b,forcingPeriodCut q br outer amp w p R (Real.exp k)) atTop
      (𝓝 (readerCoefficient q w outer R*(horizonCoordinate (tortoise R):ℂ)*physicalSelfSourceCoefficient q*
        forcingProfile (physicalRate q br) amp 1
          (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) (radialUnit (tortoise R))*
          ∫ p in a..b,Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p)) := by
  have h := (original_profile_finitePart q br amp (radialUnit (tortoise R))).const_mul
    (readerCoefficient q w outer R*(horizonCoordinate (tortoise R):ℂ))
  have h' := h.mul_const (∫ p in a..b,Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p)
  rw [← mul_assoc] at h'
  apply h'.congr'
  filter_upwards [] with k
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro p _
  dsimp only
  rw [original_forcing_period_cut]
  ring

private theorem contact_smooth {U : F} (hU : Smooth U) : Smooth (D4BMOriginalSourceContact.scalarContact U) := by
  intro x hp hr hy
  have h0 := partial_smooth U hU 0 x hp hr hy
  have h1 := partial_smooth U hU 1 x hp hr hy
  have h01 := partial_smooth _ (partial_smooth U hU 1) 0 x hp hr hy
  have h10 := partial_smooth _ (partial_smooth U hU 0) 1 x hp hr hy
  have h11 := partial_smooth _ (partial_smooth U hU 1) 1 x hp hr hy
  have hR : ContDiffAt ℝ ∞ (fun z : P => (z 1:ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (1:Fin 4))).contDiffAt
  change ContDiffAt ℝ ∞ (fun z : P =>
    -(z 1:ℂ)^2*((z 1:ℂ)^2-1)*coordDeriv 1 (coordDeriv 1 U) z-
    (z 1:ℂ)^2*(coordDeriv 0 (coordDeriv 1 U) z+coordDeriv 1 (coordDeriv 0 U) z)-
    2*(z 1:ℂ)*coordDeriv 1 U z+2*(z 1:ℂ)*coordDeriv 0 U z) x
  exact ((((hR.pow 2).neg.mul ((hR.pow 2).sub contDiffAt_const)).mul h11).sub
    ((hR.pow 2).mul (h01.add h10)) |>.sub ((contDiffAt_const.mul hR).mul h1)).add
      ((contDiffAt_const.mul hR).mul h0)

private theorem forced_smooth (q : XiZeroCopy) (br : Bool) (amp : ℂ) : Smooth (forcedContact q br amp) := by
  intro x hp hr hy
  have he : D4BMOriginalSourceContact.scalarContact (sourceScalar q br amp)=ᶠ[𝓝 x] forcedContact q br amp := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hp,
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
      (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hz0 hz1 hz3
    exact D4BMOriginalSourceContact.original_scalar_contact q br amp z hz0 hz1 hz3
  exact (contact_smooth (source_smooth q br amp) x hp hr hy).congr_of_eventuallyEq he.symm

private theorem top_time_integrable (U V : F) (hU : Smooth U) (hV : Smooth V)
    (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (hy : 0<Y) :
    IntervalIntegrable (fun p => topFlux U V p R Y) volume a b := by
  have hc : ContinuousOn (fun z : ℝ×ℝ => transfer U V 1 (slice z.1 R (point z.2 Y)))
      ((Icc a b).prod (Icc (-1/2:ℝ) (1/2:ℝ))) := by
    intro z hz
    have hu := hU (slice z.1 R (point z.2 Y)) (ha.trans_le hz.1.1) hr (by simpa [slice,point] using hy)
    have hv := partial_smooth V hV 3 (slice z.1 R (point z.2 Y)) (ha.trans_le hz.1.1) hr (by simpa [slice,point] using hy)
    change ContinuousWithinAt (fun z : ℝ×ℝ => U (slice z.1 R (point z.2 Y))*coordDeriv 3 V (slice z.1 R (point z.2 Y))) _ z
    exact ((hu.continuousAt.mul hv.continuousAt).comp
      (f:=fun z : ℝ×ℝ => slice z.1 R (point z.2 Y))
      (show Continuous (fun z : ℝ×ℝ => slice z.1 R (point z.2 Y)) by unfold slice point; fun_prop).continuousAt).continuousWithinAt
  have hi : Integrable (fun z : ℝ×ℝ => transfer U V 1 (slice z.1 R (point z.2 Y)))
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (-1/2:ℝ) (1/2:ℝ)))) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  simpa only [topFlux,← neg_div,intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2),IntegrableOn]
    using hi.integral_prod_left

/-- The original static-time metric density after finite angular integration. -/
def metricSlice (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (p R Y : ℝ) : ℂ :=
  (∫ z in domain Y,modeMetricDensity q q br outer amp w 0 (slice p R (point z.1 z.2)))-
    (∫ z in domain Y,modeMetricDensity q q br outer amp w 1 (slice p R (point z.1 z.2)))/((R:ℂ)^2-1)

def boundarySlice (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (p R Y : ℝ) : ℂ :=
  (modeCompleteTopFlux q q br outer amp w 0 p R Y-
    modeCompleteTopFlux q q br outer amp w 1 p R Y/((R:ℂ)^2-1))/(R:ℂ)^2

def sourcePrefactor (q : XiZeroCopy) (R : ℝ) : ℂ :=
  D4BMLeftModeRadialEquation.eigenvalue q*(D4BMLeftModeRadialEquation.eigenvalue q-2)/
    ((R:ℂ)^2*((R:ℂ)^2-1))

def forcingPrefactor (q : XiZeroCopy) (w : ℂ) (R : ℝ) : ℂ :=
  D4BMLeftModeRadialEquation.eigenvalue q*(R:ℂ)*w/((R:ℂ)^2-1)^2

private theorem boundary_time_integrable (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (hy : 0<Y) :
    IntervalIntegrable (fun p => boundarySlice q br outer amp w p R Y) volume a b := by
  let U := sourceScalar q br amp
  let W := modeScalar q w outer
  have hU := source_smooth q br amp
  have hW := reader_smooth q w hw outer
  have hd := top_time_integrable _ W (partial_smooth U hU 0) hW a b R Y ha hab hr hy
  have hf := top_time_integrable _ W (forced_smooth q br amp) hW a b R Y ha hab hr hy
  have hu := top_time_integrable U W hU hW a b R Y ha hab hr hy
  have hv := top_time_integrable W U hW hU a b R Y ha hab hr hy
  have hi := (((hd.const_mul (-(D4BMLeftModeRadialEquation.eigenvalue q-2))).sub
    (hf.const_mul w)).add ((hv.sub hu).const_mul (D4BMLeftModeRadialEquation.eigenvalue q*w))).div_const
      ((R:ℂ)^2*((R:ℂ)^2-1))
  apply hi.congr
  intro p hp
  have hp' : 0<p := ha.trans ((uIoc_of_le hab ▸ hp).1)
  exact (mode_static_top_flux q q br outer amp w hw p R Y hp' hr hy).symm

/-- Finite-time original Einstein pairing, with its unchanged physical reader. -/
def metricTimeRaw (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (a b R Y : ℝ) : ℂ :=
  ∫ p in a..b,metricSlice q br outer amp w p R Y

/-- Complete finite-domain transfer: both original endpoints, forcing and cusp flux survive. -/
theorem original_metric_time_transfer (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (hY : 1≤Y) :
    metricTimeRaw q br outer amp w a b R Y=
      sourcePrefactor q R*(scalarPeriod (sourceScalar q br amp) (modeScalar q w outer) b R Y-
        scalarPeriod (sourceScalar q br amp) (modeScalar q w outer) a R Y+
          2*w*(∫ p in a..b,scalarPeriod (sourceScalar q br amp) (modeScalar q w outer) p R Y))+
      forcingPrefactor q w R*(∫ p in a..b,scalarPeriod (D4BMOriginalSourceContact.originalForcing q br amp)
        (modeScalar q w outer) p R Y)+
      ∫ p in a..b,boundarySlice q br outer amp w p R Y := by
  let U := sourceScalar q br amp
  let W := modeScalar q w outer
  have hu := pair_time_integrable U W (source_smooth q br amp) (reader_smooth q w hw outer) a b R Y ha hab hr
  have hd := pair_time_integrable _ W (partial_smooth U (source_smooth q br amp) 0)
    (reader_smooth q w hw outer) a b R Y ha hab hr
  have hf := forcing_time_integrable q br outer amp w a b R Y
  have hb := boundary_time_integrable q br outer amp w hw a b R Y ha hab hr (lt_of_lt_of_le (by norm_num) hY)
  have he : metricTimeRaw q br outer amp w a b R Y=
      ∫ p in a..b,sourcePrefactor q R*(scalarPeriod (coordDeriv 0 U) W p R Y+w*scalarPeriod U W p R Y)+
        forcingPrefactor q w R*scalarPeriod (D4BMOriginalSourceContact.originalForcing q br amp) W p R Y+
        boundarySlice q br outer amp w p R Y := by
    apply intervalIntegral.integral_congr
    intro p hp
    exact mode_static_metric_scalar_integral q q br outer amp w hw p R
      (ha.trans_le ((uIcc_of_le hab ▸ hp).1)) hr hY
  rw [he,intervalIntegral.integral_add (((hd.add (hu.const_mul w)).const_mul _).add (hf.const_mul _)) hb,
    intervalIntegral.integral_add ((hd.add (hu.const_mul w)).const_mul _) (hf.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    original_period_time_transfer q q br outer amp w hw a b R Y ha hab hr]

/-- The entire cusp counterterm forced by the finite-domain metric identity.
It retains the source endpoints, source moment, forcing moment and complete top flux. -/
def metricTimeCounterterm (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (a b R Y : ℝ) : ℂ :=
  sourcePrefactor q R*(sourceCounterterm q br outer amp w b R Y-sourceCounterterm q br outer amp w a R Y+
    2*w*(∫ p in a..b,sourceCounterterm q br outer amp w p R Y))+
  forcingPrefactor q w R*(∫ p in a..b,forcingCounterterm q br outer amp w p R Y)+
  ∑ i : Fin 3,compactBoundaryCoefficient q q br outer amp w a b R i*
    Complex.exp (D4BMOriginalCuspFlux.fluxExponent q q i*(Real.log Y:ℂ))

/-- Original metric time integral with all counterterms prescribed by its source and flux. -/
def metricTimeCut (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (a b R Y : ℝ) : ℂ :=
  metricTimeRaw q br outer amp w a b R Y-metricTimeCounterterm q br outer amp w a b R Y

private theorem metric_time_cut_decomposition (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (hY : 4≤Y) :
    metricTimeCut q br outer amp w a b R Y=
      sourcePrefactor q R*(sourcePeriodCut q br outer amp w b R Y-sourcePeriodCut q br outer amp w a R Y+
        2*w*(∫ p in a..b,sourcePeriodCut q br outer amp w p R Y))+
      forcingPrefactor q w R*(∫ p in a..b,forcingPeriodCut q br outer amp w p R Y)+
      ((∫ p in a..b,boundarySlice q br outer amp w p R Y)-
        ∑ i : Fin 3,compactBoundaryCoefficient q q br outer amp w a b R i*
          Complex.exp (D4BMOriginalCuspFlux.fluxExponent q q i*(Real.log Y:ℂ))) := by
  have hU := pair_time_integrable _ _ (source_smooth q br amp) (reader_smooth q w hw outer) a b R Y ha hab hr
  have hS := source_cut_time_integrable q br outer amp w a b R Y ha hab hr hY
  have hF := forcing_time_integrable q br outer amp w a b R Y
  have hG := forcing_cut_time_integrable q br outer amp w a b R Y
  have hs : IntervalIntegrable (fun p => sourceCounterterm q br outer amp w p R Y) volume a b := by
    have he : (fun p => sourceCounterterm q br outer amp w p R Y)=
        fun p => scalarPeriod (sourceScalar q br amp) (modeScalar q w outer) p R Y-
          sourcePeriodCut q br outer amp w p R Y := by funext p;unfold sourcePeriodCut;ring
    rw [he]
    exact hU.sub hS
  have hf : IntervalIntegrable (fun p => forcingCounterterm q br outer amp w p R Y) volume a b := by
    have he : (fun p => forcingCounterterm q br outer amp w p R Y)=
        fun p => scalarPeriod (D4BMOriginalSourceContact.originalForcing q br amp) (modeScalar q w outer) p R Y-
          forcingPeriodCut q br outer amp w p R Y := by funext p;unfold forcingPeriodCut;ring
    rw [he]
    exact hF.sub hG
  have hIS : (∫ p in a..b,sourcePeriodCut q br outer amp w p R Y)=
      (∫ p in a..b,scalarPeriod (sourceScalar q br amp) (modeScalar q w outer) p R Y)-
        ∫ p in a..b,sourceCounterterm q br outer amp w p R Y := by
    simpa only [sourcePeriodCut,Pi.sub_def] using intervalIntegral.integral_sub hU hs
  have hIF : (∫ p in a..b,forcingPeriodCut q br outer amp w p R Y)=
      (∫ p in a..b,scalarPeriod (D4BMOriginalSourceContact.originalForcing q br amp) (modeScalar q w outer) p R Y)-
        ∫ p in a..b,forcingCounterterm q br outer amp w p R Y := by
    simpa only [forcingPeriodCut,Pi.sub_def] using intervalIntegral.integral_sub hF hf
  rw [metricTimeCut,original_metric_time_transfer q br outer amp w hw a b R Y ha hab hr (by linarith),
    metricTimeCounterterm,hIS,hIF,sourcePeriodCut,sourcePeriodCut]
  ring

/-- The source-faithful time-integrated metric value, retaining both endpoint values
of the original causal radial response and the full source-contact moment. -/
def restoredMetricTime (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ) (a b R : ℝ) : ℂ :=
  sourcePrefactor q R*((R:ℂ)*readerCoefficient q w outer R*Complex.exp (-w*(b:ℂ))*
      originalRadialPeriod q br amp b (b-2*tortoise R)-
    (R:ℂ)*readerCoefficient q w outer R*Complex.exp (-w*(a:ℂ))*
      originalRadialPeriod q br amp a (a-2*tortoise R)+
    2*w*((R:ℂ)*readerCoefficient q w outer R*
      ∫ p in a..b,Complex.exp (-w*(p:ℂ))*originalRadialPeriod q br amp p (p-2*tortoise R)))+
  forcingPrefactor q w R*(readerCoefficient q w outer R*(horizonCoordinate (tortoise R):ℂ)*physicalSelfSourceCoefficient q*
    forcingProfile (physicalRate q br) amp 1
      (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) (radialUnit (tortoise R))*
    ∫ p in a..b,Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p)

/-- Complete original metric time-period identification at every fixed exterior radius.
The source, forcing, angular measure, temporal endpoints and all three cusp flux powers
are retained. Infinite time, horizon and spectral continuation are not taken here. -/
theorem original_metric_time_finitePart (q : XiZeroCopy) (br outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (a b R : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) :
    Tendsto (fun k : ℝ => metricTimeCut q br outer amp w a b R (Real.exp k)) atTop
      (𝓝 (restoredMetricTime q br outer amp w a b R)) := by
  have hA := source_cut_fixed_limit q br outer amp w a R ha.le hr
  have hB := source_cut_fixed_limit q br outer amp w b R (ha.le.trans hab) hr
  have hS := original_source_period_time_finitePart q br outer amp w a b R ha hab hr
  have hF := original_forcing_period_time_finitePart q br outer amp w a b R
  have hC := mode_complete_boundary_compact_cusp q q br outer amp w hw a b R ha hab hr
  have h := ((((hB.sub hA).add (hS.const_mul (2*w))).const_mul (sourcePrefactor q R)).add
    (hF.const_mul (forcingPrefactor q w R))).add hC
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [Real.tendsto_exp_atTop.eventually (eventually_ge_atTop (4:ℝ))] with k hk
  rw [metric_time_cut_decomposition q br outer amp w hw a b R (Real.exp k) ha hab hr hk,Real.log_exp]
  rfl

end
end RHTower.D4BMOriginalMetricTimePeriod
