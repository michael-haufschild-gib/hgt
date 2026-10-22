import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticNativeCuspCurrent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticResponseMellinTransport
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticTestedCurrentCusp

/-!
# Complete quadratic-response cusp current

The original cusp assembly identifies each full response with its height-only
particular response plus its native forced field. The particular terms cancel
from the nonconstant bilinear current while remaining in both full means.
The complete incoming current retains its exact physical source contacts.
Every complex height power preserves the zero upper trace of the remaining
nonconstant current, including the original physical scalar principal factor.
The full scalar tail, source-contact trace and other physical faces remain.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMQuarticFullResponseCurrent
open D4BMModularCore D4BMGlobalAngularResponse D4BMCuspResponse
open D4BMQuarticNativeCuspCurrent D4BMQuarticResponseMellinTransport
noncomputable section
set_option autoImplicit false

private def fullPlanar (q : XiZeroCopy) (b : Bool) : ℂ → ℂ := fullAngular q b ∘ ofComplex
private def particular (q : XiZeroCopy) (b : Bool) (y : ℝ) : ℂ := cuspResponse q b ![0,y]
private def cell : Set ℝ := Ioc (-1/2:ℝ) (1/2)

private theorem full_smooth (q : XiZeroCopy) (b : Bool) :
    ContDiffOn ℝ ∞ (fullPlanar q b) {z : ℂ | 0 < z.im} :=
  (fullAngular_smooth q b).planar_contDiffOn

private theorem point_coordinates (x y : ℝ) : angularCoordinates (point x y)=![x,y] := by
  ext j
  fin_cases j <;> simp [angularCoordinates,point]

private theorem full_field_planar (q : XiZeroCopy) (b : Bool) :
    fullAngularField q b ∘ angularCoordinates=fullPlanar q b := by
  funext z
  simp only [fullAngularField,Function.comp_apply,angularCoordinates.symm_apply_apply]
  rfl

private theorem vertical_full_field (q : XiZeroCopy) (b : Bool) (x y : ℝ) :
    vertical (fullPlanar q b) (point x y)=coordDeriv 1 (fullAngularField q b) ![x,y] := by
  have h := angularCoordinates_derivative (fullAngularField q b) 1 (point x y)
  rw [full_field_planar,point_coordinates] at h
  exact h

private theorem full_cusp_value (q : XiZeroCopy) (b : Bool) {x y : ℝ}
    (hx : x ∈ cell) (hy : 3 < y) :
    fullPlanar q b (point x y)=particular q b y+responsePlanar q b (point x y) := by
  have hpos : 0 < (point x y).im := by simp only [point,Complex.add_im,Complex.ofReal_im,
    Complex.mul_I_im,Complex.ofReal_re,zero_add]; linarith
  let z : UpperHalfPlane := ⟨point x y,hpos⟩
  have hcoord : coordinates z=![x,y] := by
    ext j
    fin_cases j <;> simp [coordinates,z,point]
  have hfd : z ∈ fd := by
    constructor
    · change 1 ≤ Complex.normSq (point x y)
      simp only [Complex.normSq_apply,point,Complex.add_re,Complex.add_im,Complex.ofReal_re,
        Complex.ofReal_im,Complex.mul_I_re,Complex.mul_I_im,neg_zero,add_zero,zero_add]
      nlinarith only [sq_nonneg x,hy,sq_nonneg (y-1)]
    · change |(point x y).re| ≤ 1/2
      simpa only [point,Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,
        Complex.ofReal_im,neg_zero,add_zero] using
        abs_le.mpr ⟨by have hl : -1/2 < x := hx.1; linarith, hx.2⟩
  change fullAngular q b (ofComplex (point x y))=particular q b y+globalResponse q b (ofComplex (point x y))
  rw [ofComplex_apply_of_im_pos hpos]
  change fullAngular q b z=particular q b y+globalResponse q b z
  rw [fullAngular,globalCuspCutoff_eq_on_fd q b z hfd,hcoord]
  have hc : cutoff ![x,y]=1 := by
    change ((Real.smoothTransition (y-2):ℝ):ℂ)=1
    rw [Real.smoothTransition.one_of_one_le (by linarith)]
    rfl
  rw [cutoffResponse,hc,one_mul]
  rfl

private theorem particular_hasDerivAt (q : XiZeroCopy) (b : Bool) (y : Ioi (3:ℝ)) :
    HasDerivAt (particular q b) (deriv (particular q b) y) y := by
  have hy0 : 0 < y.val := lt_trans (by norm_num) y.2
  have h := (slice_vertical_derivative (fullPlanar q b) (full_smooth q b) 0 hy0).sub
    (slice_vertical_derivative (responsePlanar q b) (responsePlanar_smooth q b) 0 hy0)
  have hp : HasDerivAt (particular q b)
      (vertical (fullPlanar q b) (point 0 y)-vertical (responsePlanar q b) (point 0 y)) y := by
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds y.2] with t ht
    have he := full_cusp_value q b (x := 0) (by norm_num [cell]) ht
    change particular q b t=fullPlanar q b (point 0 t)-responsePlanar q b (point 0 t)
    rw [he,add_sub_cancel_right]
  exact hp.differentiableAt.hasDerivAt

private theorem full_cusp_vertical (q : XiZeroCopy) (b : Bool) {x : ℝ}
    (hx : x ∈ cell) (y : Ioi (3:ℝ)) :
    vertical (fullPlanar q b) (point x y)=
      deriv (particular q b) y+vertical (responsePlanar q b) (point x y) := by
  have hy0 : 0 < y.val := lt_trans (by norm_num) y.2
  have hs := (particular_hasDerivAt q b y).add
    (slice_vertical_derivative (responsePlanar q b) (responsePlanar_smooth q b) x hy0)
  have h : HasDerivAt (fun t => fullPlanar q b (point x t))
      (deriv (particular q b) y+vertical (responsePlanar q b) (point x y)) y := by
    apply hs.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds y.2] with t ht
    exact full_cusp_value q b hx ht
  exact (slice_vertical_derivative (fullPlanar q b) (full_smooth q b) x hy0).unique h

private theorem mean_const (c : ℂ) : (∫ _x in cell,c)=c := by
  change (∫ _x in Ioc (-1/2:ℝ) (1/2),c)=c
  rw [← intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2)]
  rw [intervalIntegral.integral_const]
  norm_num

private theorem fullMean_decomposition (q : XiZeroCopy) (b : Bool) (y : Ioi (3:ℝ)) :
    fullMean q b y=particular q b y+responseMean q b y := by
  have hy0 : 0 < y.val := lt_trans (by norm_num) y.2
  have hr : IntegrableOn (fun x => responsePlanar q b (point x y)) cell :=
    (slice_continuous _ (responsePlanar_smooth q b) hy0).integrableOn_Ioc
  have hc : IntegrableOn (fun _x : ℝ => particular q b y) cell := by
    change IntegrableOn (fun _x : ℝ => particular q b y) (Ioc (-1/2:ℝ) (1/2))
    exact integrable_const _
  change (∫ x in cell,fullPlanar q b (point x y))=particular q b y+responseMean q b y
  calc
    _ = ∫ x in cell,particular q b y+responsePlanar q b (point x y) := by
      exact setIntegral_congr_fun measurableSet_Ioc (fun x hx => full_cusp_value q b hx y.2)
    _ = _ := by rw [integral_add hc hr,mean_const]; rfl

private theorem fullMean_derivative (q : XiZeroCopy) (b : Bool) (y : Ioi (3:ℝ)) :
    deriv (fullMean q b) y=deriv (particular q b) y+deriv (responseMean q b) y := by
  have hy0 : 0 < y.val := lt_trans (by norm_num) y.2
  have hr := (average_hasDerivAt (responsePlanar q b) (responsePlanar_smooth q b) hy0).differentiableAt.hasDerivAt
  have h := (particular_hasDerivAt q b y).add hr
  have hm : HasDerivAt (fullMean q b)
      (deriv (particular q b) y+deriv (responseMean q b) y) y := by
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds y.2] with t ht
    exact fullMean_decomposition q b ⟨t,ht⟩
  exact hm.deriv

/-- Original coordinate current built from both complete constructed response fields. -/
def fullCuspFlux (q : XiZeroCopy) (a b : Bool) (y : ℝ) : ℂ :=
  D4BMCuspProjection.mean (fun x => coordDeriv 1 (fullAngularField q a) ![x,y]*fullAngularField q b ![x,y])

private theorem fullCuspFlux_planar (q : XiZeroCopy) (a b : Bool) (y : ℝ) :
    fullCuspFlux q a b y=average (fun z => vertical (fullPlanar q a) z*fullPlanar q b z) y := by
  change (∫ x in cell,coordDeriv 1 (fullAngularField q a) ![x,y]*fullAngularField q b ![x,y])=
    ∫ x in cell,vertical (fullPlanar q a) (point x y)*fullPlanar q b (point x y)
  apply integral_congr_ae
  filter_upwards with x
  rw [vertical_full_field]
  congr 1

/-- The source particular responses change the full means but leave exactly the
native nonconstant current in the original complete coordinate flux. -/
theorem fullCuspFlux_decomposition (q : XiZeroCopy) (a b : Bool) (y : Ioi (3:ℝ)) :
    fullCuspFlux q a b y=deriv (fullMean q a) y*fullMean q b y+nativePairCurrent q a b y := by
  have hy0 : 0 < y.val := lt_trans (by norm_num) y.2
  have hv : ContDiffOn ℝ ∞ (vertical (responsePlanar q a)) {z : ℂ | 0 < z.im} :=
    planar_derivative_contDiffOn (responsePlanar_smooth q a) Complex.I
  have hr : Continuous (fun x => responsePlanar q b (point x y)) :=
    slice_continuous _ (responsePlanar_smooth q b) hy0
  have hd : Continuous (fun x => vertical (responsePlanar q a) (point x y)) :=
    slice_continuous _ hv hy0
  let A := deriv (particular q a) y
  let B := particular q b y
  have h0 : IntegrableOn (fun _x : ℝ => A*B) cell := by
    change IntegrableOn (fun _x : ℝ => A*B) (Ioc (-1/2:ℝ) (1/2))
    exact integrable_const _
  have h1 : IntegrableOn (fun x => A*responsePlanar q b (point x y)) cell := (hr.const_mul A).integrableOn_Ioc
  have h2 : IntegrableOn (fun x => vertical (responsePlanar q a) (point x y)*B) cell := (hd.mul_const B).integrableOn_Ioc
  have h3 : IntegrableOn (fun x => vertical (responsePlanar q a) (point x y)*responsePlanar q b (point x y)) cell :=
    (hd.mul hr).integrableOn_Ioc
  have h01 : IntegrableOn (fun x => A*B+A*responsePlanar q b (point x y)) cell := h0.add h1
  have h012 : IntegrableOn (fun x => A*B+A*responsePlanar q b (point x y)+vertical (responsePlanar q a) (point x y)*B) cell := h01.add h2
  have he : fullCuspFlux q a b y=A*B+A*responseMean q b y+deriv (responseMean q a) y*B+nativeCuspFlux q a b y := by
    rw [fullCuspFlux_planar]
    change (∫ x in cell,vertical (fullPlanar q a) (point x y)*fullPlanar q b (point x y))=_
    calc
      _ = ∫ x in cell,A*B+A*responsePlanar q b (point x y)+
          vertical (responsePlanar q a) (point x y)*B+vertical (responsePlanar q a) (point x y)*responsePlanar q b (point x y) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        dsimp only
        rw [full_cusp_vertical q a hx y,full_cusp_value q b hx y.2]
        dsimp only [A,B]
        ring
      _ = _ := by
        rw [integral_add h012 h3,integral_add h01 h2,integral_add h0 h1,mean_const,
          integral_const_mul,integral_mul_const]
        have hm := (average_hasDerivAt (responsePlanar q a) (responsePlanar_smooth q a) hy0).deriv
        change deriv (responseMean q a) y=average (vertical (responsePlanar q a)) y at hm
        change A*B+A*responseMean q b y+average (vertical (responsePlanar q a)) y*B+nativeCuspFlux q a b y=_
        rw [← hm]
  rw [he,fullMean_decomposition q b y,fullMean_derivative q a y,nativeCuspFlux_decomposition q a b ⟨y.val,hy0⟩]
  dsimp only [A,B]
  ring

/-- Source-derived rapid upper trace for both complete response corrections,
retaining the original full mean and its derivative. -/
theorem fullCuspFlux_remainder_weighted_tendsto_zero (q : XiZeroCopy) (a b : Bool) (N : ℕ) :
    Tendsto (fun y : ℝ => (y:ℂ)^N*(fullCuspFlux q a b y-deriv (fullMean q a) y*fullMean q b y)) atTop (𝓝 0) := by
  apply (nativePairCurrent_weighted_tendsto_zero q a b N).congr'
  filter_upwards [eventually_gt_atTop (3:ℝ)] with y hy
  rw [fullCuspFlux_decomposition q a b ⟨y,hy⟩,add_sub_cancel_left]


open D4BMQuarticResponseWork D4BMQuarticTestedCurrentCusp

/-- Source contacts of the original complete incoming current, with all three
unchanged physical coefficients. -/
def completeContactCurrent (q : XiZeroCopy) (j : Fin 2) (w : Fin 2 → ℝ) : ℂ :=
  let p := D4BMModularCore.physicalRate q true*D4BMModularCore.physicalRate q false/3
  fullSquarePotential q w*
    ((sourceWorkWeights q 0-p*parameter q false)*coordDeriv j (fullAngularField q true) w+
      (sourceWorkWeights q 1+p*parameter q true)*coordDeriv j (fullAngularField q false) w+
      (2*sourceWorkWeights q 2/3)*coordDeriv j (fullSquarePotential q) w)

/-- The original source weights cancel exactly their Green-contact pieces;
the surviving three coefficients are fixed by the two physical rates. -/
theorem completeContactCurrent_source (q : XiZeroCopy) (j : Fin 2) (w : Fin 2 → ℝ) :
    let s := D4BMModularCore.physicalRate q true
    let t := D4BMModularCore.physicalRate q false
    let ds := s*(s-1)/4
    let dt := t*(t-1)/4
    completeContactCurrent q j w=fullSquarePotential q w*
      ((-2*s*dt*((t+1)^2-s*t))*coordDeriv j (fullAngularField q true) w+
        (2*t*ds*((s+1)^2-s*t))*coordDeriv j (fullAngularField q false) w+
        (4*ds*dt*(s-t)*(1-s*t)/3)*coordDeriv j (fullSquarePotential q) w) := by
  dsimp only
  simp only [completeContactCurrent,sourceWorkWeights,parameter_physicalRate,
    D4BMQuadraticMixedSource.resolventParameter,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Matrix.cons_val_succ]
  ring

private theorem completeCurrent_split (q : XiZeroCopy) (j : Fin 2) (w : Fin 2 → ℝ) :
    completeCurrent q j w=
      -(D4BMModularCore.physicalRate q true*D4BMModularCore.physicalRate q false/3)*
        (parameter q false*(coordDeriv j (fullAngularField q true) w*fullAngularField q false w)-
          parameter q true*(coordDeriv j (fullAngularField q false) w*fullAngularField q true w))+
      completeContactCurrent q j w := by
  change -(D4BMModularCore.physicalRate q true*D4BMModularCore.physicalRate q false/3)*
      (parameter q false*coordDeriv j (fullAngularField q true) w*
        (fullAngularField q false w+fullSquarePotential q w)-
      parameter q true*coordDeriv j (fullAngularField q false) w*
        (fullAngularField q true w+fullSquarePotential q w))+
    fullSquarePotential q w*(sourceWorkWeights q 0*coordDeriv j (fullAngularField q true) w+
      sourceWorkWeights q 1*coordDeriv j (fullAngularField q false) w+
      (2*sourceWorkWeights q 2/3)*coordDeriv j (fullSquarePotential q) w)=_
  dsimp only [completeContactCurrent]
  ring

private theorem coordinate_slice_continuous (F : (Fin 2 → ℝ) → ℂ)
    (hF : ∀ w, 0 < w 1 → ContinuousAt F w) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => F ![x,y]) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact ContinuousAt.comp (f := fun t : ℝ => ![t,y]) (x := x)
    (hF ![x,y] hy) (by fun_prop)

private theorem full_slice (q : XiZeroCopy) (b : Bool) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => fullAngularField q b ![x,y]) :=
  coordinate_slice_continuous _ (fun w hw => (fullAngularField_smooth q b w hw).continuousAt) hy

private theorem vertical_full_slice (q : XiZeroCopy) (b : Bool) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => coordDeriv 1 (fullAngularField q b) ![x,y]) := by
  apply coordinate_slice_continuous _ _ hy
  intro w hw
  exact (ScalarTwoJet.coordDeriv_hasFDerivAt
    ((contDiffAt_infty.mp (fullAngularField_smooth q b w hw)) 2) 1).continuousAt

private theorem contact_slice (q : XiZeroCopy) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => completeContactCurrent q 1 ![x,y]) := by
  have hQ : Continuous (fun x : ℝ => fullSquarePotential q ![x,y]) :=
    coordinate_slice_continuous _ (fun w hw => (fullSquarePotential_smooth q w hw 1).continuousAt) hy
  have hdQ : Continuous (fun x : ℝ => coordDeriv 1 (fullSquarePotential q) ![x,y]) :=
    coordinate_slice_continuous _ (fun w hw =>
      (ScalarTwoJet.coordDeriv_hasFDerivAt (fullSquarePotential_smooth q w hw 2) 1).continuousAt) hy
  exact hQ.mul (((vertical_full_slice q true hy).const_mul _).add
    ((vertical_full_slice q false hy).const_mul _) |>.add (hdQ.const_mul _))

/-- Original finite-cell mean of the complete incoming current before its scalar test. -/
def completeCuspMean (q : XiZeroCopy) (y : ℝ) : ℂ :=
  D4BMCuspProjection.mean (fun x => completeCurrent q 1 ![x,y])

/-- All original source contacts retained in the same cusp cell. -/
def completeCuspContact (q : XiZeroCopy) (y : ℝ) : ℂ :=
  D4BMCuspProjection.mean (fun x => completeContactCurrent q 1 ![x,y])

/-- Contribution of the full constructed response means at their unchanged rates. -/
def fullMeanCurrent (q : XiZeroCopy) (y : ℝ) : ℂ :=
  -(D4BMModularCore.physicalRate q true*D4BMModularCore.physicalRate q false/3)*
    (parameter q false*(deriv (fullMean q true) y*fullMean q false y)-
      parameter q true*(deriv (fullMean q false) y*fullMean q true y))

/-- Exact source-cell decomposition of the original complete incoming current.
Both full response means, all source contacts, and both ordered covariances remain. -/
theorem completeCuspMean_decomposition (q : XiZeroCopy) (y : Ioi (3:ℝ)) :
    completeCuspMean q y=fullMeanCurrent q y+completeCuspContact q y+
      (-(D4BMModularCore.physicalRate q true*D4BMModularCore.physicalRate q false/3))*
        (parameter q false*nativePairCurrent q true false y-
          parameter q true*nativePairCurrent q false true y) := by
  have hy0 : 0 < y.val := lt_trans (by norm_num) y.2
  let A := fun x : ℝ => coordDeriv 1 (fullAngularField q true) ![x,y]*fullAngularField q false ![x,y]
  let B := fun x : ℝ => coordDeriv 1 (fullAngularField q false) ![x,y]*fullAngularField q true ![x,y]
  let c := -(D4BMModularCore.physicalRate q true*D4BMModularCore.physicalRate q false/3)
  have hA : IntegrableOn A cell := ((vertical_full_slice q true hy0).mul (full_slice q false hy0)).integrableOn_Ioc
  have hB : IntegrableOn B cell := ((vertical_full_slice q false hy0).mul (full_slice q true hy0)).integrableOn_Ioc
  have hC : IntegrableOn (fun x : ℝ => completeContactCurrent q 1 ![x,y]) cell :=
    (contact_slice q hy0).integrableOn_Ioc
  have hPA : IntegrableOn (fun x => parameter q false*A x) cell := hA.const_mul _
  have hPB : IntegrableOn (fun x => parameter q true*B x) cell := hB.const_mul _
  have hAB : IntegrableOn (fun x => parameter q false*A x-parameter q true*B x) cell := hPA.sub hPB
  have hS : IntegrableOn (fun x => c*(parameter q false*A x-parameter q true*B x)) cell := hAB.const_mul c
  have he : completeCuspMean q y=
      c*(parameter q false*fullCuspFlux q true false y-parameter q true*fullCuspFlux q false true y)+
        completeCuspContact q y := by
    change (∫ x in cell,completeCurrent q 1 ![x,y])=_
    calc
      _ = ∫ x in cell,c*(parameter q false*A x-parameter q true*B x)+completeContactCurrent q 1 ![x,y] := by
        apply integral_congr_ae
        filter_upwards with x
        exact completeCurrent_split q 1 ![x,y]
      _ = _ := by
        rw [integral_add hS hC,
          integral_const_mul,integral_sub hPA hPB,
          integral_const_mul,integral_const_mul]
        rfl
  rw [he,fullCuspFlux_decomposition q true false y,fullCuspFlux_decomposition q false true y]
  dsimp only [fullMeanCurrent,c]
  ring

/-- The original complete current has no additional polynomially weighted cusp
trace beyond its full response means and its explicitly retained source contacts. -/
theorem completeCuspMean_remainder_weighted_tendsto_zero (q : XiZeroCopy) (N : ℕ) :
    Tendsto (fun y : ℝ => (y:ℂ)^N*
      (completeCuspMean q y-fullMeanCurrent q y-completeCuspContact q y)) atTop (𝓝 0) := by
  let c := -(D4BMModularCore.physicalRate q true*D4BMModularCore.physicalRate q false/3)
  have h := (((nativePairCurrent_weighted_tendsto_zero q true false N).const_mul (parameter q false)).sub
    ((nativePairCurrent_weighted_tendsto_zero q false true N).const_mul (parameter q true))).const_mul c
  simp only [mul_zero,sub_self] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (3:ℝ)] with y hy
  rw [completeCuspMean_decomposition q ⟨y,hy⟩]
  dsimp only [c]
  ring


private theorem cpow_remainder_tendsto_zero (f : ℝ → ℂ)
    (hf : ∀ N : ℕ, Tendsto (fun y : ℝ => (y:ℂ)^N*f y) atTop (𝓝 0)) (w : ℂ) :
    Tendsto (fun y : ℝ => (y:ℂ)^w*f y) atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := exists_nat_gt w.re
  have h := (hf N).norm
  simp only [norm_zero] at h
  apply squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy0,norm_mul,norm_pow,
    Complex.norm_of_nonneg hy0.le]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hy hN.le

/-- Every original complex height power preserves the vanishing covariance
remainder of the complete response product. -/
theorem fullCuspFlux_remainder_cpow_tendsto_zero (q : XiZeroCopy) (a b : Bool) (w : ℂ) :
    Tendsto (fun y : ℝ => (y:ℂ)^w*
      (fullCuspFlux q a b y-deriv (fullMean q a) y*fullMean q b y)) atTop (𝓝 0) :=
  cpow_remainder_tendsto_zero _ (fullCuspFlux_remainder_weighted_tendsto_zero q a b) w

/-- Complex height weights leave exactly the full-mean and source-contact
contributions in the original complete incoming cusp current. -/
theorem completeCuspMean_remainder_cpow_tendsto_zero (q : XiZeroCopy) (w : ℂ) :
    Tendsto (fun y : ℝ => (y:ℂ)^w*
      (completeCuspMean q y-fullMeanCurrent q y-completeCuspContact q y)) atTop (𝓝 0) :=
  cpow_remainder_tendsto_zero _ (completeCuspMean_remainder_weighted_tendsto_zero q) w

/-- The original physical scalar principal part annihilates the proven
nonconstant remainder; its full theta tail is retained as a separate term. -/
theorem physicalPrincipal_remainder_tendsto_zero (q : XiZeroCopy) :
    Tendsto (fun y : ℝ => principal (D4BMJointSource.physicalAngularParameter q) ![0,y]*
      (completeCuspMean q y-fullMeanCurrent q y-completeCuspContact q y)) atTop (𝓝 0) := by
  have h := (completeCuspMean_remainder_cpow_tendsto_zero q (1-(q.1:ℂ)/2)).const_mul
    (reflectedCompletedLambda ((q.1:ℂ)-1))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards with y
  rw [D4BMJointSource.physicalScalar_principal]
  change _=(reflectedCompletedLambda ((q.1:ℂ)-1)*(y:ℂ)^(1-(q.1:ℂ)/2))*_
  ring

end
end RHTower.D4BMQuarticFullResponseCurrent
