import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticNativeCuspCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalVerticalAdmission

/-!
# Complete physical scalar test on the centered native response current

The original forced response equation and literal period-one source matching
produce a six-term bilinear current law. Both derivatives of the physical test,
the changing inverse-square metric weight and the complete forcing remain.
The original Fourier formulas bound the full test and its first derivatives.
Centered Young and native Parseval estimates then admit the current and its
actual derivative under every polynomial height weight, proving zero upper
cusp trace under every complex height power.

The original tested moment is restored with both response means and both
linear tested moments. The full six-term integral retains the negative lower
endpoint. This does not cancel those restored terms, source contacts, other
physical boundary faces or the complete left-QNM action. The source-predeclared
physical parameter and common Hawking clock are unchanged.
-/

open scoped ContDiff
open MeasureTheory Set Filter Topology UpperHalfPlane
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.SelbergMaassMean
open GaloisForLFunctions.RHTower.SelbergMaassFourier
open GaloisForLFunctions.RHTower.SelbergMaassParseval
namespace RHTower.D4BMQuarticTestedNativeCurrent
open D4BMModularCore D4BMGlobalAngularResponse D4BMQuarticNativeCuspModes
open D4BMQuarticNativeCuspComparison D4BMQuarticNativeCuspEnergy
noncomputable section
set_option autoImplicit false
private theorem directional_smooth {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im}) (v : ℂ) :
    ContDiffOn ℝ ∞ (directional v F) {z : ℂ | 0 < z.im} :=
  planar_derivative_contDiffOn hf v

private def cell : Set ℝ := Ioc 0 1
private def cellMean (f : ℝ → ℂ) : ℂ := ∫ x in cell, f x
private def cellVariance (f : ℝ → ℂ) : ℝ :=
  (∫ x in cell, Complex.normSq (f x))-Complex.normSq (cellMean f)

private theorem cell_integrable {f : ℝ → ℂ} (hf : Continuous f) : IntegrableOn f cell :=
  hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self

private theorem cell_normSq_integrable {f : ℝ → ℂ} (hf : Continuous f) :
    IntegrableOn (fun x => Complex.normSq (f x)) cell := by
  have h : IntegrableOn (fun x => ‖f x‖ ^ 2) (Ioc 0 1) :=
    (hf.norm.pow 2).integrableOn_Ioc
  simpa only [cell,Complex.normSq_eq_norm_sq] using h

private theorem cell_const_real (c : ℝ) : (∫ _x in cell, c)=c := by
  change (∫ _x in Ioc (0:ℝ) 1, c)=c
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  simp only [intervalIntegral.integral_const,sub_zero,one_smul]

private theorem cell_centered_square {f : ℝ → ℂ} (hf : Continuous f) :
    (∫ x in cell, Complex.normSq (f x-cellMean f))=cellVariance f := by
  let a := cellMean f
  have hi := cell_normSq_integrable hf
  have hr := cell_integrable (hf.mul_const ((starRingEnd ℂ) a))
  have hj : IntegrableOn (fun x => 2*(f x*(starRingEnd ℂ) a).re) cell := hr.re.const_mul 2
  have hc : IntegrableOn (fun _ : ℝ => Complex.normSq a) cell :=
    (continuous_const : Continuous (fun _ : ℝ => Complex.normSq a)).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have he : (∫ x in cell, (f x*(starRingEnd ℂ) a).re)=Complex.normSq a := by
    change (∫ x in cell, RCLike.re (f x*(starRingEnd ℂ) a))=Complex.normSq a
    rw [integral_re hr,integral_mul_const]
    change (a*(starRingEnd ℂ) a).re=Complex.normSq a
    simp only [Complex.mul_conj,Complex.ofReal_re]
  calc
    _ = ∫ x in cell, Complex.normSq (f x)+Complex.normSq a-2*(f x*(starRingEnd ℂ) a).re := by
      apply setIntegral_congr_fun (show MeasurableSet cell from measurableSet_Ioc)
      intro x _
      exact Complex.normSq_sub (f x) a
    _ = (∫ x in cell, Complex.normSq (f x))+Complex.normSq a-2*Complex.normSq a := by
      have hsum : IntegrableOn (fun x => Complex.normSq (f x)+Complex.normSq a) cell := hi.add hc
      rw [integral_sub hsum hj, integral_add hi hc,
        cell_const_real,integral_const_mul,he]
    _ = cellVariance f := by dsimp only [cellVariance,a]; ring


private def mean (F : ℂ → ℂ) (y : ℝ) : ℂ := cellMean (fun x => F (point x y))

private theorem mean_eq_coefficient (F : ℂ → ℂ) : mean F=coefficient 1 0 F := by
  funext y
  simp only [coefficient,deningerFourierCoeff,deningerFourierKernel,Int.cast_zero,
    mul_zero,zero_mul,neg_zero,Complex.exp_zero,Complex.ofReal_one,div_one,one_mul]
  change (∫ x in Ioc (0:ℝ) 1,F (point x y))=∫ x in (0:ℝ)..1,F (point x y)
  exact (intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)).symm

private theorem mean_slice_congr {F G : ℂ → ℂ} {y : ℝ}
    (h : ∀ x : ℝ,F (point x y)=G (point x y)) : mean F y=mean G y :=
  integral_congr_ae (Filter.Eventually.of_forall h)

private theorem mean_add {F G : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im})
    (hg : ContinuousOn G {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    mean (fun z => F z+G z) y=mean F y+mean G y :=
  integral_add (cell_integrable (slice_continuous hf hy)) (cell_integrable (slice_continuous hg hy))

private theorem mean_sub {F G : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im})
    (hg : ContinuousOn G {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    mean (fun z => F z-G z) y=mean F y-mean G y :=
  integral_sub (cell_integrable (slice_continuous hf hy)) (cell_integrable (slice_continuous hg hy))

private theorem mean_mul_const (F : ℂ → ℂ) (c : ℂ) (y : ℝ) :
    mean (fun z => F z*c) y=mean F y*c := integral_mul_const _ _

private theorem mean_const_mul (F : ℂ → ℂ) (c : ℂ) (y : ℝ) :
    mean (fun z => c*F z) y=c*mean F y := integral_const_mul _ _

private theorem mean_hasDerivAt {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (mean F) (mean (directional Complex.I F) y) y := by
  simpa only [mean_eq_coefficient] using coefficient_hasDerivAt 1 (by norm_num) 0
    (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hy

private theorem vertical_product {F G : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im})
    (hg : ContDiffOn ℝ ∞ G {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    directional Complex.I (fun z => F z*G z) (point x y)=
      directional Complex.I F (point x y)*G (point x y)+F (point x y)*directional Complex.I G (point x y) := by
  have hf1 := hf.of_le (show (1 : WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)
  have hg1 := hg.of_le (show (1 : WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)
  exact (slice_vertical (hf1.mul hg1) x hy).unique
    ((slice_vertical hf1 x hy).mul (slice_vertical hg1 x hy))

private theorem mean_product_hasDerivAt {F G : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im})
    (hg : ContDiffOn ℝ ∞ G {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (mean (fun z => F z*G z))
      (mean (fun z => directional Complex.I F z*G z) y+
        mean (fun z => F z*directional Complex.I G z) y) y := by
  apply (mean_hasDerivAt (hf.mul hg) hy).congr_deriv
  have he : mean (directional Complex.I (fun z => F z*G z)) y=
      mean (fun z => directional Complex.I F z*G z+F z*directional Complex.I G z) y :=
    mean_slice_congr (fun x => vertical_product hf hg hy x)
  rw [he,mean_add (F := fun z => directional Complex.I F z*G z)
      (G := fun z => F z*directional Complex.I G z)
      ((directional_smooth hf Complex.I).continuousOn.mul hg.continuousOn)
      (hf.continuousOn.mul (directional_smooth hg Complex.I).continuousOn) hy]

private theorem mean_triple_hasDerivAt {T F G : ℂ → ℂ}
    (ht : ContDiffOn ℝ ∞ T {z : ℂ | 0 < z.im})
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im})
    (hg : ContDiffOn ℝ ∞ G {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (mean (fun z => T z*F z*G z))
      (mean (fun z => directional Complex.I T z*F z*G z) y+
        mean (fun z => T z*directional Complex.I F z*G z) y+
        mean (fun z => T z*F z*directional Complex.I G z) y) y := by
  apply (mean_product_hasDerivAt (ht.mul hf) hg hy).congr_deriv
  have he : mean (fun z => directional Complex.I (fun w => T w*F w) z*G z) y=
      mean (fun z => (directional Complex.I T z*F z)*G z+(T z*directional Complex.I F z)*G z) y := by
    apply mean_slice_congr
    intro x
    rw [vertical_product ht hf hy x]
    ring
  rw [he,mean_add (F := fun z => directional Complex.I T z*F z*G z)
    (G := fun z => T z*directional Complex.I F z*G z)
    (((directional_smooth ht Complex.I).continuousOn.mul hf.continuousOn).mul hg.continuousOn)
    ((ht.continuousOn.mul (directional_smooth hf Complex.I).continuousOn).mul hg.continuousOn) hy]

/-- Period-one bilinear covariance with the entire spatial test retained. -/
def weightedCovariance (T F G : ℂ → ℂ) (y : ℝ) : ℂ :=
  coefficient 1 0 (fun z => T z*F z*G z) y-
    coefficient 1 0 F y*coefficient 1 0 (fun z => T z*G z) y-
    coefficient 1 0 G y*coefficient 1 0 (fun z => T z*F z) y+
    coefficient 1 0 F y*coefficient 1 0 G y*coefficient 1 0 T y

private theorem weightedCovariance_mean (T F G : ℂ → ℂ) (y : ℝ) :
    weightedCovariance T F G y=mean (fun z => T z*F z*G z) y-
      mean F y*mean (fun z => T z*G z) y-mean G y*mean (fun z => T z*F z) y+
      mean F y*mean G y*mean T y := by
  simp only [mean_eq_coefficient,weightedCovariance]

private theorem weightedCovariance_centered {T F G : ℂ → ℂ}
    (ht : ContinuousOn T {z : ℂ | 0 < z.im})
    (hf : ContinuousOn F {z : ℂ | 0 < z.im})
    (hg : ContinuousOn G {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    weightedCovariance T F G y=
      ∫ x in cell,T (point x y)*(F (point x y)-mean F y)*(G (point x y)-mean G y) := by
  let a := mean F y
  let b := mean G y
  have he : (fun z => T z*(F z-a)*(G z-b))=
      (fun z => ((T z*F z*G z)-(T z*G z)*a)-(T z*F z)*b+T z*(a*b)) := by
    funext z; ring
  change weightedCovariance T F G y=mean (fun z => T z*(F z-a)*(G z-b)) y
  rw [weightedCovariance_mean,he,
    mean_add (F := fun z => (T z*F z*G z-(T z*G z)*a)-(T z*F z)*b)
      (G := fun z => T z*(a*b))
      (((ht.mul hf).mul hg).sub ((ht.mul hg).mul_const a) |>.sub ((ht.mul hf).mul_const b))
      (ht.mul_const (a*b)) hy,
    mean_sub (F := fun z => T z*F z*G z-(T z*G z)*a) (G := fun z => (T z*F z)*b)
      (((ht.mul hf).mul hg).sub ((ht.mul hg).mul_const a)) ((ht.mul hf).mul_const b) hy,
    mean_sub (F := fun z => T z*F z*G z) (G := fun z => (T z*G z)*a)
      ((ht.mul hf).mul hg) ((ht.mul hg).mul_const a) hy,
    mean_mul_const,mean_mul_const,mean_mul_const]
  dsimp only [a,b]
  ring

private theorem weightedCovariance_hasDerivAt {T F G : ℂ → ℂ}
    (ht : ContDiffOn ℝ ∞ T {z : ℂ | 0 < z.im})
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im})
    (hg : ContDiffOn ℝ ∞ G {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (weightedCovariance T F G)
      (weightedCovariance (directional Complex.I T) F G y+
        weightedCovariance T (directional Complex.I F) G y+
        weightedCovariance T F (directional Complex.I G) y) y := by
  have h := (((mean_triple_hasDerivAt ht hf hg hy).sub
    ((mean_hasDerivAt hf hy).mul (mean_product_hasDerivAt ht hg hy))).sub
    ((mean_hasDerivAt hg hy).mul (mean_product_hasDerivAt ht hf hy))).add
    (((mean_hasDerivAt hf hy).mul (mean_hasDerivAt hg hy)).mul (mean_hasDerivAt ht hy))
  have he : weightedCovariance T F G=(fun t => mean (fun z => T z*F z*G z) t-
      mean F t*mean (fun z => T z*G z) t-mean G t*mean (fun z => T z*F z) t+
      mean F t*mean G t*mean T t) := funext (weightedCovariance_mean T F G)
  rw [he]
  apply h.congr_deriv
  simp only [weightedCovariance_mean,Pi.mul_apply]
  ring


private theorem mean_linear {F G : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im})
    (hg : ContinuousOn G {z : ℂ | 0 < z.im}) (c d : ℂ)
    {y : ℝ} (hy : 0 < y) :
    mean (fun z => c*F z+d*G z) y=c*mean F y+d*mean G y := by
  rw [mean_add (F := fun z => c*F z) (G := fun z => d*G z)
    (hf.const_mul c) (hg.const_mul d) hy,mean_const_mul,mean_const_mul]

private theorem weightedCovariance_linear_left {T F G H : ℂ → ℂ}
    (ht : ContinuousOn T {z : ℂ | 0 < z.im})
    (hf : ContinuousOn F {z : ℂ | 0 < z.im})
    (hg : ContinuousOn G {z : ℂ | 0 < z.im})
    (hh : ContinuousOn H {z : ℂ | 0 < z.im}) (c d : ℂ)
    {y : ℝ} (hy : 0 < y) :
    weightedCovariance T (fun z => c*F z+d*G z) H y=
      c*weightedCovariance T F H y+d*weightedCovariance T G H y := by
  have he0 : (fun z => T z*(c*F z+d*G z)*H z)=
      (fun z => c*(T z*F z*H z)+d*(T z*G z*H z)) := by funext z; ring
  have he1 : (fun z => T z*(c*F z+d*G z))=
      (fun z => c*(T z*F z)+d*(T z*G z)) := by funext z; ring
  simp only [weightedCovariance_mean]
  rw [he0,he1,mean_linear (F := fun z => T z*F z*H z) (G := fun z => T z*G z*H z)
    ((ht.mul hf).mul hh) ((ht.mul hg).mul hh) c d hy,
    mean_linear hf hg c d hy,
    mean_linear (F := fun z => T z*F z) (G := fun z => T z*G z) (ht.mul hf) (ht.mul hg) c d hy]
  ring

private theorem weightedCovariance_slice_congr {T F G H : ℂ → ℂ} {y : ℝ}
    (he : ∀ x : ℝ, F (point x y)=G (point x y)) :
    weightedCovariance T F H y=weightedCovariance T G H y := by
  have h0 : mean F y=mean G y := mean_slice_congr he
  have h1 : mean (fun z => T z*F z*H z) y=mean (fun z => T z*G z*H z) y := by
    apply mean_slice_congr
    intro x
    rw [he x]
  have h2 : mean (fun z => T z*F z) y=mean (fun z => T z*G z) y := by
    apply mean_slice_congr
    intro x
    rw [he x]
  simp only [weightedCovariance_mean,h0,h1,h2]

private theorem weightedCovariance_horizontal_second {T F G : ℂ → ℂ}
    (ht : ContDiffOn ℝ ∞ T {z : ℂ | 0 < z.im})
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im})
    (hg : ContDiffOn ℝ ∞ G {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y)
    (pt : ∀ x, T (point (x+1) y)=T (point x y))
    (pf : ∀ x, F (point (x+1) y)=F (point x y))
    (pg : ∀ x, G (point (x+1) y)=G (point x y)) :
    weightedCovariance T (directional 1 (directional 1 F)) G y=
      -weightedCovariance T (directional 1 F) (directional 1 G) y-
        weightedCovariance (directional 1 T) (directional 1 F) G y := by
  have ht1 := ht.of_le (show (1 : WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)
  have hf1 := hf.of_le (show (1 : WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)
  have hg1 := hg.of_le (show (1 : WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)
  have htx := directional_smooth ht (1:ℂ)
  have hfx := directional_smooth hf (1:ℂ)
  have hfxx := directional_smooth hfx (1:ℂ)
  have hgx := directional_smooth hg (1:ℂ)
  have hfx1 := hfx.of_le (show (1 : WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)
  have ct := slice_continuous ht.continuousOn hy
  have ctx := slice_continuous htx.continuousOn hy
  have cfx := slice_continuous hfx.continuousOn hy
  have cfxx := slice_continuous hfxx.continuousOn hy
  have cg := slice_continuous hg.continuousOn hy
  have cgx := slice_continuous hgx.continuousOn hy
  let m := mean G y
  let A := fun x => T (point x y)*directional 1 (directional 1 F) (point x y)*(G (point x y)-m)
  let B := fun x => T (point x y)*directional 1 F (point x y)*directional 1 G (point x y)
  let C := fun x => directional 1 T (point x y)*directional 1 F (point x y)*(G (point x y)-m)
  have hA : IntegrableOn A cell := cell_integrable ((ct.mul cfxx).mul (cg.sub continuous_const))
  have hB : IntegrableOn B cell := cell_integrable ((ct.mul cfx).mul cgx)
  have hC : IntegrableOn C cell := cell_integrable ((ctx.mul cfx).mul (cg.sub continuous_const))
  have hd (x : ℝ) : HasDerivAt
      (fun t => T (point t y)*directional 1 F (point t y)*(G (point t y)-m))
      ((directional 1 T (point x y)*directional 1 F (point x y)+
        T (point x y)*directional 1 (directional 1 F) (point x y))*(G (point x y)-m)+
        T (point x y)*directional 1 F (point x y)*directional 1 G (point x y)) x :=
    ((slice_horizontal ht1 hy x).mul (slice_horizontal hfx1 hy x)).mul
      ((slice_horizontal hg1 hy x).sub_const m)
  have cd : Continuous (fun x =>
      (directional 1 T (point x y)*directional 1 F (point x y)+
        T (point x y)*directional 1 (directional 1 F) (point x y))*(G (point x y)-m)+
        T (point x y)*directional 1 F (point x y)*directional 1 G (point x y)) :=
    (((ctx.mul cfx).add (ct.mul cfxx)).mul (cg.sub continuous_const)).add ((ct.mul cfx).mul cgx)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
    (fun x _ => hd x) (cd.intervalIntegrable 0 1)
  have pt0 : T (point 1 y)=T (point 0 y) := by simpa only [zero_add] using pt 0
  have pf0 : directional 1 F (point 1 y)=directional 1 F (point 0 y) := by
    simpa only [zero_add] using directional_periodic hf1 hy 1 pf 0
  have pg0 : G (point 1 y)=G (point 0 y) := by simpa only [zero_add] using pg 0
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),pt0,pf0,pg0,sub_self] at hFTC
  have hi : (∫ x in cell,A x+B x+C x)=0 := by
    calc
      _ = ∫ x in cell,(directional 1 T (point x y)*directional 1 F (point x y)+
          T (point x y)*directional 1 (directional 1 F) (point x y))*(G (point x y)-m)+
          T (point x y)*directional 1 F (point x y)*directional 1 G (point x y) := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [A,B,C]
        ring
      _ = 0 := hFTC
  have hAB : IntegrableOn (fun x => A x+B x) cell := hA.add hB
  rw [integral_add hAB hC,integral_add hA hB] at hi
  have mf0 : mean (directional 1 F) y=0 := by
    rw [mean_eq_coefficient,coefficient_horizontal 1 (by norm_num) 0 hf1 hy pf]
    simp only [signedFrequency,Int.cast_zero,mul_zero,zero_div,Complex.ofReal_zero,zero_mul]
  have mg0 : mean (directional 1 G) y=0 := by
    rw [mean_eq_coefficient,coefficient_horizontal 1 (by norm_num) 0 hg1 hy pg]
    simp only [signedFrequency,Int.cast_zero,mul_zero,zero_div,Complex.ofReal_zero,zero_mul]
  have mff0 : mean (directional 1 (directional 1 F)) y=0 := by
    rw [mean_eq_coefficient,coefficient_horizontal_second 1 (by norm_num) 0
      (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hy pf]
    simp only [signedFrequency,Int.cast_zero,mul_zero,zero_div,Complex.ofReal_zero,
      zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,neg_zero,zero_mul]
  rw [weightedCovariance_centered ht.continuousOn hfxx.continuousOn hg.continuousOn hy,
    weightedCovariance_centered ht.continuousOn hfx.continuousOn hgx.continuousOn hy,
    weightedCovariance_centered htx.continuousOn hfx.continuousOn hg.continuousOn hy]
  simp only [mf0,mg0,mff0,sub_zero]
  change (∫ x in cell,A x)=-(∫ x in cell,B x)-(∫ x in cell,C x)
  linear_combination hi


open D4BMJointSource D4BMAngularSeries

/-- The complete original scalar test at the source-predeclared physical parameter. -/
def physicalTest (q : XiZeroCopy) (z : ℂ) : ℂ :=
  scalar (physicalAngularParameter q) (angularCoordinates z)

private theorem physicalTest_smooth (q : XiZeroCopy) :
    ContDiffOn ℝ ∞ (physicalTest q) {z : ℂ | 0 < z.im} := by
  intro z hz
  have h := (cuspLeg_contDiffOn .scalar (physicalAngularParameter q)).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds
      (show 0 < angularCoordinates z 1 from hz))
  exact (h.comp z angularCoordinates.contDiff.contDiffAt).contDiffWithinAt

private theorem physicalTest_periodic (q : XiZeroCopy) (y x : ℝ) :
    physicalTest q (point (x+1) y)=physicalTest q (point x y) := by
  have hp : Function.Periodic (scalar (physicalAngularParameter q)) ![1,0] := by
    intro z
    simpa [scalar,Pi.add_apply] using d4BM_completedEisensteinCuspLeg_scalar_periodic
      (physicalAngularParameter q) (z 1) (z 0)
  have hc : angularCoordinates (point (x+1) y)=angularCoordinates (point x y)+![1,0] := by
    ext i
    fin_cases i <;> norm_num [angularCoordinates,point,Pi.add_apply]
  exact (congrArg (scalar (physicalAngularParameter q)) hc).trans (hp _)

/-- The physical test remains inside the centered bilinear response current. -/
def testedPairCurrent (q : XiZeroCopy) (a b : Bool) (y : ℝ) : ℂ :=
  weightedCovariance (physicalTest q)
    (directional Complex.I (D4BMCuspResponse.responsePlanar q a))
    (D4BMCuspResponse.responsePlanar q b) y

/-- All six source and test contributions to the differentiated current. -/
def testedPairDensity (q : XiZeroCopy) (a b : Bool) (y : ℝ) : ℂ :=
  weightedCovariance (directional Complex.I (physicalTest q))
    (directional Complex.I (D4BMCuspResponse.responsePlanar q a))
    (D4BMCuspResponse.responsePlanar q b) y+
  weightedCovariance (physicalTest q)
    (directional Complex.I (D4BMCuspResponse.responsePlanar q a))
    (directional Complex.I (D4BMCuspResponse.responsePlanar q b)) y+
  weightedCovariance (physicalTest q)
    (directional 1 (D4BMCuspResponse.responsePlanar q a))
    (directional 1 (D4BMCuspResponse.responsePlanar q b)) y+
  weightedCovariance (directional 1 (physicalTest q))
    (directional 1 (D4BMCuspResponse.responsePlanar q a))
    (D4BMCuspResponse.responsePlanar q b) y+
  (parameter q a/(y:ℂ)^2)*weightedCovariance (physicalTest q)
    (D4BMCuspResponse.responsePlanar q a) (D4BMCuspResponse.responsePlanar q b) y+
  (1/(y:ℂ)^2)*weightedCovariance (physicalTest q)
    (globalForcing q a ∘ ofComplex) (D4BMCuspResponse.responsePlanar q b) y

/-- Source smoothness, periodicity and the original forced equation prove this
identity. No extinction, clock covariance, or current conservation is assumed. -/
theorem testedPairCurrent_hasDerivAt (q : XiZeroCopy) (a b : Bool) (y : Ioi (0:ℝ)) :
    HasDerivAt (testedPairCurrent q a b) (testedPairDensity q a b y) y := by
  let T := physicalTest q
  let F := D4BMCuspResponse.responsePlanar q a
  let G := D4BMCuspResponse.responsePlanar q b
  let S := globalForcing q a ∘ ofComplex
  have ht := physicalTest_smooth q
  have hf := D4BMCuspResponse.responsePlanar_smooth q a
  have hg := D4BMCuspResponse.responsePlanar_smooth q b
  have hs := (globalForcing_smooth q a).planar_contDiffOn
  have hv := directional_smooth hf Complex.I
  have hh := directional_smooth hf (1:ℂ)
  have hvv := directional_smooth hv Complex.I
  have hhh := directional_smooth hh (1:ℂ)
  have hp (x : ℝ) :
      directional Complex.I (directional Complex.I F) (point x y)+
        directional 1 (directional 1 F) (point x y) =
      (parameter q a/(y.val:ℂ)^2)*F (point x y)+(1/(y.val:ℂ)^2)*S (point x y) := by
    have hx : 0 < (point x y).im := by simpa only [point,Complex.add_im,
      Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] using (show 0 < y.val from y.2)
    have he := globalResponse_classical_planar q a (point x y) hx
    have he' : directional 1 (directional 1 F) (point x y)+
        directional Complex.I (directional Complex.I F) (point x y) =
        (parameter q a*F (point x y)+S (point x y))/(y.val:ℂ)^2 := by
      change (fderiv ℝ (fun w => fderiv ℝ (globalResponse q a ∘ ofComplex) w 1) (point x y) 1+
        fderiv ℝ (fun w => fderiv ℝ (globalResponse q a ∘ ofComplex) w Complex.I)
          (point x y) Complex.I) = _
      simpa only [F,S,D4BMCuspResponse.responsePlanar,directional,Function.comp_apply,
        planarLaplacian,Fin.sum_univ_two,direction,Matrix.cons_val_zero,
        Matrix.cons_val_one,point,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,
        Complex.ofReal_re,zero_add] using he
    linear_combination he'
  have hl := weightedCovariance_linear_left ht.continuousOn hvv.continuousOn
    hhh.continuousOn hg.continuousOn (1:ℂ) 1 y.2
  simp only [one_mul] at hl
  have hr := weightedCovariance_linear_left ht.continuousOn hf.continuousOn
    hs.continuousOn hg.continuousOn
    (parameter q a/(y.val:ℂ)^2) (1/(y.val:ℂ)^2) y.2
  have he := hl.symm.trans ((weightedCovariance_slice_congr (T := T) (H := G) hp).trans hr)
  rw [weightedCovariance_horizontal_second ht hf hg y.2 (physicalTest_periodic q y)
    (D4BMCuspResponse.responsePlanar_periodic q a y.2)
    (D4BMCuspResponse.responsePlanar_periodic q b y.2)] at he
  have hd := weightedCovariance_hasDerivAt ht hv hg y.2
  apply hd.congr_deriv
  change weightedCovariance (directional Complex.I T) (directional Complex.I F) G y+
      weightedCovariance T (directional Complex.I (directional Complex.I F)) G y+
      weightedCovariance T (directional Complex.I F) (directional Complex.I G) y =
    weightedCovariance (directional Complex.I T) (directional Complex.I F) G y+
      weightedCovariance T (directional Complex.I F) (directional Complex.I G) y+
      weightedCovariance T (directional 1 F) (directional 1 G) y+
      weightedCovariance (directional 1 T) (directional 1 F) G y+
      (parameter q a/(y.val:ℂ)^2)*weightedCovariance T F G y+
      (1/(y.val:ℂ)^2)*weightedCovariance T S G y
  linear_combination he


private theorem weightedCovariance_continuousOn {T F G : ℂ → ℂ}
    (ht : ContDiffOn ℝ ∞ T {z : ℂ | 0 < z.im})
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im})
    (hg : ContDiffOn ℝ ∞ G {z : ℂ | 0 < z.im}) :
    ContinuousOn (weightedCovariance T F G) (Ioi (0:ℝ)) :=
  fun _ hy => (weightedCovariance_hasDerivAt ht hf hg hy).continuousAt.continuousWithinAt

private theorem testedPairDensity_continuousOn (q : XiZeroCopy) (a b : Bool) :
    ContinuousOn (testedPairDensity q a b) (Ioi (0:ℝ)) := by
  have ht := physicalTest_smooth q
  have hf := D4BMCuspResponse.responsePlanar_smooth q a
  have hg := D4BMCuspResponse.responsePlanar_smooth q b
  have hs := (globalForcing_smooth q a).planar_contDiffOn
  have h0 := weightedCovariance_continuousOn (directional_smooth ht Complex.I)
    (directional_smooth hf Complex.I) hg
  have h1 := weightedCovariance_continuousOn ht (directional_smooth hf Complex.I)
    (directional_smooth hg Complex.I)
  have h2 := weightedCovariance_continuousOn ht (directional_smooth hf 1) (directional_smooth hg 1)
  have h3 := weightedCovariance_continuousOn (directional_smooth ht 1) (directional_smooth hf 1) hg
  have hm := weightedCovariance_continuousOn ht hf hg
  have hw := weightedCovariance_continuousOn ht hs hg
  have hp : ContinuousOn (fun y : ℝ => (y:ℂ)^2) (Ioi (0:ℝ)) :=
    Complex.continuous_ofReal.continuousOn.pow 2
  have hn (y : ℝ) (hy : y ∈ Ioi (0:ℝ)) : (y:ℂ)^2 ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hy))
  exact ((((h0.add h1).add h2).add h3).add
    ((continuousOn_const.div hp hn).mul hm)).add ((continuousOn_const.div hp hn).mul hw)

/-- Both finite cusp endpoints remain in the physical scalar-tested source law. -/
theorem testedPairCurrent_finite_balance (q : XiZeroCopy) (a b : Bool) (l r : Ioi (0:ℝ)) :
    (∫ y in (l:ℝ)..r, testedPairDensity q a b y)=
      testedPairCurrent q a b r-testedPairCurrent q a b l := by
  have hi : IntervalIntegrable (testedPairDensity q a b) volume (l:ℝ) r := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    exact (testedPairDensity_continuousOn q a b y ((lt_min l.2 r.2).trans_le hy.1)).mono
      (fun _ hw => (lt_min l.2 r.2).trans_le hw.1)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy =>
    testedPairCurrent_hasDerivAt q a b ⟨y,(lt_min l.2 r.2).trans_le hy.1⟩) hi

/-- Restore the original tested response moment and both original response means.
The test is not centered, and its two linear response moments are retained. -/
theorem testedPairCurrent_decomposition (q : XiZeroCopy) (a b : Bool) (y : Ioi (0:ℝ)) :
    coefficient 1 0 (fun z => physicalTest q z*
      directional Complex.I (D4BMCuspResponse.responsePlanar q a) z*
      D4BMCuspResponse.responsePlanar q b z) y =
    testedPairCurrent q a b y+
      deriv (responseMode q a 0) y*coefficient 1 0
        (fun z => physicalTest q z*D4BMCuspResponse.responsePlanar q b z) y+
      responseMode q b 0 y*coefficient 1 0
        (fun z => physicalTest q z*directional Complex.I (D4BMCuspResponse.responsePlanar q a) z) y-
      deriv (responseMode q a 0) y*responseMode q b 0 y*coefficient 1 0 (physicalTest q) y := by
  have hd := (coefficient_hasDerivAt 1 (by norm_num) 0
    ((D4BMCuspResponse.responsePlanar_smooth q a).of_le (WithTop.coe_le_coe.mpr le_top)) y.2).deriv
  change deriv (responseMode q a 0) y=coefficient 1 0
    (directional Complex.I (D4BMCuspResponse.responsePlanar q a)) y at hd
  rw [hd]
  unfold testedPairCurrent weightedCovariance responseMode
  ring


open GaloisForLFunctions.HTGeometry.ScalarTwoJet

private theorem physicalScalar_horizontal_eq (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    coordDeriv 0 (scalar (physicalAngularParameter q)) z =
      2*(horizontalRate false*value (physicalAngularParameter q) (physicalAngularParameter q) (1/2) 1 false z+
        horizontalRate true*value (physicalAngularParameter q) (physicalAngularParameter q) (1/2) 1 true z) := by
  let u := physicalAngularParameter q
  change coordDeriv 0 (scalar u) z=_
  have he : scalar u =ᶠ[𝓝 z] fun w => principal u w+
      2*(value u u (1/2) 0 false w+value u u (1/2) 0 true w) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    change principal u w+tail u w = _
    simp only [tail,d4BMCompletedEisensteinCuspTailPart,d4BMCompletedEisensteinFullSignedZeroWord,
      signedTail_eq_value _ _ _ _ _ w hw,Nat.cast_zero,zero_add]
  have hp : DifferentiableAt ℝ (principal u) z :=
    ((cuspConstantPart_contDiffOn .scalar u).contDiffAt
      ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)).differentiableAt (by simp)
  have h0 := (value_hasFDerivAt u u (1/2) 0 false z hz).differentiableAt
  have h1 := (value_hasFDerivAt u u (1/2) 0 true z hz).differentiableAt
  have hpx : coordDeriv 0 (principal u) z=0 := by
    let c := reflectedCompletedLambda ((q.1:ℂ)-1)
    let k := 1-(q.1:ℂ)/2
    have heP : principal u=(fun w => c*(w 1:ℂ)^k) := funext (physicalScalar_principal q)
    have hd := (height_cpow_hasFDerivAt k z hz).const_mul c
    rw [coordDeriv,heP,hd.fderiv]
    simp only [smul_apply,smul_eq_mul]
    change c*((1:ℝ) • (0:ℂ)+(0:ℝ) • (k*(z 1:ℂ)^(k-1)))=0
    simp only [smul_zero,zero_smul,add_zero,mul_zero]
  unfold coordDeriv at hpx ⊢
  rw [he.fderiv_eq,fderiv_fun_add hp ((h0.fun_add h1).const_mul 2),
    fderiv_const_mul (h0.fun_add h1),fderiv_fun_add h0 h1]
  simp only [add_apply,smul_apply,smul_eq_mul,hpx,zero_add]
  change 2*(coordDeriv 0 (value u u (1/2) 0 false) z+
      coordDeriv 0 (value u u (1/2) 0 true) z)=_
  rw [value_coordDeriv_zero u u (1/2) 0 false z hz,
    value_coordDeriv_zero u u (1/2) 0 true z hz]

private theorem physicalScalar_horizontal_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, 3 < z 1 →
      ‖coordDeriv 0 (scalar (physicalAngularParameter q)) z‖ ≤ C := by
  let u := physicalAngularParameter q
  obtain ⟨A,hA,ha⟩ := weighted_value_bounded u u 0 (1/2) 1 false 3 (by norm_num)
  obtain ⟨B,hB,hb⟩ := weighted_value_bounded u u 0 (1/2) 1 true 3 (by norm_num)
  simp only [Complex.cpow_zero,one_mul] at ha hb
  refine ⟨2*(‖horizontalRate false‖*A+‖horizontalRate true‖*B),by positivity,?_⟩
  intro z hz
  rw [physicalScalar_horizontal_eq q z (by linarith),norm_mul]
  norm_num only [Complex.norm_ofNat]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
  exact (norm_add_le _ _).trans (by
    simp only [norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (ha z hz.le) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hb z hz.le) (norm_nonneg _)))

private theorem physicalScalar_value_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, 3 < z 1 →
      ‖scalar (physicalAngularParameter q) z‖ ≤ C*z 1 := by
  let u := physicalAngularParameter q
  let c := reflectedCompletedLambda ((q.1:ℂ)-1)
  obtain ⟨B,hB,hb⟩ := weighted_tail_bounded u 0 3 (by norm_num)
  simp only [Complex.cpow_zero,one_mul] at hb
  refine ⟨‖c‖+B,by positivity,?_⟩
  intro z hz
  have hy : 0 < z 1 := by linarith
  have hw : (1-(q.1:ℂ)/2).re≤1 := by
    simp only [Complex.sub_re,Complex.one_re,Complex.div_ofNat_re]
    linarith [(xi_divisor_support_re_mem_open_unit q.1).1]
  have he : ‖(z 1:ℂ)^(1-(q.1:ℂ)/2)‖≤z 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤z 1) hw
  change ‖principal u z+tail u z‖≤_
  rw [physicalScalar_principal]
  have hn := norm_add_le (c*(z 1:ℂ)^(1-(q.1:ℂ)/2)) (tail u z)
  rw [norm_mul] at hn
  have hp := mul_le_mul_of_nonneg_left he (norm_nonneg c)
  have hby := mul_le_mul_of_nonneg_left (by linarith : (1:ℝ)≤z 1) hB
  nlinarith only [hn,hp,hb z hz.le,hby]

/-- Literal source bounds for the full physical scalar test and both first jets.
The value grows at most linearly; the two ordinary derivatives are bounded. -/
theorem physicalTest_firstJet_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Ioi (3:ℝ), ∀ x : ℝ,
      ‖physicalTest q (point x y)‖ ≤ C*y.val ∧
      ‖directional Complex.I (physicalTest q) (point x y)‖ ≤ C ∧
      ‖directional 1 (physicalTest q) (point x y)‖ ≤ C := by
  obtain ⟨A,hA,ha⟩ := physicalScalar_value_bound q
  obtain ⟨B,hB,hb⟩ := physicalScalar_vertical_cusp_bound q
  obtain ⟨C,hC,hc⟩ := physicalScalar_horizontal_bound q
  refine ⟨A+B+C,by positivity,?_⟩
  intro y x
  let z := angularCoordinates (point x y)
  have he : z 1=y.val := by
    change (point x y).im=y.val
    simp only [point,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,
      Complex.ofReal_re,zero_add]
  have hz : 3 < z 1 := by rw [he]; exact y.2
  have hv : directional Complex.I (physicalTest q) (point x y)=
      coordDeriv 1 (scalar (physicalAngularParameter q)) z :=
    angularCoordinates_derivative (scalar (physicalAngularParameter q)) 1 (point x y)
  have hh : directional 1 (physicalTest q) (point x y)=
      coordDeriv 0 (scalar (physicalAngularParameter q)) z :=
    angularCoordinates_derivative (scalar (physicalAngularParameter q)) 0 (point x y)
  refine ⟨(ha z hz).trans ?_,?_,?_⟩
  · rw [he]
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith [y.2])
  · rw [hv]
    exact (hb z hz).trans (by linarith)
  · rw [hh]
    exact (hc z hz).trans (by linarith)


private theorem coefficient_zero_integral (F : ℂ → ℂ) (y : ℝ) :
    coefficient 1 0 F y=cellMean (fun x => F (point x y)) :=
  congrFun (mean_eq_coefficient F).symm y

private def variance (F : ℂ → ℂ) (y : ℝ) : ℝ := cellVariance (fun x => F (point x y))

private theorem variance_nonneg {F : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) : 0 ≤ variance F y := by
  change 0 ≤ cellVariance (fun x => F (point x y))
  rw [← cell_centered_square (slice_continuous hf hy)]
  exact integral_nonneg (fun _ => Complex.normSq_nonneg _)

private theorem native_variance (q : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    variance (D4BMCuspResponse.responsePlanar q b) y=nonconstantMass q b y := by
  have hs := coefficient_mass_hasSum 1 (by norm_num)
    (D4BMCuspResponse.responsePlanar_smooth q b).continuousOn y.2
  simp only [inv_one,one_mul] at hs
  have he := hs.unique (modeMass_hasSum q b y)
  unfold variance cellVariance
  rw [← coefficient_zero_integral]
  dsimp only [cell]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),he,nativeMass_decomposition q b y]
  change modeMass q b 0 y+nonconstantMass q b y-modeMass q b 0 y=nonconstantMass q b y
  ring

private theorem native_gradient_variance (q : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    2*variance (directional Complex.I (D4BMCuspResponse.responsePlanar q b)) y+
      variance (directional 1 (D4BMCuspResponse.responsePlanar q b)) y=nonconstantEnergy q b y := by
  let F := D4BMCuspResponse.responsePlanar q b
  have hf1 := (D4BMCuspResponse.responsePlanar_smooth q b).of_le
    (show (1 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hm : coefficient 1 0 (directional 1 F) y=0 := by
    rw [coefficient_horizontal 1 (by norm_num) 0 hf1 y.2 (D4BMCuspResponse.responsePlanar_periodic q b y.2)]
    simp only [signedFrequency,Int.cast_zero,mul_zero,zero_div,Complex.ofReal_zero,zero_mul]
  have hv := (coefficient_hasDerivAt 1 (by norm_num) 0 hf1 y.2).deriv
  have he := nativeGradientSlice_decomposition q b y
  unfold variance cellVariance
  rw [← coefficient_zero_integral,← coefficient_zero_integral,hm,Complex.normSq_zero,sub_zero]
  change deriv (responseMode q b 0) y=coefficient 1 0 (directional Complex.I F) y at hv
  rw [← hv]
  change 2*((∫ x in Ioc (0:ℝ) 1, Complex.normSq (directional Complex.I F (point x y)))-
      Complex.normSq (deriv (responseMode q b 0) y))+
    (∫ x in Ioc (0:ℝ) 1, Complex.normSq (directional 1 F (point x y)))=nonconstantEnergy q b y
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  simp only [nativeGradientSlice,modeEnergy,signedFrequency,Int.cast_zero,mul_zero,zero_div,
    zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_mul,add_zero] at he
  linear_combination he

private theorem forcing_variance_bound (q : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    variance (globalForcing q b ∘ ofComplex) y ≤ y.val^4*forcingMass q b y := by
  have hs := coefficient_mass_hasSum 1 (by norm_num)
    (globalForcing_smooth q b).planar_contDiffOn.continuousOn y.2
  simp only [inv_one,one_mul] at hs
  have he := (hs.div_const (y.val^4)).unique (forcingLoss_hasSum q b y)
  have hy4 : y.val^4 ≠ 0 := pow_ne_zero 4 (ne_of_gt y.2)
  have hm := (div_eq_iff hy4).mp he
  unfold variance cellVariance
  change (∫ x in Ioc (0:ℝ) 1, Complex.normSq ((globalForcing q b ∘ ofComplex) (point x y)))-
      Complex.normSq (cellMean (fun x => (globalForcing q b ∘ ofComplex) (point x y))) ≤ _
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),hm]
  nlinarith only [Complex.normSq_nonneg (cellMean (fun x => (globalForcing q b ∘ ofComplex) (point x y)))]

private theorem native_mass_le_energy (q : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    nonconstantMass q b y ≤ nonconstantEnergy q b y := by
  have hm := (modeMass_hasSum q b y).summable.subtype (fun n : ℤ => n ≠ 0)
  have he := (modeEnergy_hasSum q b y).summable.subtype (fun n : ℤ => n ≠ 0)
  apply hm.tsum_le_tsum ?_ he
  intro n
  have hnZ : (1:ℤ) ≤ n.val^2 := Int.add_one_le_iff.mpr (sq_pos_of_ne_zero n.2)
  have hnR : (1:ℝ) ≤ (n.val:ℝ)^2 := by exact_mod_cast hnZ
  have hk : 1 ≤ (signedFrequency 1 n.val)^2 := by
    have hh := mul_le_mul_of_nonneg_left hnR (sq_nonneg (2*Real.pi))
    have hp := Real.pi_gt_three
    dsimp only [signedFrequency]
    rw [div_one,mul_pow]
    nlinarith only [hh,hp,sq_nonneg (Real.pi-3)]
  have h := mul_le_mul_of_nonneg_right hk (Complex.normSq_nonneg (responseMode q b n.val y))
  change 1*modeMass q b n.val y ≤ (signedFrequency 1 n.val)^2*modeMass q b n.val y at h
  change modeMass q b n.val y ≤ 2*Complex.normSq (deriv (responseMode q b n.val) y)+
    (signedFrequency 1 n.val)^2*modeMass q b n.val y
  linarith only [h,Complex.normSq_nonneg (deriv (responseMode q b n.val) y)]

private theorem energy_nonneg (q : XiZeroCopy) (b : Bool) (y : ℝ) :
    0 ≤ nonconstantEnergy q b y := by
  apply tsum_nonneg
  intro n
  exact add_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
    (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))


private theorem complex_young (z w : ℂ) : 2*‖z*w‖ ≤ Complex.normSq z+Complex.normSq w := by
  rw [norm_mul,Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]
  nlinarith only [sq_nonneg (‖z‖-‖w‖)]

private theorem weightedCovariance_bound {T F G : ℂ → ℂ}
    (ht : ContinuousOn T {z : ℂ | 0 < z.im})
    (hf : ContinuousOn F {z : ℂ | 0 < z.im})
    (hg : ContinuousOn G {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x : ℝ, ‖T (point x y)‖≤C) :
    2*‖weightedCovariance T F G y‖≤C*(variance F y+variance G y) := by
  have cf := slice_continuous hf hy
  have cg := slice_continuous hg hy
  have ct := slice_continuous ht hy
  have cfc := cf.sub (continuous_const : Continuous (fun _ : ℝ => mean F y))
  have cgc := cg.sub (continuous_const : Continuous (fun _ : ℝ => mean G y))
  let f := fun x => F (point x y)-mean F y
  let g := fun x => G (point x y)-mean G y
  have hi := cell_integrable ((ct.mul cfc).mul cgc)
  have hf2 : IntegrableOn (fun x => Complex.normSq (f x)) cell := cell_normSq_integrable cfc
  have hg2 : IntegrableOn (fun x => Complex.normSq (g x)) cell := cell_normSq_integrable cgc
  rw [weightedCovariance_centered ht hf hg hy]
  have hnorm := norm_integral_le_integral_norm (μ := volume.restrict cell)
    (fun x => T (point x y)*f x*g x)
  have hp (x : ℝ) : 2*‖T (point x y)*f x*g x‖≤C*(Complex.normSq (f x)+Complex.normSq (g x)) := by
    have he := mul_le_mul_of_nonneg_left (complex_young (f x) (g x)) hC
    have hb' := mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (f x*g x))
    rw [norm_mul] at he hb'
    simp only [norm_mul]
    nlinarith only [he,hb']
  have hm := integral_mono (hi.norm.const_mul 2) ((hf2.add hg2).const_mul C) hp
  change (∫ x in cell,2*‖T (point x y)*f x*g x‖)≤
    ∫ x in cell,C*(Complex.normSq (f x)+Complex.normSq (g x)) at hm
  rw [integral_const_mul,integral_const_mul,integral_add hf2 hg2] at hm
  have heF : (∫ x in cell,Complex.normSq (f x))=variance F y := cell_centered_square cf
  have heG : (∫ x in cell,Complex.normSq (g x))=variance G y := cell_centered_square cg
  rw [heF,heG] at hm
  linarith only [hnorm,hm]

private theorem native_variance_bounds (q : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    variance (D4BMCuspResponse.responsePlanar q b) y≤nonconstantEnergy q b y ∧
    variance (directional Complex.I (D4BMCuspResponse.responsePlanar q b)) y≤nonconstantEnergy q b y ∧
    variance (directional 1 (D4BMCuspResponse.responsePlanar q b)) y≤nonconstantEnergy q b y := by
  have hf := D4BMCuspResponse.responsePlanar_smooth q b
  have hv := variance_nonneg (directional_smooth hf Complex.I).continuousOn y.2
  have hh := variance_nonneg (directional_smooth hf 1).continuousOn y.2
  have he := native_gradient_variance q b y
  refine ⟨?_,by linarith only [he,hv,hh],by linarith only [he,hv]⟩
  rw [native_variance]
  exact native_mass_le_energy q b y


/-- One source-derived constant controls the full physical tested current and all
six differentiated terms by original native energies and complete forcing mass. -/
theorem testedPair_source_bounds (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : Bool, ∀ y : Ioi (3:ℝ),
      ‖testedPairCurrent q a b y‖ ≤ C*y.val*(nonconstantEnergy q a y+nonconstantEnergy q b y) ∧
      ‖testedPairDensity q a b y‖ ≤ C*y.val*
        ((‖parameter q a‖+5)*(nonconstantEnergy q a y+nonconstantEnergy q b y)+
          y.val^4*forcingMass q a y) := by
  obtain ⟨C,hC,hjet⟩ := physicalTest_firstJet_bound q
  refine ⟨C,hC,?_⟩
  intro a b y
  have hy0 : 0 < y.val := lt_trans (by norm_num : (0:ℝ)<3) y.2
  let z : Ioi (0:ℝ) := ⟨y.val,hy0⟩
  let T := physicalTest q
  let F := D4BMCuspResponse.responsePlanar q a
  let G := D4BMCuspResponse.responsePlanar q b
  let S := globalForcing q a ∘ ofComplex
  let E := nonconstantEnergy q a y+nonconstantEnergy q b y
  have ht := physicalTest_smooth q
  have hf := D4BMCuspResponse.responsePlanar_smooth q a
  have hg := D4BMCuspResponse.responsePlanar_smooth q b
  have hs := (globalForcing_smooth q a).planar_contDiffOn
  have htv := directional_smooth ht Complex.I
  have htx := directional_smooth ht 1
  have hfv := directional_smooth hf Complex.I
  have hfx := directional_smooth hf 1
  have hgv := directional_smooth hg Complex.I
  have hgx := directional_smooth hg 1
  obtain ⟨hf0,hf1,hf2⟩ := native_variance_bounds q a z
  obtain ⟨hg0,hg1,hg2⟩ := native_variance_bounds q b z
  have hforce := forcing_variance_bound q a z
  have hCY : 0 ≤ C*y.val := mul_nonneg hC hy0.le
  have hy3 : 3 < y.val := y.2
  have hC_le : C≤C*y.val := by nlinarith only [hC,hy3]
  have hb0 (x : ℝ) : ‖T (point x y)‖≤C*y.val := (hjet y x).1
  have hb1 (x : ℝ) : ‖directional Complex.I T (point x y)‖≤C*y.val :=
    (hjet y x).2.1.trans hC_le
  have hb2 (x : ℝ) : ‖directional 1 T (point x y)‖≤C*y.val :=
    (hjet y x).2.2.trans hC_le
  have hb {W H K : ℂ → ℂ}
      (hw : ContinuousOn W {z : ℂ | 0 < z.im})
      (hh : ContinuousOn H {z : ℂ | 0 < z.im})
      (hk : ContinuousOn K {z : ℂ | 0 < z.im})
      (hwb : ∀ x : ℝ, ‖W (point x y)‖≤C*y.val) {A B : ℝ}
      (ha : variance H y≤A) (hb : variance K y≤B) :
      2*‖weightedCovariance W H K y‖≤C*y.val*(A+B) :=
    (weightedCovariance_bound hw hh hk hy0 hCY hwb).trans
      (mul_le_mul_of_nonneg_left (add_le_add ha hb) hCY)
  have hj := hb ht.continuousOn hfv.continuousOn hg.continuousOn hb0 hf1 hg0
  have h0 := hb htv.continuousOn hfv.continuousOn hg.continuousOn hb1 hf1 hg0
  have h1 := hb ht.continuousOn hfv.continuousOn hgv.continuousOn hb0 hf1 hg1
  have h2 := hb ht.continuousOn hfx.continuousOn hgx.continuousOn hb0 hf2 hg2
  have h3 := hb htx.continuousOn hfx.continuousOn hg.continuousOn hb2 hf2 hg0
  have hm := hb ht.continuousOn hf.continuousOn hg.continuousOn hb0 hf0 hg0
  have hw := hb ht.continuousOn hs.continuousOn hg.continuousOn hb0 hforce hg0
  have hcoef : ‖(1:ℂ)/(y.val:ℂ)^2‖ ≤ 1 := by
    rw [norm_div,norm_one,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy0]
    apply (div_le_one (sq_pos_of_pos hy0)).mpr
    nlinarith only [hy3,sq_nonneg (y.val-1)]
  have hpcoef : ‖parameter q a/(y.val:ℂ)^2‖≤‖parameter q a‖ := by
    rw [show parameter q a/(y.val:ℂ)^2=parameter q a*((1:ℂ)/(y.val:ℂ)^2) by ring,norm_mul]
    exact (mul_le_mul_of_nonneg_left hcoef (norm_nonneg _)).trans_eq (mul_one _)
  let A := weightedCovariance (directional Complex.I T) (directional Complex.I F) G y
  let B := weightedCovariance T (directional Complex.I F) (directional Complex.I G) y
  let D := weightedCovariance T (directional 1 F) (directional 1 G) y
  let H := weightedCovariance (directional 1 T) (directional 1 F) G y
  let M := weightedCovariance T F G y
  let W := weightedCovariance T S G y
  have hpm := mul_le_mul_of_nonneg_right hpcoef (norm_nonneg M)
  have hfw := mul_le_mul_of_nonneg_right hcoef (norm_nonneg W)
  have hmp := mul_le_mul_of_nonneg_left hm (norm_nonneg (parameter q a))
  have hn0 := norm_add_le A B
  have hn1 := norm_add_le (A+B) D
  have hn2 := norm_add_le (A+B+D) H
  have hn3 := norm_add_le (A+B+D+H) ((parameter q a/(y.val:ℂ)^2)*M)
  have hn4 := norm_add_le (A+B+D+H+(parameter q a/(y.val:ℂ)^2)*M)
    ((1/(y.val:ℂ)^2)*W)
  rw [norm_mul] at hn3 hn4
  change ‖testedPairDensity q a b y‖≤_ at hn4
  have hEa : 0 ≤ nonconstantEnergy q a y := energy_nonneg q a y
  have hextra := mul_nonneg hCY hEa
  refine ⟨?_,?_⟩
  · change 2*‖testedPairCurrent q a b y‖≤_ at hj
    linarith only [hj,norm_nonneg (testedPairCurrent q a b y)]
  · change 2*‖A‖≤C*y.val*E at h0
    change 2*‖B‖≤C*y.val*E at h1
    change 2*‖D‖≤C*y.val*E at h2
    change 2*‖H‖≤C*y.val*E at h3
    change 2*‖W‖≤C*y.val*(y.val^4*forcingMass q a y+nonconstantEnergy q b y) at hw
    change ‖parameter q a‖*(2*‖M‖)≤‖parameter q a‖*(C*y.val*E) at hmp
    change ‖testedPairDensity q a b y‖≤C*y.val*((‖parameter q a‖+5)*E+y.val^4*forcingMass q a y)
    dsimp only [E] at *
    nlinarith only [h0,h1,h2,h3,hw,hpm,hfw,hmp,hn0,hn1,hn2,hn3,hn4,hextra,
      norm_nonneg (testedPairDensity q a b y)]

private theorem inverse_square_integrable {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun y : ℝ => 1/y^2) (Ioi T) := by
  have h := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hT
  apply h.congr_fun ?_ measurableSet_Ioi
  intro y hy
  change y^(-(2:ℝ))=1/y^2
  rw [Real.rpow_neg (le_of_lt (lt_trans hT hy)),Real.rpow_two,one_div]

private theorem polynomial_pair_hasDerivAt (q : XiZeroCopy) (a b : Bool) (N : ℕ)
    (y : Ioi (0:ℝ)) :
    HasDerivAt (fun t : ℝ => (t:ℂ)^N*testedPairCurrent q a b t)
      ((N:ℂ)*(y.val:ℂ)^(N-1)*testedPairCurrent q a b y+
        (y.val:ℂ)^N*testedPairDensity q a b y) y := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := y.val)).pow N).mul
    (testedPairCurrent_hasDerivAt q a b y)
  change HasDerivAt (fun t : ℝ => (t:ℂ)^N*testedPairCurrent q a b t)
    ((N:ℂ)*(y.val:ℂ)^(N-1)*(1:ℂ)*testedPairCurrent q a b y+
      (y.val:ℂ)^N*testedPairDensity q a b y) y at h
  simpa only [mul_one] using h


private theorem testedPairCurrent_continuousOn (q : XiZeroCopy) (a b : Bool) :
    ContinuousOn (testedPairCurrent q a b) (Ioi (0:ℝ)) :=
  fun y hy => (testedPairCurrent_hasDerivAt q a b ⟨y,hy⟩).continuousAt.continuousWithinAt

private theorem polynomial_pair_admission (q : XiZeroCopy) (a b : Bool) (N : ℕ) :
    ∃ T : ℝ, 4 ≤ T ∧
      IntegrableOn (fun y : ℝ => (y:ℂ)^N*testedPairCurrent q a b y) (Ioi T) ∧
      IntegrableOn (fun y : ℝ => (N:ℂ)*(y:ℂ)^(N-1)*testedPairCurrent q a b y+
        (y:ℂ)^N*testedPairDensity q a b y) (Ioi T) := by
  obtain ⟨A,hA,hia,_⟩ := nativeNonconstantEnergy_admission q a (N+1)
  obtain ⟨B,hB,hib,_⟩ := nativeNonconstantEnergy_admission q b (N+1)
  obtain ⟨D,hD,hforce⟩ := forcingMass_weighted_bound q a (N+3)
  obtain ⟨C,hC,hsource⟩ := testedPair_source_bounds q
  let T := max (A+1) (max (B+1) 4)
  have hTA : A+1 ≤ T := le_max_left _ _
  have hTB : B+1 ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hT : 4 ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hypos (y : ℝ) (hy : y ∈ Ioi T) : 0 < y := lt_trans hT0 hy
  have hyhigh (y : ℝ) (hy : y ∈ Ioi T) : 3 < y :=
    lt_of_lt_of_le (by norm_num : (3:ℝ)<4) (hT.trans hy.le)
  have hsub : Ioi T ⊆ Ioi (0:ℝ) := fun y hy => hypos y hy
  let W : ℝ → ℝ := fun y => y^(2*(N+2))*(nonconstantEnergy q a y+nonconstantEnergy q b y)
  have hiW : IntegrableOn W (Ioi T) := by
    have hia' := hia.mono_set (Ioi_subset_Ioi hTA)
    have hib' := hib.mono_set (Ioi_subset_Ioi hTB)
    convert hia'.add hib' using 1 <;> try rfl
    funext y
    change y^(2*(N+2))*(nonconstantEnergy q a y+nonconstantEnergy q b y)=
      y^(2*(N+1+1))*nonconstantEnergy q a y+y^(2*(N+1+1))*nonconstantEnergy q b y
    rw [show N+1+1=N+2 by omega]
    ring
  let K : ℝ := ‖parameter q a‖+5
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hbound (y : ℝ) (hy : y ∈ Ioi T) :
      ‖(y:ℂ)^N*testedPairCurrent q a b y‖≤C*W y ∧
      ‖(N:ℂ)*(y:ℂ)^(N-1)*testedPairCurrent q a b y+
        (y:ℂ)^N*testedPairDensity q a b y‖≤C*(((N:ℝ)+K)*W y+D*(1/y^2)) := by
    have hy0 := hypos y hy
    have hy3 := hyhigh y hy
    have hy1 : 1 < y := lt_trans (by norm_num : (1:ℝ)<3) hy3
    let E := nonconstantEnergy q a y+nonconstantEnergy q b y
    have hE : 0 ≤ E := add_nonneg (energy_nonneg q a y) (energy_nonneg q b y)
    obtain ⟨hj,hd⟩ := hsource a b ⟨y,hy3⟩
    have hPN : y^(N+1)≤y^(2*(N+2)) := pow_le_pow_right₀ hy1.le (by omega)
    have hPm : y^(N-1+1)≤y^(2*(N+2)) := pow_le_pow_right₀ hy1.le (by omega)
    have hJW : y^(N+1)*E≤W y := mul_le_mul_of_nonneg_right hPN hE
    have hJmW : y^(N-1+1)*E≤W y := mul_le_mul_of_nonneg_right hPm hE
    have hJ : y^N*‖testedPairCurrent q a b y‖≤C*W y := by
      calc
        _ ≤ y^N*(C*y*E) := mul_le_mul_of_nonneg_left hj (pow_nonneg hy0.le N)
        _ = C*(y^(N+1)*E) := by rw [pow_succ]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hJW hC
    have hJm : y^(N-1)*‖testedPairCurrent q a b y‖≤C*W y := by
      calc
        _ ≤ y^(N-1)*(C*y*E) := mul_le_mul_of_nonneg_left hj (pow_nonneg hy0.le (N-1))
        _ = C*(y^(N-1+1)*E) := by rw [pow_succ]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hJmW hC
    have hF0 : 0 ≤ forcingMass q a y := by
      rw [← (forcingLoss_hasSum q a ⟨y,hy0⟩).tsum_eq]
      exact tsum_nonneg (fun _ => div_nonneg (Complex.normSq_nonneg _) (pow_nonneg hy0.le 4))
    have hFp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hy1.le (show N+7≤2*(N+3)+4 by omega)) hF0
    have hF : y^(N+1)*(y^4*forcingMass q a y)≤D/y^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hy0)).mpr
      calc
        _ = y^(N+7)*forcingMass q a y := by
          rw [show N+7=((N+1)+4)+2 by omega,pow_add,pow_add]
          ring
        _ ≤ y^(2*(N+3)+4)*forcingMass q a y := hFp
        _ ≤ D := hforce ⟨y,hy3⟩
    have hD0 := mul_le_mul_of_nonneg_left hd (pow_nonneg hy0.le N)
    have hDW := mul_le_mul_of_nonneg_left hJW (mul_nonneg hC hK)
    have hDF := mul_le_mul_of_nonneg_left hF hC
    have hD' : y^N*‖testedPairDensity q a b y‖≤C*(K*W y+D/y^2) := by
      change y^N*‖testedPairDensity q a b y‖≤y^N*(C*y*(K*E+y^4*forcingMass q a y)) at hD0
      rw [pow_succ] at hDW hDF
      nlinarith only [hD0,hDW,hDF]
    have hnorm := norm_add_le ((N:ℂ)*(y:ℂ)^(N-1)*testedPairCurrent q a b y)
      ((y:ℂ)^N*testedPairDensity q a b y)
    simp only [norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hy0] at hnorm ⊢
    refine ⟨hJ,?_⟩
    have hNJ := mul_le_mul_of_nonneg_left hJm (Nat.cast_nonneg (α := ℝ) N)
    rw [show D*(1/y^2)=D/y^2 by ring]
    nlinarith only [hnorm,hNJ,hD']
  have hcP : ContinuousOn (fun y : ℝ => (y:ℂ)^N) (Ioi T) :=
    Complex.continuous_ofReal.continuousOn.pow N
  have hcM : ContinuousOn (fun y : ℝ => (y:ℂ)^(N-1)) (Ioi T) :=
    Complex.continuous_ofReal.continuousOn.pow (N-1)
  have hcJ := (testedPairCurrent_continuousOn q a b).mono hsub
  have hcD := (testedPairDensity_continuousOn q a b).mono hsub
  have hjm : AEStronglyMeasurable (fun y : ℝ => (y:ℂ)^N*testedPairCurrent q a b y)
      (volume.restrict (Ioi T)) := (hcP.mul hcJ).aestronglyMeasurable measurableSet_Ioi
  have hdm : AEStronglyMeasurable (fun y : ℝ => (N:ℂ)*(y:ℂ)^(N-1)*testedPairCurrent q a b y+
      (y:ℂ)^N*testedPairDensity q a b y) (volume.restrict (Ioi T)) :=
    (((hcM.const_mul (N:ℂ)).mul hcJ).add (hcP.mul hcD)).aestronglyMeasurable measurableSet_Ioi
  have hiR : IntegrableOn (fun y : ℝ => C*(((N:ℝ)+K)*W y+D*(1/y^2))) (Ioi T) :=
    ((hiW.const_mul ((N:ℝ)+K)).add ((inverse_square_integrable hT0).const_mul D)).const_mul C
  refine ⟨T,hT,(hiW.const_mul C).mono' hjm ?_,hiR.mono' hdm ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (hbound y hy).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (hbound y hy).2

/-- Every polynomially weighted physical scalar-tested centered response current
has zero upper cusp trace, from the original source energy and forcing bounds. -/
theorem testedPairCurrent_weighted_tendsto_zero (q : XiZeroCopy) (a b : Bool) (N : ℕ) :
    Tendsto (fun y : ℝ => (y:ℂ)^N*testedPairCurrent q a b y) atTop (𝓝 0) := by
  obtain ⟨T,hT,hiJ,hiD⟩ := polynomial_pair_admission q a b N
  apply tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi ?_ hiD hiJ
  intro y hy
  have hy0 : 0 < y := lt_trans (lt_of_lt_of_le (by norm_num : (0:ℝ)<4) hT) hy
  exact polynomial_pair_hasDerivAt q a b N ⟨y,hy0⟩


/-- Every complex height weight preserves the zero trace of the centered current
with the full original physical scalar test retained. -/
theorem testedPairCurrent_cpow_tendsto_zero (q : XiZeroCopy) (a b : Bool) (w : ℂ) :
    Tendsto (fun y : ℝ => (y:ℂ)^w*testedPairCurrent q a b y) atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := exists_nat_gt w.re
  have h := (testedPairCurrent_weighted_tendsto_zero q a b N).norm
  simp only [norm_zero] at h
  apply squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy0,norm_mul,norm_pow,
    Complex.norm_of_nonneg hy0.le]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hy hN.le

/-- The improper integral of all six source terms is the negative lower current.
Upper cusp decay does not remove this original finite endpoint. -/
theorem testedPairDensity_integral_tendsto (q : XiZeroCopy) (a b : Bool) (l : Ioi (0:ℝ)) :
    Tendsto (fun r : ℝ => ∫ y in (l:ℝ)..r,testedPairDensity q a b y) atTop
      (𝓝 (-testedPairCurrent q a b l)) := by
  have h : Tendsto (testedPairCurrent q a b) atTop (𝓝 0) := by
    simpa only [pow_zero,one_mul] using testedPairCurrent_weighted_tendsto_zero q a b 0
  have hd := h.sub (tendsto_const_nhds (x := testedPairCurrent q a b l))
  simp only [zero_sub] at hd
  apply hd.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  exact (testedPairCurrent_finite_balance q a b l ⟨r,hr⟩).symm

end
end RHTower.D4BMQuarticTestedNativeCurrent
