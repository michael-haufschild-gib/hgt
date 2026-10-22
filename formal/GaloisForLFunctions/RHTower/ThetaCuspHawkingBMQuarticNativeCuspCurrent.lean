import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticNativeCuspEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Source-derived upper trace of the native bilinear cusp current

The original forced response equation determines the complex bilinear current
with its mean product separated. Periodicity cancels the horizontal side flux,
while the signed forcing work remains. Finite-cell covariance and the existing
Parseval decomposition bound the current and its derivative by the admitted
native nonconstant energies and complete original forcing mass.

Both polynomially weighted integrabilities are derived from those source bounds,
so the improper-integral theorem supplies the zero upper trace. The last theorem
restores the original cusp cell and native mean product explicitly. This closes
the native nonconstant current trace, not the full scalar-tested nonlinear action
or fixed Hawking-clock extinction. The source-predeclared clock is unchanged.
-/

open scoped ContDiff
open MeasureTheory Set Filter Topology UpperHalfPlane
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.SelbergMaassMean
open GaloisForLFunctions.RHTower.SelbergMaassFourier
open GaloisForLFunctions.RHTower.SelbergMaassParseval
namespace RHTower.D4BMQuarticNativeCuspCurrent
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
private def cellCovariance (f g : ℝ → ℂ) : ℂ :=
  cellMean (fun x => f x*g x)-cellMean f*cellMean g

private theorem cell_integrable {f : ℝ → ℂ} (hf : Continuous f) : IntegrableOn f cell :=
  hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self

private theorem cell_normSq_integrable {f : ℝ → ℂ} (hf : Continuous f) :
    IntegrableOn (fun x => Complex.normSq (f x)) cell := by
  have h : IntegrableOn (fun x => ‖f x‖ ^ 2) (Ioc 0 1) :=
    (hf.norm.pow 2).integrableOn_Ioc
  simpa only [cell,Complex.normSq_eq_norm_sq] using h

private theorem cellMean_const (c : ℂ) : cellMean (fun _ => c)=c := by
  change (∫ x in Ioc (0:ℝ) 1, c)=c
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  simp only [intervalIntegral.integral_const,sub_zero,one_smul]

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

theorem cellCovariance_centered {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    cellCovariance f g=∫ x in cell, (f x-cellMean f)*(g x-cellMean g) := by
  let a := cellMean f
  let b := cellMean g
  have hfg : IntegrableOn (fun x => f x*g x) cell := cell_integrable (hf.mul hg)
  have hfb := cell_integrable (hf.mul_const b)
  have hag := cell_integrable (hg.const_mul a)
  have hc := cell_integrable (continuous_const : Continuous (fun _ : ℝ => a*b))
  have he : (fun x => (f x-a)*(g x-b))=(fun x => (f x*g x-f x*b)-(a*g x)+a*b) := by
    funext x; ring
  have hsub : IntegrableOn (fun x => f x*g x-f x*b) cell := hfg.sub hfb
  have hsub' : IntegrableOn (fun x => (f x*g x-f x*b)-a*g x) cell := hsub.sub hag
  rw [he,integral_add hsub' hc,
    integral_sub hsub hag,integral_sub hfg hfb,integral_mul_const,integral_const_mul]
  change cellMean (fun x => f x*g x)-a*b=
    (cellMean (fun x => f x*g x)-a*b)-a*b+cellMean (fun _ => a*b)
  rw [cellMean_const]
  ring

private theorem complex_young (z w : ℂ) : 2*‖z*w‖ ≤ Complex.normSq z+Complex.normSq w := by
  rw [norm_mul,Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]
  nlinarith only [sq_nonneg (‖z‖-‖w‖)]

private theorem cellCovariance_bound {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    2*‖cellCovariance f g‖ ≤ cellVariance f+cellVariance g := by
  have hfc : Continuous (fun x => f x-cellMean f) := hf.sub continuous_const
  have hgc : Continuous (fun x => g x-cellMean g) := hg.sub continuous_const
  have hi := cell_integrable (hfc.mul hgc)
  have hf2 := cell_normSq_integrable hfc
  have hg2 := cell_normSq_integrable hgc
  rw [cellCovariance_centered hf hg]
  have hnorm := norm_integral_le_integral_norm (μ := volume.restrict cell)
    (fun x => (f x-cellMean f)*(g x-cellMean g))
  have hb := integral_mono (hi.norm.const_mul 2) (hf2.add hg2)
    (fun x => complex_young (f x-cellMean f) (g x-cellMean g))
  change (∫ x in cell, 2*‖(f x-cellMean f)*(g x-cellMean g)‖) ≤
    (∫ x in cell, Complex.normSq (f x-cellMean f)+Complex.normSq (g x-cellMean g)) at hb
  rw [integral_const_mul,integral_add hf2 hg2,cell_centered_square hf,cell_centered_square hg] at hb
  linarith only [hnorm,hb]

private theorem coefficient_zero_integral (F : ℂ → ℂ) (y : ℝ) :
    coefficient 1 0 F y=cellMean (fun x => F (point x y)) := by
  simp only [coefficient,deningerFourierCoeff,deningerFourierKernel,Int.cast_zero,
    mul_zero,zero_mul,neg_zero,Complex.exp_zero,Complex.ofReal_one,div_one,one_mul]
  change (∫ x in (0:ℝ)..1, F (point x y))=∫ x in Ioc (0:ℝ) 1, F (point x y)
  exact intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)

/-- Complex bilinear covariance of the literal period-one slices. -/
def covariance (F G : ℂ → ℂ) (y : ℝ) : ℂ :=
  coefficient 1 0 (fun z => F z*G z) y-coefficient 1 0 F y*coefficient 1 0 G y

/-- The original native bilinear vertical current with its mean product separated. -/
def nativePairCurrent (q : XiZeroCopy) (a b : Bool) : ℝ → ℂ :=
  covariance (directional Complex.I (D4BMCuspResponse.responsePlanar q a))
    (D4BMCuspResponse.responsePlanar q b)

theorem coefficient_zero_linear {F G : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im})
    (hg : ContinuousOn G {z : ℂ | 0 < z.im}) (c d : ℂ)
    {y : ℝ} (hy : 0 < y) :
    coefficient 1 0 (fun z => c*F z+d*G z) y =
      c*coefficient 1 0 F y+d*coefficient 1 0 G y := by
  simp only [coefficient_zero_integral,cellMean]
  rw [integral_add ((cell_integrable (slice_continuous hf hy)).const_mul c)
    ((cell_integrable (slice_continuous hg hy)).const_mul d),integral_const_mul,integral_const_mul]

theorem covariance_linear_left {F G H : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im})
    (hg : ContinuousOn G {z : ℂ | 0 < z.im})
    (hh : ContinuousOn H {z : ℂ | 0 < z.im}) (c d : ℂ)
    {y : ℝ} (hy : 0 < y) :
    covariance (fun z => c*F z+d*G z) H y = c*covariance F H y+d*covariance G H y := by
  have he : (fun z => (c*F z+d*G z)*H z) = (fun z => c*(F z*H z)+d*(G z*H z)) := by
    funext z; ring
  unfold covariance
  rw [he,coefficient_zero_linear (F := fun z => F z*H z) (G := fun z => G z*H z)
    (hf.mul hh) (hg.mul hh) c d hy,
    coefficient_zero_linear hf hg c d hy]
  ring

theorem covariance_slice_congr {F G H : ℂ → ℂ} {y : ℝ}
    (he : ∀ x : ℝ, F (point x y)=G (point x y)) : covariance F H y=covariance G H y := by
  simp only [covariance,coefficient_zero_integral,cellMean]
  congr 1
  · exact integral_congr_ae (Filter.Eventually.of_forall (fun x => congrArg (fun z => z*H (point x y)) (he x)))
  · congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall he)

theorem covariance_hasDerivAt {F G : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im})
    (hg : ContDiffOn ℝ ∞ G {z : ℂ | 0 < z.im})
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (covariance F G)
      (covariance (directional Complex.I F) G y+covariance F (directional Complex.I G) y) y := by
  have hf1 := hf.of_le (show (1 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hg1 := hg.of_le (show (1 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hdi := (coefficient_hasDerivAt 1 (by norm_num) 0 (hf1.mul hg1) hy).sub
    ((coefficient_hasDerivAt 1 (by norm_num) 0 hf1 hy).mul
      (coefficient_hasDerivAt 1 (by norm_num) 0 hg1 hy))
  have hp (x : ℝ) : directional Complex.I (fun z => F z*G z) (point x y) =
      directional Complex.I F (point x y)*G (point x y)+F (point x y)*directional Complex.I G (point x y) :=
    (slice_vertical (hf1.mul hg1) x hy).unique ((slice_vertical hf1 x hy).mul (slice_vertical hg1 x hy))
  have hm : coefficient 1 0 (directional Complex.I (fun z => F z*G z)) y =
      coefficient 1 0 (fun z => directional Complex.I F z*G z) y+
        coefficient 1 0 (fun z => F z*directional Complex.I G z) y := by
    simp only [coefficient_zero_integral,cellMean]
    rw [integral_congr_ae (Filter.Eventually.of_forall hp)]
    exact integral_add
      (cell_integrable ((slice_continuous (directional_smooth hf Complex.I).continuousOn hy).mul
        (slice_continuous hg.continuousOn hy)))
      (cell_integrable ((slice_continuous hf.continuousOn hy).mul
        (slice_continuous (directional_smooth hg Complex.I).continuousOn hy)))
  apply hdi.congr_deriv
  rw [hm]
  unfold covariance
  ring

theorem covariance_horizontal_second {F G : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im})
    (hg : ContDiffOn ℝ ∞ G {z : ℂ | 0 < z.im})
    {y : ℝ} (hy : 0 < y)
    (hp : ∀ x, F (point (x+1) y)=F (point x y))
    (hq : ∀ x, G (point (x+1) y)=G (point x y)) :
    covariance (directional 1 (directional 1 F)) G y =
      -covariance (directional 1 F) (directional 1 G) y := by
  have hf1 := hf.of_le (show (1 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hg1 := hg.of_le (show (1 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hdx := directional_smooth hf (1:ℂ)
  have hxx := directional_smooth hdx (1:ℂ)
  have hdy := directional_smooth hg (1:ℂ)
  have hdx1 := hdx.of_le (show (1 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hiu : IntegrableOn (fun x => directional 1 (directional 1 F) (point x y)*G (point x y)) cell :=
    cell_integrable ((slice_continuous hxx.continuousOn hy).mul (slice_continuous hg.continuousOn hy))
  have hiv : IntegrableOn (fun x => directional 1 F (point x y)*directional 1 G (point x y)) cell :=
    cell_integrable ((slice_continuous hdx.continuousOn hy).mul (slice_continuous hdy.continuousOn hy))
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
    (fun x _ => (slice_horizontal hdx1 hy x).mul (slice_horizontal hg1 hy x))
    ((((slice_continuous hxx.continuousOn hy).mul (slice_continuous hg.continuousOn hy)).add
      ((slice_continuous hdx.continuousOn hy).mul (slice_continuous hdy.continuousOn hy))).intervalIntegrable 0 1)
  have hper : directional 1 F (point 1 y)=directional 1 F (point 0 y) := by
    simpa only [zero_add] using directional_periodic hf1 hy 1 hp 0
  have hgper : G (point 1 y)=G (point 0 y) := by simpa only [zero_add] using hq 0
  simp only [Pi.mul_apply] at ht
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),hper,hgper,sub_self] at ht
  change (∫ x in cell, directional 1 (directional 1 F) (point x y)*G (point x y)+
    directional 1 F (point x y)*directional 1 G (point x y))=0 at ht
  rw [integral_add hiu hiv] at ht
  have hm1 : coefficient 1 0 (directional 1 F) y=0 := by
    rw [coefficient_horizontal 1 (by norm_num) 0 hf1 hy hp]
    simp only [signedFrequency,Int.cast_zero,mul_zero,zero_div,Complex.ofReal_zero,zero_mul]
  have hm2 : coefficient 1 0 (directional 1 (directional 1 F)) y=0 := by
    rw [coefficient_horizontal_second 1 (by norm_num) 0
      (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hy hp]
    simp only [signedFrequency,Int.cast_zero,mul_zero,zero_div,Complex.ofReal_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,neg_zero,zero_mul]
  simp only [covariance,hm1,hm2,zero_mul,sub_zero,coefficient_zero_integral,cellMean]
  linear_combination ht

/-- All signed terms of the original forced bilinear current derivative. -/
def nativePairDensity (q : XiZeroCopy) (a b : Bool) (y : ℝ) : ℂ :=
  covariance (directional Complex.I (D4BMCuspResponse.responsePlanar q a))
    (directional Complex.I (D4BMCuspResponse.responsePlanar q b)) y+
  covariance (directional 1 (D4BMCuspResponse.responsePlanar q a))
    (directional 1 (D4BMCuspResponse.responsePlanar q b)) y+
  (parameter q a/(y:ℂ)^2)*covariance (D4BMCuspResponse.responsePlanar q a)
    (D4BMCuspResponse.responsePlanar q b) y+
  (1/(y:ℂ)^2)*covariance (globalForcing q a ∘ ofComplex)
    (D4BMCuspResponse.responsePlanar q b) y

/-- The literal source equation determines the native bilinear current derivative.
The two horizontal side fluxes cancel by actual source periodicity; forcing work remains. -/
theorem nativePairCurrent_hasDerivAt (q : XiZeroCopy) (a b : Bool) (y : Ioi (0:ℝ)) :
    HasDerivAt (nativePairCurrent q a b) (nativePairDensity q a b y) y := by
  let F := D4BMCuspResponse.responsePlanar q a
  let G := D4BMCuspResponse.responsePlanar q b
  let S := globalForcing q a ∘ ofComplex
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
  have hl := covariance_linear_left hvv.continuousOn hhh.continuousOn hg.continuousOn
    (1:ℂ) 1 y.2
  simp only [one_mul] at hl
  have hr := covariance_linear_left hf.continuousOn hs.continuousOn hg.continuousOn
    (parameter q a/(y.val:ℂ)^2) (1/(y.val:ℂ)^2) y.2
  have he := hl.symm.trans ((covariance_slice_congr (H := G) hp).trans hr)
  rw [covariance_horizontal_second hf hg y.2
    (D4BMCuspResponse.responsePlanar_periodic q a y.2)
    (D4BMCuspResponse.responsePlanar_periodic q b y.2)] at he
  have hd := covariance_hasDerivAt hv hg y.2
  apply hd.congr_deriv
  change covariance (directional Complex.I (directional Complex.I F)) G y+
      covariance (directional Complex.I F) (directional Complex.I G) y =
    covariance (directional Complex.I F) (directional Complex.I G) y+
      covariance (directional 1 F) (directional 1 G) y+
      (parameter q a/(y.val:ℂ)^2)*covariance F G y+
      (1/(y.val:ℂ)^2)*covariance S G y
  linear_combination he

/-- The native mean product is restored exactly, separately from the nonconstant current. -/
theorem nativePairCurrent_decomposition (q : XiZeroCopy) (a b : Bool) (y : Ioi (0:ℝ)) :
    coefficient 1 0 (fun z => directional Complex.I (D4BMCuspResponse.responsePlanar q a) z*
      D4BMCuspResponse.responsePlanar q b z) y =
      deriv (responseMode q a 0) y*responseMode q b 0 y+nativePairCurrent q a b y := by
  have hd := (coefficient_hasDerivAt 1 (by norm_num) 0
    ((D4BMCuspResponse.responsePlanar_smooth q a).of_le (WithTop.coe_le_coe.mpr le_top)) y.2).deriv
  change deriv (responseMode q a 0) y=coefficient 1 0
    (directional Complex.I (D4BMCuspResponse.responsePlanar q a)) y at hd
  rw [hd]
  unfold nativePairCurrent covariance responseMode
  ring

private def variance (F : ℂ → ℂ) (y : ℝ) : ℝ := cellVariance (fun x => F (point x y))

private theorem variance_nonneg {F : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) : 0 ≤ variance F y := by
  change 0 ≤ cellVariance (fun x => F (point x y))
  rw [← cell_centered_square (slice_continuous hf hy)]
  exact integral_nonneg (fun _ => Complex.normSq_nonneg _)

private theorem covariance_bound {F G : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im})
    (hg : ContinuousOn G {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    2*‖covariance F G y‖ ≤ variance F y+variance G y := by
  simpa only [covariance,coefficient_zero_integral,cellCovariance,variance] using
    cellCovariance_bound (slice_continuous hf hy) (slice_continuous hg hy)

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

/-- Pointwise control of the original bilinear current by admitted native energies. -/
theorem nativePairCurrent_bound (q : XiZeroCopy) (a b : Bool) (y : Ioi (0:ℝ)) :
    2*‖nativePairCurrent q a b y‖ ≤ nonconstantEnergy q a y+nonconstantMass q b y := by
  have hf := D4BMCuspResponse.responsePlanar_smooth q a
  have hg := D4BMCuspResponse.responsePlanar_smooth q b
  have hv := (directional_smooth hf Complex.I).continuousOn
  have hh := (directional_smooth hf (1:ℂ)).continuousOn
  have h := covariance_bound hv hg.continuousOn y.2
  rw [native_variance q b y] at h
  have he := native_gradient_variance q a y
  have hnv := variance_nonneg hv y.2
  have hnh := variance_nonneg hh y.2
  change 2*‖nativePairCurrent q a b y‖ ≤ _ at h
  linarith only [h,he,hnv,hnh]

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

/-- The complete native derivative density is controlled by both branch energies
and the complete original forcing mass, without deleting the source-work term. -/
theorem nativePairDensity_bound (q : XiZeroCopy) (a b : Bool) (y : Ioi (1:ℝ)) :
    2*‖nativePairDensity q a b y‖ ≤ nonconstantEnergy q a y+nonconstantEnergy q b y+
      (‖parameter q a‖+1)*(nonconstantMass q a y+nonconstantMass q b y)+
      y.val^4*forcingMass q a y := by
  have hy0 : 0 < y.val := lt_trans zero_lt_one y.2
  let z : Ioi (0:ℝ) := ⟨y.val,hy0⟩
  let F := D4BMCuspResponse.responsePlanar q a
  let G := D4BMCuspResponse.responsePlanar q b
  let S := globalForcing q a ∘ ofComplex
  have hf := D4BMCuspResponse.responsePlanar_smooth q a
  have hg := D4BMCuspResponse.responsePlanar_smooth q b
  have hs := (globalForcing_smooth q a).planar_contDiffOn
  have hva := (directional_smooth hf Complex.I).continuousOn
  have hvb := (directional_smooth hg Complex.I).continuousOn
  have hha := (directional_smooth hf (1:ℂ)).continuousOn
  have hhb := (directional_smooth hg (1:ℂ)).continuousOn
  have hv := covariance_bound hva hvb hy0
  have hh := covariance_bound hha hhb hy0
  have hm := covariance_bound hf.continuousOn hg.continuousOn hy0
  have hw := covariance_bound hs.continuousOn hg.continuousOn hy0
  rw [native_variance q a z,native_variance q b z] at hm
  rw [native_variance q b z] at hw
  have heA := native_gradient_variance q a z
  have heB := native_gradient_variance q b z
  have hnA := variance_nonneg hva hy0
  have hnB := variance_nonneg hvb hy0
  have hforce := forcing_variance_bound q a z
  have hcoef : ‖(1:ℂ)/(y.val:ℂ)^2‖ ≤ 1 := by
    rw [norm_div,norm_one,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy0]
    apply (div_le_one (sq_pos_of_pos hy0)).mpr
    have hy1 : 1 < y.val := y.2
    nlinarith only [hy1,sq_nonneg (y.val-1)]
  have hpcoef : ‖parameter q a/(y.val:ℂ)^2‖ ≤ ‖parameter q a‖ := by
    have he : parameter q a/(y.val:ℂ)^2=parameter q a*((1:ℂ)/(y.val:ℂ)^2) := by ring
    rw [he,norm_mul]
    exact (mul_le_mul_of_nonneg_left hcoef (norm_nonneg _)).trans_eq (mul_one _)
  have hp := mul_le_mul_of_nonneg_right hpcoef (norm_nonneg (covariance F G y))
  have hscoef := mul_le_mul_of_nonneg_right hcoef (norm_nonneg (covariance S G y))
  have hmcoef := mul_le_mul_of_nonneg_left hm (norm_nonneg (parameter q a))
  have hnorm := norm_add_le
    (covariance (directional Complex.I F) (directional Complex.I G) y+
      covariance (directional 1 F) (directional 1 G) y+
      (parameter q a/(y.val:ℂ)^2)*covariance F G y)
    ((1/(y.val:ℂ)^2)*covariance S G y)
  have hnorm2 := norm_add_le
    (covariance (directional Complex.I F) (directional Complex.I G) y+
      covariance (directional 1 F) (directional 1 G) y)
    ((parameter q a/(y.val:ℂ)^2)*covariance F G y)
  have hnorm3 := norm_add_le
    (covariance (directional Complex.I F) (directional Complex.I G) y)
    (covariance (directional 1 F) (directional 1 G) y)
  rw [norm_mul] at hnorm hnorm2
  change ‖nativePairDensity q a b y‖ ≤ _ at hnorm
  have hnM : 0 ≤ nonconstantMass q a y := tsum_nonneg (fun _ => Complex.normSq_nonneg _)
  linarith only [hv,hh,hw,heA,heB,hnA,hnB,hforce,hp,hscoef,hmcoef,hnorm,hnorm2,hnorm3,hnM]

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

theorem covariance_continuousOn {F G : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im})
    (hg : ContDiffOn ℝ ∞ G {z : ℂ | 0 < z.im}) :
    ContinuousOn (covariance F G) (Ioi (0:ℝ)) :=
  fun _ hy => (covariance_hasDerivAt hf hg hy).continuousAt.continuousWithinAt

private theorem pair_continuousOn (q : XiZeroCopy) (a b : Bool) :
    ContinuousOn (nativePairCurrent q a b) (Ioi (0:ℝ)) :=
  fun y hy => (nativePairCurrent_hasDerivAt q a b ⟨y,hy⟩).continuousAt.continuousWithinAt

private theorem density_continuousOn (q : XiZeroCopy) (a b : Bool) :
    ContinuousOn (nativePairDensity q a b) (Ioi (0:ℝ)) := by
  have hf := D4BMCuspResponse.responsePlanar_smooth q a
  have hg := D4BMCuspResponse.responsePlanar_smooth q b
  have hs := (globalForcing_smooth q a).planar_contDiffOn
  have hv := covariance_continuousOn (directional_smooth hf Complex.I) (directional_smooth hg Complex.I)
  have hh := covariance_continuousOn (directional_smooth hf 1) (directional_smooth hg 1)
  have hm := covariance_continuousOn hf hg
  have hw := covariance_continuousOn hs hg
  have hp : ContinuousOn (fun y : ℝ => (y:ℂ)^2) (Ioi (0:ℝ)) :=
    Complex.continuous_ofReal.continuousOn.pow 2
  have hn (y : ℝ) (hy : y ∈ Ioi (0:ℝ)) : (y:ℂ)^2 ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hy))
  exact ((hv.add hh).add ((continuousOn_const.div hp hn).mul hm)).add
    ((continuousOn_const.div hp hn).mul hw)

private theorem source_bounds (q : XiZeroCopy) (a b : Bool) (y : Ioi (1:ℝ)) :
    ‖nativePairCurrent q a b y‖ ≤ nonconstantEnergy q a y+nonconstantEnergy q b y ∧
    ‖nativePairDensity q a b y‖ ≤ (‖parameter q a‖+2)*
      (nonconstantEnergy q a y+nonconstantEnergy q b y)+y.val^4*forcingMass q a y := by
  have hy0 : 0 < y.val := lt_trans (show (0:ℝ)<1 from zero_lt_one) (show 1 < y.val from y.2)
  let z : Ioi (0:ℝ) := ⟨y.val,hy0⟩
  have hma := native_mass_le_energy q a z
  have hmb := native_mass_le_energy q b z
  have hj := nativePairCurrent_bound q a b z
  have hd := nativePairDensity_bound q a b y
  have hcmp := mul_le_mul_of_nonneg_left (add_le_add hma hmb)
    (show 0 ≤ ‖parameter q a‖+1 by positivity)
  constructor
  · linarith only [hj,hmb,norm_nonneg (nativePairCurrent q a b y)]
  · linarith only [hd,hcmp,norm_nonneg (nativePairDensity q a b y)]

private theorem inverse_square_integrable {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun y : ℝ => 1/y^2) (Ioi T) := by
  have h := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hT
  apply h.congr_fun ?_ measurableSet_Ioi
  intro y hy
  change y^(-(2:ℝ))=1/y^2
  rw [Real.rpow_neg (le_of_lt (lt_trans hT hy)),Real.rpow_two,one_div]

private theorem polynomial_pair_hasDerivAt (q : XiZeroCopy) (a b : Bool) (N : ℕ)
    (y : Ioi (0:ℝ)) :
    HasDerivAt (fun t : ℝ => (t:ℂ)^N*nativePairCurrent q a b t)
      ((N:ℂ)*(y.val:ℂ)^(N-1)*nativePairCurrent q a b y+
        (y.val:ℂ)^N*nativePairDensity q a b y) y := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := y.val)).pow N).mul
    (nativePairCurrent_hasDerivAt q a b y)
  change HasDerivAt (fun t : ℝ => (t:ℂ)^N*nativePairCurrent q a b t)
    ((N:ℂ)*(y.val:ℂ)^(N-1)*(1:ℂ)*nativePairCurrent q a b y+
      (y.val:ℂ)^N*nativePairDensity q a b y) y at h
  simpa only [mul_one] using h

private theorem polynomial_pair_admission (q : XiZeroCopy) (a b : Bool) (N : ℕ) :
    ∃ T : ℝ, 4 ≤ T ∧
      IntegrableOn (fun y : ℝ => (y:ℂ)^N*nativePairCurrent q a b y) (Ioi T) ∧
      IntegrableOn (fun y : ℝ => (N:ℂ)*(y:ℂ)^(N-1)*nativePairCurrent q a b y+
        (y:ℂ)^N*nativePairDensity q a b y) (Ioi T) := by
  obtain ⟨A,hA,hia,_⟩ := nativeNonconstantEnergy_admission q a N
  obtain ⟨B,hB,hib,_⟩ := nativeNonconstantEnergy_admission q b N
  obtain ⟨C,hC,hforce⟩ := forcingMass_weighted_bound q a (N+2)
  let T := max (A+1) (max (B+1) 4)
  have hTA : A+1 ≤ T := le_max_left _ _
  have hTB : B+1 ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hT : 4 ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hypos (y : ℝ) (hy : y ∈ Ioi T) : 0 < y := lt_trans hT0 hy
  have hyeq (y : ℝ) (hy : y ∈ Ioi T) : 1 < y := lt_of_lt_of_le (by norm_num : (1:ℝ)<4) (hT.trans hy.le)
  have hsub : Ioi T ⊆ Ioi (0:ℝ) := fun y hy => hypos y hy
  let W : ℝ → ℝ := fun y => y^(2*(N+1))*(nonconstantEnergy q a y+nonconstantEnergy q b y)
  have hiW : IntegrableOn W (Ioi T) := by
    have hia' := hia.mono_set (Ioi_subset_Ioi hTA)
    have hib' := hib.mono_set (Ioi_subset_Ioi hTB)
    convert hia'.add hib' using 1 <;> try rfl
    funext y
    change y^(2*(N+1))*(nonconstantEnergy q a y+nonconstantEnergy q b y)=
      y^(2*(N+1))*nonconstantEnergy q a y+y^(2*(N+1))*nonconstantEnergy q b y
    ring
  let K : ℝ := ‖parameter q a‖+2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hbound (y : ℝ) (hy : y ∈ Ioi T) :
      ‖(y:ℂ)^N*nativePairCurrent q a b y‖ ≤ W y ∧
      ‖(N:ℂ)*(y:ℂ)^(N-1)*nativePairCurrent q a b y+
        (y:ℂ)^N*nativePairDensity q a b y‖ ≤ ((N:ℝ)+K)*W y+C*(1/y^2) := by
    have hy0 := hypos y hy
    have hy1 := hyeq y hy
    have hy3 : 3 < y := lt_of_lt_of_le (by norm_num : (3:ℝ)<4) (hT.trans hy.le)
    have hE : 0 ≤ nonconstantEnergy q a y+nonconstantEnergy q b y :=
      add_nonneg (energy_nonneg q a y) (energy_nonneg q b y)
    obtain ⟨hj,hd⟩ := source_bounds q a b ⟨y,hy1⟩
    have hPN : y^N ≤ y^(2*(N+1)) := pow_le_pow_right₀ hy1.le (by omega)
    have hPm : y^(N-1) ≤ y^(2*(N+1)) := pow_le_pow_right₀ hy1.le (by omega)
    have hJ : y^N*‖nativePairCurrent q a b y‖ ≤ W y :=
      (mul_le_mul_of_nonneg_left hj (pow_nonneg hy0.le N)).trans
        (mul_le_mul_of_nonneg_right hPN hE)
    have hJm : y^(N-1)*‖nativePairCurrent q a b y‖ ≤ W y :=
      (mul_le_mul_of_nonneg_left hj (pow_nonneg hy0.le (N-1))).trans
        (mul_le_mul_of_nonneg_right hPm hE)
    have hF0 : 0 ≤ forcingMass q a y := by
      rw [← (forcingLoss_hasSum q a ⟨y,hy0⟩).tsum_eq]
      exact tsum_nonneg (fun _ => div_nonneg (Complex.normSq_nonneg _) (pow_nonneg hy0.le 4))
    have hFp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hy1.le (show N+6 ≤ 2*(N+2)+4 by omega)) hF0
    have hF : y^N*(y^4*forcingMass q a y) ≤ C/y^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hy0)).mpr
      calc
        _ = y^(N+6)*forcingMass q a y := by
          rw [show N+6=(N+4)+2 by omega,pow_add,pow_add]
          ring
        _ ≤ y^(2*(N+2)+4)*forcingMass q a y := hFp
        _ ≤ C := hforce ⟨y,hy3⟩
    have hD0 := mul_le_mul_of_nonneg_left hd (pow_nonneg hy0.le N)
    have hDW := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPN hE) hK
    have hD : y^N*‖nativePairDensity q a b y‖ ≤ K*W y+C/y^2 := by
      change y^N*‖nativePairDensity q a b y‖ ≤ y^N*(K*(nonconstantEnergy q a y+nonconstantEnergy q b y)+y^4*forcingMass q a y) at hD0
      change K*(y^N*(nonconstantEnergy q a y+nonconstantEnergy q b y)) ≤ K*W y at hDW
      nlinarith only [hD0,hDW,hF]
    have hnorm := norm_add_le ((N:ℂ)*(y:ℂ)^(N-1)*nativePairCurrent q a b y)
      ((y:ℂ)^N*nativePairDensity q a b y)
    simp only [norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy0] at hnorm ⊢
    refine ⟨hJ,?_⟩
    have hNJ := mul_le_mul_of_nonneg_left hJm (Nat.cast_nonneg (α := ℝ) N)
    rw [show C*(1/y^2)=C/y^2 by ring]
    nlinarith only [hnorm,hNJ,hD]
  have hcP : ContinuousOn (fun y : ℝ => (y:ℂ)^N) (Ioi T) :=
    Complex.continuous_ofReal.continuousOn.pow N
  have hcM : ContinuousOn (fun y : ℝ => (y:ℂ)^(N-1)) (Ioi T) :=
    Complex.continuous_ofReal.continuousOn.pow (N-1)
  have hcJ := (pair_continuousOn q a b).mono hsub
  have hcD := (density_continuousOn q a b).mono hsub
  have hjm : AEStronglyMeasurable (fun y : ℝ => (y:ℂ)^N*nativePairCurrent q a b y)
      (volume.restrict (Ioi T)) := (hcP.mul hcJ).aestronglyMeasurable measurableSet_Ioi
  have hdm : AEStronglyMeasurable (fun y : ℝ => (N:ℂ)*(y:ℂ)^(N-1)*nativePairCurrent q a b y+
      (y:ℂ)^N*nativePairDensity q a b y) (volume.restrict (Ioi T)) :=
    (((hcM.const_mul (N:ℂ)).mul hcJ).add (hcP.mul hcD)).aestronglyMeasurable measurableSet_Ioi
  have hiR : IntegrableOn (fun y : ℝ => ((N:ℝ)+K)*W y+C*(1/y^2)) (Ioi T) :=
    (hiW.const_mul ((N:ℝ)+K)).add ((inverse_square_integrable hT0).const_mul C)
  refine ⟨T,hT,hiW.mono' hjm ?_,hiR.mono' hdm ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (hbound y hy).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (hbound y hy).2

/-- Every polynomially weighted native nonconstant bilinear current has zero upper
cusp trace. Both required integrabilities come from the original forced response. -/
theorem nativePairCurrent_weighted_tendsto_zero (q : XiZeroCopy) (a b : Bool) (N : ℕ) :
    Tendsto (fun y : ℝ => (y:ℂ)^N*nativePairCurrent q a b y) atTop (𝓝 0) := by
  obtain ⟨T,hT,hiJ,hiD⟩ := polynomial_pair_admission q a b N
  apply tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi ?_ hiD hiJ
  intro y hy
  have hy0 : 0 < y := lt_trans (lt_of_lt_of_le (by norm_num : (0:ℝ)<4) hT) hy
  exact polynomial_pair_hasDerivAt q a b N ⟨y,hy0⟩

theorem coefficient_zero_cusp_mean (F : ℂ → ℂ) (y : ℝ)
    (hp : ∀ x : ℝ, F (point (x+1) y)=F (point x y)) :
    coefficient 1 0 F y=D4BMCuspResponse.average F y := by
  rw [coefficient_zero_integral]
  change (∫ x in Ioc (0:ℝ) 1, F (point x y))=
    ∫ x in Ioc (-1/2:ℝ) (1/2), F (point x y)
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    ← intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2)]
  have hper : Function.Periodic (fun x : ℝ => F (point x y)) 1 := hp
  simpa only [zero_add,show (-1/2:ℝ)+1=1/2 by ring] using hper.intervalIntegral_add_eq 0 (-1/2)

private theorem native_mode_zero_eq_mean (q : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    responseMode q b 0 y=D4BMCuspResponse.responseMean q b y :=
  coefficient_zero_cusp_mean _ y (D4BMCuspResponse.responsePlanar_periodic q b y.2)

private theorem native_mode_zero_derivative (q : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    deriv (responseMode q b 0) y=deriv (D4BMCuspResponse.responseMean q b) y := by
  have h := coefficient_hasDerivAt 1 (by norm_num) 0
    ((D4BMCuspResponse.responsePlanar_smooth q b).of_le (WithTop.coe_le_coe.mpr le_top)) y.2
  have hm : HasDerivAt (D4BMCuspResponse.responseMean q b)
      (coefficient 1 0 (directional Complex.I (D4BMCuspResponse.responsePlanar q b)) y) y := by
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds y.2] with t ht
    exact (native_mode_zero_eq_mean q b ⟨t,ht⟩).symm
  exact h.deriv.trans hm.deriv.symm

private theorem native_vertical_periodic (q : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) (x : ℝ) :
    directional Complex.I (D4BMCuspResponse.responsePlanar q b) (point (x+1) y)=
      directional Complex.I (D4BMCuspResponse.responsePlanar q b) (point x y) := by
  have hf := (D4BMCuspResponse.responsePlanar_smooth q b).of_le
    (show (1 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have h := slice_vertical hf (x+1) y.2
  have hh : HasDerivAt (fun t => D4BMCuspResponse.responsePlanar q b (point x t))
      (directional Complex.I (D4BMCuspResponse.responsePlanar q b) (point (x+1) y)) y := by
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds y.2] with t ht
    exact (D4BMCuspResponse.responsePlanar_periodic q b ht x).symm
  exact hh.unique (slice_vertical hf x y.2)

/-- Original native bilinear flux on the source's cusp cell, before discarding any mean. -/
def nativeCuspFlux (q : XiZeroCopy) (a b : Bool) : ℝ → ℂ :=
  D4BMCuspResponse.average (fun z => directional Complex.I (D4BMCuspResponse.responsePlanar q a) z*
    D4BMCuspResponse.responsePlanar q b z)

/-- The actual source-cell flux splits into its retained original mean and the controlled current. -/
theorem nativeCuspFlux_decomposition (q : XiZeroCopy) (a b : Bool) (y : Ioi (0:ℝ)) :
    nativeCuspFlux q a b y=deriv (D4BMCuspResponse.responseMean q a) y*
      D4BMCuspResponse.responseMean q b y+nativePairCurrent q a b y := by
  have hp (x : ℝ) :
      directional Complex.I (D4BMCuspResponse.responsePlanar q a) (point (x+1) y)*
        D4BMCuspResponse.responsePlanar q b (point (x+1) y)=
      directional Complex.I (D4BMCuspResponse.responsePlanar q a) (point x y)*
        D4BMCuspResponse.responsePlanar q b (point x y) := by
    exact congrArg₂ (·*·) (native_vertical_periodic q a y x)
      (D4BMCuspResponse.responsePlanar_periodic q b y.2 x)
  have h := nativePairCurrent_decomposition q a b y
  rw [coefficient_zero_cusp_mean _ y hp,native_mode_zero_derivative q a y,
    native_mode_zero_eq_mean q b y] at h
  exact h

/-- The complete native cusp-cell flux approaches its original mean product with
all polynomial weights. The mean product itself is not set to zero. -/
theorem nativeCuspFlux_remainder_weighted_tendsto_zero (q : XiZeroCopy) (a b : Bool) (N : ℕ) :
    Tendsto (fun y : ℝ => (y:ℂ)^N*(nativeCuspFlux q a b y-
      deriv (D4BMCuspResponse.responseMean q a) y*D4BMCuspResponse.responseMean q b y)) atTop (𝓝 0) := by
  apply (nativePairCurrent_weighted_tendsto_zero q a b N).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  rw [nativeCuspFlux_decomposition q a b ⟨y,hy⟩,add_sub_cancel_left]

end
end RHTower.D4BMQuarticNativeCuspCurrent
