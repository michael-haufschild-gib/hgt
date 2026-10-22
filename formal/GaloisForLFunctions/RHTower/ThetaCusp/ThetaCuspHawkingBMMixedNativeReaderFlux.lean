import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticTestedNativeCurrent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticCuspFluxDecay
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedQuadraticCurrent

/-!
# Source-derived native extinction at the mixed current's angular cusp face

The original forced native response, its complete nonconstant energy, and the
independent physical reader imply absolute integrability of the ordered
native/reader current and its derivative. Horizontal periodicity retains the
original forcing term in the differentiated identity. The upper trace is zero.
The reversed ordered product is controlled separately by native mass decay.

The native mean is restored using the source-selected stable indicial root and
all forcing tails. Both mean products also decay at the unchanged physical
reader parameter. Thus the full coefficient-weighted native Green flux vanishes.
The actual mixed source current consequently has precisely its particular
response and full squared-source cusp flux left at this face.

These are unconditional identities and estimates for the original angular
response and reader. The particular/square flux is not set to zero. The other
causal faces, independent nonlinear channels, complete physical action and
fixed Hawking-clock extinction remain separate obligations.
-/

open scoped ContDiff
open MeasureTheory Set Filter Topology UpperHalfPlane
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.SelbergMaassMean
open GaloisForLFunctions.RHTower.SelbergMaassFourier
open GaloisForLFunctions.RHTower.SelbergMaassParseval
namespace RHTower.D4BMMixedNativeReaderFlux
open D4BMModularCore D4BMGlobalAngularResponse D4BMQuarticNativeCuspModes
open D4BMQuarticNativeCuspComparison D4BMQuarticNativeCuspEnergy
open D4BMQuarticTestedNativeCurrent D4BMJointSource
open D4BMQuarticNativeCuspCurrent (covariance)
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

private theorem cellCovariance_centered {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
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

private theorem coefficient_zero_integral (F : ℂ → ℂ) (y : ℝ) :
    coefficient 1 0 F y=cellMean (fun x => F (point x y)) := by
  simp only [coefficient,deningerFourierCoeff,deningerFourierKernel,Int.cast_zero,
    mul_zero,zero_mul,neg_zero,Complex.exp_zero,Complex.ofReal_one,div_one,one_mul]
  change (∫ x in (0:ℝ)..1, F (point x y))=∫ x in Ioc (0:ℝ) 1, F (point x y)
  exact intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)

private theorem coefficient_zero_linear {F G : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im})
    (hg : ContinuousOn G {z : ℂ | 0 < z.im}) (c d : ℂ)
    {y : ℝ} (hy : 0 < y) :
    coefficient 1 0 (fun z => c*F z+d*G z) y =
      c*coefficient 1 0 F y+d*coefficient 1 0 G y := by
  simp only [coefficient_zero_integral,cellMean]
  rw [integral_add ((cell_integrable (slice_continuous hf hy)).const_mul c)
    ((cell_integrable (slice_continuous hg hy)).const_mul d),integral_const_mul,integral_const_mul]

private theorem covariance_linear_left {F G H : ℂ → ℂ}
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

private theorem covariance_slice_congr {F G H : ℂ → ℂ} {y : ℝ}
    (he : ∀ x : ℝ, F (point x y)=G (point x y)) : covariance F H y=covariance G H y := by
  simp only [covariance,coefficient_zero_integral,cellMean]
  congr 1
  · exact integral_congr_ae (Filter.Eventually.of_forall (fun x => congrArg (fun z => z*H (point x y)) (he x)))
  · congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall he)

private theorem covariance_hasDerivAt {F G : ℂ → ℂ}
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

private theorem covariance_horizontal_second {F G : ℂ → ℂ}
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


private theorem physicalTest_smooth (q : XiZeroCopy) :
    ContDiffOn ℝ ∞ (physicalTest q) {z : ℂ | 0 < z.im} := by
  intro z hz
  have h := (D4BMAngularSeries.cuspLeg_contDiffOn .scalar (physicalAngularParameter q)).contDiffAt
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



private theorem weighted_young (z w : ℂ) {y : ℝ} (hy : 0 < y) :
    2*‖z*w‖ ≤ y^4*Complex.normSq z+Complex.normSq w/y^4 := by
  have hn : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have h := complex_young ((y:ℂ)^2*z) (w/(y:ℂ)^2)
  have he : ((y:ℂ)^2*z)*(w/(y:ℂ)^2)=z*w := by field_simp
  rw [he,Complex.normSq_mul,Complex.normSq_div,map_pow,
    Complex.normSq_ofReal] at h
  simpa only [show (y*y)^2=y^4 by ring] using h

private theorem covariance_weighted_bound {F G : ℂ → ℂ}
    (hf : ContinuousOn F {z : ℂ | 0 < z.im})
    (hg : ContinuousOn G {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    2*‖covariance F G y‖ ≤ y^4*variance F y+variance G y/y^4 := by
  let f : ℝ → ℂ := fun x => F (point x y)
  let g : ℝ → ℂ := fun x => G (point x y)
  have cf := slice_continuous hf hy
  have cg := slice_continuous hg hy
  have cfc : Continuous (fun x => f x-cellMean f) := cf.sub continuous_const
  have cgc : Continuous (fun x => g x-cellMean g) := cg.sub continuous_const
  have hi := cell_integrable (cfc.mul cgc)
  have hn := norm_integral_le_integral_norm (μ := volume.restrict cell)
    (fun x => (f x-cellMean f)*(g x-cellMean g))
  have hb := integral_mono (hi.norm.const_mul 2)
    (((cell_normSq_integrable cfc).const_mul (y^4)).add
      ((cell_normSq_integrable cgc).div_const (y^4)))
    (fun x => weighted_young (f x-cellMean f) (g x-cellMean g) hy)
  change (∫ x in cell, 2*‖(f x-cellMean f)*(g x-cellMean g)‖) ≤
    ∫ x in cell, y^4*Complex.normSq (f x-cellMean f)+Complex.normSq (g x-cellMean g)/y^4 at hb
  have hiF : IntegrableOn (fun x => y^4*Complex.normSq (f x-cellMean f)) cell :=
    (cell_normSq_integrable cfc).const_mul (y^4)
  have hiG : IntegrableOn (fun x => Complex.normSq (g x-cellMean g)/y^4) cell :=
    (cell_normSq_integrable cgc).div_const (y^4)
  rw [integral_const_mul,integral_add hiF hiG,integral_const_mul,integral_div,
    cell_centered_square cf,cell_centered_square cg] at hb
  have he : covariance F G y=cellCovariance f g := by
    simp only [covariance,coefficient_zero_integral,cellCovariance,f,g]
  rw [he,cellCovariance_centered cf cg]
  change 2*‖∫ x in cell, (f x-cellMean f)*(g x-cellMean g)‖ ≤
    y^4*cellVariance f+cellVariance g/y^4
  linarith only [hn,hb]

private theorem variance_pointwise_bound {G : ℂ → ℂ}
    (hg : ContinuousOn G {z : ℂ | 0 < z.im}) {y B : ℝ} (hy : 0 < y)
    (hB : 0 ≤ B) (hb : ∀ x : ℝ, ‖G (point x y)‖≤B) : variance G y≤B^2 := by
  have hi := cell_normSq_integrable (slice_continuous hg hy)
  have hm := integral_mono hi
    (cell_normSq_integrable (continuous_const (y := (B:ℂ)))) (fun x => by
      simp only [Complex.normSq_eq_norm_sq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB]
      exact (sq_le_sq₀ (norm_nonneg _) hB).mpr (hb x))
  change (∫ x in cell, Complex.normSq (G (point x y))) ≤
    ∫ _x in cell, Complex.normSq (B:ℂ) at hm
  rw [cell_const_real,Complex.normSq_ofReal] at hm
  unfold variance cellVariance
  nlinarith only [hm,Complex.normSq_nonneg (cellMean (fun x => G (point x y)))]

/-- The ordered native/reader boundary current retains every nonconstant mode. -/
def readerCurrent (q r : XiZeroCopy) (b : Bool) : ℝ → ℂ :=
  covariance (directional Complex.I (D4BMCuspResponse.responsePlanar q b)) (physicalTest r)

/-- All derivative, original-forcing and metric-parameter terms after horizontal Stokes. -/
def readerDensity (q r : XiZeroCopy) (b : Bool) (y : ℝ) : ℂ :=
  covariance (directional Complex.I (D4BMCuspResponse.responsePlanar q b))
    (directional Complex.I (physicalTest r)) y+
  covariance (directional 1 (D4BMCuspResponse.responsePlanar q b))
    (directional 1 (physicalTest r)) y+
  (parameter q b/(y:ℂ)^2)*covariance (D4BMCuspResponse.responsePlanar q b) (physicalTest r) y+
  (1/(y:ℂ)^2)*covariance (globalForcing q b ∘ ofComplex) (physicalTest r) y

/-- The complete literal forcing proves the actual reader-current derivative. -/
theorem readerCurrent_hasDerivAt (q r : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    HasDerivAt (readerCurrent q r b) (readerDensity q r b y) y := by
  let F := D4BMCuspResponse.responsePlanar q b
  let G := physicalTest r
  let S := globalForcing q b ∘ ofComplex
  have hf := D4BMCuspResponse.responsePlanar_smooth q b
  have hg := physicalTest_smooth r
  have hs := (globalForcing_smooth q b).planar_contDiffOn
  have hv := directional_smooth hf Complex.I
  have hh := directional_smooth hf (1:ℂ)
  have hvv := directional_smooth hv Complex.I
  have hhh := directional_smooth hh (1:ℂ)
  have hp (x : ℝ) :
      directional Complex.I (directional Complex.I F) (point x y)+
        directional 1 (directional 1 F) (point x y) =
      (parameter q b/(y.val:ℂ)^2)*F (point x y)+(1/(y.val:ℂ)^2)*S (point x y) := by
    have hx : 0 < (point x y).im := by simpa only [point,Complex.add_im,
      Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] using (show 0 < y.val from y.2)
    have he := globalResponse_classical_planar q b (point x y) hx
    have he' : directional 1 (directional 1 F) (point x y)+
        directional Complex.I (directional Complex.I F) (point x y) =
        (parameter q b*F (point x y)+S (point x y))/(y.val:ℂ)^2 := by
      change (fderiv ℝ (fun w => fderiv ℝ (globalResponse q b ∘ ofComplex) w 1) (point x y) 1+
        fderiv ℝ (fun w => fderiv ℝ (globalResponse q b ∘ ofComplex) w Complex.I)
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
    (parameter q b/(y.val:ℂ)^2) (1/(y.val:ℂ)^2) y.2
  have he := hl.symm.trans ((covariance_slice_congr (H := G) hp).trans hr)
  rw [covariance_horizontal_second hf hg y.2
    (D4BMCuspResponse.responsePlanar_periodic q b y.2)
    (physicalTest_periodic r y)] at he
  have hd := covariance_hasDerivAt hv hg y.2
  apply hd.congr_deriv
  change covariance (directional Complex.I (directional Complex.I F)) G y+
      covariance (directional Complex.I F) (directional Complex.I G) y =
    covariance (directional Complex.I F) (directional Complex.I G) y+
      covariance (directional 1 F) (directional 1 G) y+
      (parameter q b/(y.val:ℂ)^2)*covariance F G y+
      (1/(y.val:ℂ)^2)*covariance S G y
  linear_combination he


/-- One original source-derived bound controls the actual current and its derivative. -/
theorem reader_source_bounds (q r : XiZeroCopy) (b : Bool) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : Ioi (3:ℝ),
      ‖readerCurrent q r b y‖ ≤ y.val^4*nonconstantEnergy q b y+B/y.val^2 ∧
      ‖readerDensity q r b y‖ ≤ (‖parameter q b‖+3)*
        (y.val^4*nonconstantEnergy q b y+B/y.val^2) := by
  obtain ⟨C,hC,hjet⟩ := physicalTest_firstJet_bound r
  obtain ⟨D,hD,hforce⟩ := forcingMass_weighted_bound q b 3
  refine ⟨C^2+D,by positivity,?_⟩
  intro y
  have hy0 : 0 < y.val := lt_trans (by norm_num : (0:ℝ)<3) y.2
  have hy3 : 3 < y.val := y.2
  let z : Ioi (0:ℝ) := ⟨y.val,hy0⟩
  let F := D4BMCuspResponse.responsePlanar q b
  let R := physicalTest r
  let S := globalForcing q b ∘ ofComplex
  let W := y.val^4*nonconstantEnergy q b y+(C^2+D)/y.val^2
  have hf := D4BMCuspResponse.responsePlanar_smooth q b
  have hr := physicalTest_smooth r
  have hs := (globalForcing_smooth q b).planar_contDiffOn
  have hfv := (directional_smooth hf Complex.I).continuousOn
  have hfx := (directional_smooth hf 1).continuousOn
  have hrv := (directional_smooth hr Complex.I).continuousOn
  have hrx := (directional_smooth hr 1).continuousOn
  have hCY : 0 ≤ C*y.val := mul_nonneg hC hy0.le
  have hCy : C≤C*y.val := by nlinarith only [hC,hy3]
  have hR : variance R y ≤ (C*y.val)^2 :=
    variance_pointwise_bound hr.continuousOn hy0 hCY (fun x => (hjet y x).1)
  have hRv : variance (directional Complex.I R) y ≤ (C*y.val)^2 :=
    variance_pointwise_bound hrv hy0 hCY (fun x => (hjet y x).2.1.trans hCy)
  have hRx : variance (directional 1 R) y ≤ (C*y.val)^2 :=
    variance_pointwise_bound hrx hy0 hCY (fun x => (hjet y x).2.2.trans hCy)
  obtain ⟨hF,hFv,hFx⟩ := native_variance_bounds q b z
  have hS := forcing_variance_bound q b z
  have he : 0 ≤ y.val^4*nonconstantEnergy q b y :=
    mul_nonneg (pow_nonneg hy0.le 4) (energy_nonneg q b y)
  have htail : y.val^4*(y.val^4*forcingMass q b y) ≤ D/y.val^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hy0)).mpr
    calc
      _ = y.val^10*forcingMass q b y := by ring
      _ ≤ D := hforce y
  have hb {H K : ℂ → ℂ}
      (hh : ContinuousOn H {z : ℂ | 0 < z.im})
      (hk : ContinuousOn K {z : ℂ | 0 < z.im})
      (hH : variance H y ≤ nonconstantEnergy q b y)
      (hK : variance K y ≤ (C*y.val)^2) : 2*‖covariance H K y‖≤W := by
    have h := (covariance_weighted_bound hh hk hy0).trans
      (add_le_add (mul_le_mul_of_nonneg_left hH (pow_nonneg hy0.le 4))
        (div_le_div_of_nonneg_right hK (pow_nonneg hy0.le 4)))
    have hc : (C*y.val)^2/y.val^4=C^2/y.val^2 := by field_simp
    rw [hc] at h
    have hd := div_nonneg hD (sq_nonneg y.val)
    dsimp only [W]
    rw [add_div]
    linarith only [h,hd]
  have hj := hb hfv hr.continuousOn hFv hR
  have hv := hb hfv hrv hFv hRv
  have hx := hb hfx hrx hFx hRx
  have hm := hb hf.continuousOn hr.continuousOn hF hR
  have hw : 2*‖covariance S R y‖≤W := by
    have h := (covariance_weighted_bound hs.continuousOn hr.continuousOn hy0).trans
      (add_le_add (mul_le_mul_of_nonneg_left hS (pow_nonneg hy0.le 4))
        (div_le_div_of_nonneg_right hR (pow_nonneg hy0.le 4)))
    have hc : (C*y.val)^2/y.val^4=C^2/y.val^2 := by field_simp
    rw [hc] at h
    dsimp only [W]
    rw [add_div]
    linarith only [h,htail,he]
  have hcoef : ‖(1:ℂ)/(y.val:ℂ)^2‖≤1 := by
    rw [norm_div,norm_one,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy0]
    apply (div_le_one (sq_pos_of_pos hy0)).mpr
    nlinarith only [hy3,sq_nonneg (y.val-1)]
  have hpcoef : ‖parameter q b/(y.val:ℂ)^2‖≤‖parameter q b‖ := by
    rw [show parameter q b/(y.val:ℂ)^2=parameter q b*((1:ℂ)/(y.val:ℂ)^2) by ring,norm_mul]
    exact (mul_le_mul_of_nonneg_left hcoef (norm_nonneg _)).trans_eq (mul_one _)
  let V := covariance (directional Complex.I F) (directional Complex.I R) y
  let X := covariance (directional 1 F) (directional 1 R) y
  let M := covariance F R y
  let Z := covariance S R y
  have h1 := norm_add_le V X
  have h2 := norm_add_le (V+X) ((parameter q b/(y.val:ℂ)^2)*M)
  have h3 := norm_add_le (V+X+(parameter q b/(y.val:ℂ)^2)*M) (((1:ℂ)/(y.val:ℂ)^2)*Z)
  rw [norm_mul] at h2 h3
  have hpm := mul_le_mul_of_nonneg_right hpcoef (norm_nonneg M)
  have hfz := mul_le_mul_of_nonneg_right hcoef (norm_nonneg Z)
  have hmp := mul_le_mul_of_nonneg_left hm (norm_nonneg (parameter q b))
  change ‖readerDensity q r b y‖≤_ at h3
  refine ⟨?_,?_⟩
  · change 2*‖readerCurrent q r b y‖≤W at hj
    linarith only [hj,norm_nonneg (readerCurrent q r b y)]
  · change ‖readerDensity q r b y‖≤(‖parameter q b‖+3)*W
    change 2*‖V‖≤W at hv
    change 2*‖X‖≤W at hx
    change 2*‖Z‖≤W at hw
    change ‖parameter q b‖*(2*‖M‖)≤‖parameter q b‖*W at hmp
    nlinarith only [hv,hx,hw,hmp,h1,h2,h3,hpm,hfz,norm_nonneg (readerDensity q r b y)]

private theorem covariance_continuousOn {F G : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im})
    (hg : ContDiffOn ℝ ∞ G {z : ℂ | 0 < z.im}) :
    ContinuousOn (covariance F G) (Ioi (0:ℝ)) :=
  fun _ hy => (covariance_hasDerivAt hf hg hy).continuousAt.continuousWithinAt

private theorem pair_continuousOn (q r : XiZeroCopy) (b : Bool) :
    ContinuousOn (readerCurrent q r b) (Ioi (0:ℝ)) :=
  fun y hy => (readerCurrent_hasDerivAt q r b ⟨y,hy⟩).continuousAt.continuousWithinAt

private theorem density_continuousOn (q r : XiZeroCopy) (b : Bool) :
    ContinuousOn (readerDensity q r b) (Ioi (0:ℝ)) := by
  have hf := D4BMCuspResponse.responsePlanar_smooth q b
  have hg := physicalTest_smooth r
  have hs := (globalForcing_smooth q b).planar_contDiffOn
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

private theorem inverse_square_integrable {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun y : ℝ => 1/y^2) (Ioi T) := by
  have h := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hT
  apply h.congr_fun ?_ measurableSet_Ioi
  intro y hy
  change y^(-(2:ℝ))=1/y^2
  rw [Real.rpow_neg (le_of_lt (lt_trans hT hy)),Real.rpow_two,one_div]

/-- Both absolute integrabilities follow from original native energy and forcing. -/
theorem readerCurrent_admission (q r : XiZeroCopy) (b : Bool) :
    ∃ T : ℝ, 4 ≤ T ∧ IntegrableOn (readerCurrent q r b) (Ioi T) ∧
      IntegrableOn (readerDensity q r b) (Ioi T) := by
  obtain ⟨A,hA,hiE,_⟩ := nativeNonconstantEnergy_admission q b 1
  obtain ⟨B,hB,hbound⟩ := reader_source_bounds q r b
  let T := A+1
  have hT : 4 ≤ T := by dsimp only [T]; linarith only [hA]
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ)<4) hT
  let W : ℝ → ℝ := fun y => y^4*nonconstantEnergy q b y+B*(1/y^2)
  have hiW : IntegrableOn W (Ioi T) := hiE.add ((inverse_square_integrable hT0).const_mul B)
  have hsub : Ioi T ⊆ Ioi (0:ℝ) := fun y hy => lt_trans hT0 hy
  have hcJ := (pair_continuousOn q r b).mono hsub
  have hcD := (density_continuousOn q r b).mono hsub
  refine ⟨T,hT,hiW.mono' (hcJ.aestronglyMeasurable measurableSet_Ioi) ?_,
    (hiW.const_mul (‖parameter q b‖+3)).mono'
      (hcD.aestronglyMeasurable measurableSet_Ioi) ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy3 : 3 < y := lt_trans (lt_of_lt_of_le (by norm_num : (3:ℝ)<4) hT) hy
    simpa only [W,mul_one_div] using (hbound ⟨y,hy3⟩).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy3 : 3 < y := lt_trans (lt_of_lt_of_le (by norm_num : (3:ℝ)<4) hT) hy
    simpa only [W,mul_one_div] using (hbound ⟨y,hy3⟩).2

/-- The actual native derivative paired with the independent original reader
has zero nonconstant upper trace, derived without a boundary-value premise. -/
theorem readerCurrent_tendsto_zero (q r : XiZeroCopy) (b : Bool) :
    Tendsto (readerCurrent q r b) atTop (𝓝 0) := by
  obtain ⟨T,hT,hiJ,hiD⟩ := readerCurrent_admission q r b
  apply tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi ?_ hiD hiJ
  intro y hy
  exact readerCurrent_hasDerivAt q r b
    ⟨y,lt_trans (lt_of_lt_of_le (by norm_num : (0:ℝ)<4) hT) hy⟩

/-- The second ordered product in the native Green flux, with every nonconstant mode. -/
def readerReverseCurrent (q r : XiZeroCopy) (b : Bool) : ℝ → ℂ :=
  covariance (D4BMCuspResponse.responsePlanar q b) (directional Complex.I (physicalTest r))

/-- Native mass decay controls the differentiated original reader separately. -/
theorem readerReverseCurrent_tendsto_zero (q r : XiZeroCopy) (b : Bool) :
    Tendsto (readerReverseCurrent q r b) atTop (𝓝 0) := by
  obtain ⟨C,hC,hjet⟩ := physicalTest_firstJet_bound r
  have hm : Tendsto (fun y : ℝ => y^4*nonconstantMass q b y) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat] using nonconstantMass_weighted_tendsto_zero q b (4:ℝ)
  have ht : Tendsto (fun y : ℝ => C^2/y^4) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<4)).const_mul (C^2)
    apply (show Tendsto (fun y : ℝ => C^2*y^(-(4:ℝ))) atTop (𝓝 0) by simpa only [mul_zero] using h).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    rw [Real.rpow_neg hy.le,Real.rpow_ofNat]
    ring
  apply squeeze_zero_norm' ?_ (show Tendsto
    (fun y : ℝ => y^4*nonconstantMass q b y+C^2/y^4) atTop (𝓝 0) by
      simpa only [add_zero] using hm.add ht)
  filter_upwards [eventually_gt_atTop (3:ℝ)] with y hy
  have hy0 : 0 < y := lt_trans (by norm_num : (0:ℝ)<3) hy
  have hf := (D4BMCuspResponse.responsePlanar_smooth q b).continuousOn
  have hr := (directional_smooth (physicalTest_smooth r) Complex.I).continuousOn
  have hR := variance_pointwise_bound hr hy0 hC (fun x => (hjet ⟨y,hy⟩ x).2.1)
  have h := covariance_weighted_bound hf hr hy0
  rw [native_variance q b ⟨y,hy0⟩] at h
  have hh := div_le_div_of_nonneg_right hR (pow_nonneg hy0.le 4)
  change 2*‖readerReverseCurrent q r b y‖≤_ at h
  linarith only [h,hh,norm_nonneg (readerReverseCurrent q r b y)]

/-- All coefficient-weighted native nonconstant Green terms have zero upper trace. -/
theorem nativeGreenCovariance_tendsto_zero (q r : XiZeroCopy) (b : Bool) :
    Tendsto (fun y : ℝ =>
      (physicalAngularParameter r^2-1/4)*readerCurrent q r b y-
        parameter q b*readerReverseCurrent q r b y) atTop (𝓝 0) := by
  simpa only [mul_zero,sub_zero] using
    ((readerCurrent_tendsto_zero q r b).const_mul (physicalAngularParameter r^2-1/4)).sub
      ((readerReverseCurrent_tendsto_zero q r b).const_mul (parameter q b))

open D4BMCuspResponse hiding point
open D4BMQuarticCuspFluxDecay

/-- The original native mean retains only its stable coefficient and rapidly
weighted complete forcing tails; no endpoint coefficient is postulated. -/
theorem nativeMean_weighted_remainder (q : XiZeroCopy) (b : Bool) (w : ℂ) :
    Tendsto (fun y : ℝ => (y:ℂ)^w*(responseMean q b y-
      (y:ℂ)^(root q b false)*limitingCoefficient q b false)) atTop (𝓝 0) := by
  have h := ((weighted_source_tail_tendsto_zero q b true (w+root q b false)).sub
    (weighted_source_tail_tendsto_zero q b false (w+root q b true))).div_const (rootGap q b)
  apply (show Tendsto (fun y : ℝ =>
      ((y:ℂ)^(w+root q b false)*(∫ t in Ioi y, fluxSource q b true t)-
        (y:ℂ)^(w+root q b true)*(∫ t in Ioi y, fluxSource q b false t))/rootGap q b)
      atTop (𝓝 0) by simpa only [sub_zero,zero_div] using h).congr'
  filter_upwards [eventually_gt_atTop (3:ℝ)] with y hy
  have hn : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith : 0 < y))
  rw [responseMean_native_decomposition q b hy,Complex.cpow_add _ _ hn,Complex.cpow_add _ _ hn]
  ring

private theorem height_power_decay {w : ℂ} (hw : w.re < 0) :
    Tendsto (fun y : ℝ => (y:ℂ)^w) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (tendsto_rpow_neg_atTop (neg_pos.mpr hw))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

/-- The literal physical reader lies strictly below the native mean boundary threshold. -/
theorem nativeReader_exponent_negative (q r : XiZeroCopy) (b : Bool) :
    (root q b false-(r.1:ℂ)/2).re < 0 := by
  have hb := (D4BMCuspProjection.physicalRate_re_bounds q b).2
  have hr := (xi_divisor_support_re_mem_open_unit r.1).1
  norm_num [root,Complex.div_ofNat_re]
  linarith

/-- The original native mean paired with the physical reader's derivative weight vanishes. -/
theorem nativeMean_reader_weight_tendsto_zero (q r : XiZeroCopy) (b : Bool) :
    Tendsto (fun y : ℝ => (y:ℂ)^(-(r.1:ℂ)/2)*responseMean q b y) atTop (𝓝 0) := by
  have hr := nativeMean_weighted_remainder q b (-(r.1:ℂ)/2)
  have hp := (height_power_decay (nativeReader_exponent_negative q r b)).mul_const
    (limitingCoefficient q b false)
  apply (show Tendsto (fun y : ℝ =>
    (y:ℂ)^(-(r.1:ℂ)/2)*(responseMean q b y-(y:ℂ)^(root q b false)*limitingCoefficient q b false)+
      (y:ℂ)^(root q b false-(r.1:ℂ)/2)*limitingCoefficient q b false) atTop (𝓝 0) by
        simpa only [zero_mul,add_zero] using hr.add hp).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  have hn := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [show root q b false-(r.1:ℂ)/2=-(r.1:ℂ)/2+root q b false by ring,
    Complex.cpow_add _ _ hn]
  ring
/-- The derivative of the original native mean paired with the physical reader
also vanishes, using its exact forced indicial flux. -/
theorem nativeMean_derivative_reader_weight_tendsto_zero (q r : XiZeroCopy) (b : Bool) :
    Tendsto (fun y : ℝ => (y:ℂ)^(1-(r.1:ℂ)/2)*deriv (responseMean q b) y) atTop (𝓝 0) := by
  have hm := (nativeMean_reader_weight_tendsto_zero q r b).const_mul (root q b false)
  have ht := weighted_source_tail_tendsto_zero q b false (1-(r.1:ℂ)/2-root q b false)
  apply (show Tendsto (fun y : ℝ =>
    root q b false*((y:ℂ)^(-(r.1:ℂ)/2)*responseMean q b y)-
      (y:ℂ)^(1-(r.1:ℂ)/2-root q b false)*(∫ t in Ioi y, fluxSource q b false t))
    atTop (𝓝 0) by simpa only [mul_zero,sub_zero] using hm.sub ht).congr'
  filter_upwards [eventually_gt_atTop (3:ℝ)] with y hy
  have hn : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith : 0 < y))
  have h1 : (y:ℂ)^(1-(r.1:ℂ)/2-root q b false)*(y:ℂ)^(root q b false)=
      (y:ℂ)^(1-(r.1:ℂ)/2) := by rw [← Complex.cpow_add _ _ hn]; congr 1; ring
  have h2 : (y:ℂ)^(1-(r.1:ℂ)/2-root q b false)*(y:ℂ)^(root q b false-1)=
      (y:ℂ)^(-(r.1:ℂ)/2) := by rw [← Complex.cpow_add _ _ hn]; congr 1; ring
  have hf := congrArg (fun z : ℂ => (y:ℂ)^(1-(r.1:ℂ)/2-root q b false)*z)
    (responseFlux_first_eq_neg_source_tail q b hy)
  change (y:ℂ)^(1-(r.1:ℂ)/2-root q b false)*
    ((y:ℂ)^(root q b false)*deriv (responseMean q b) y-
      root q b false*(y:ℂ)^(root q b false-1)*responseMean q b y)=
    (y:ℂ)^(1-(r.1:ℂ)/2-root q b false)*(-(∫ t in Ioi y, fluxSource q b false t)) at hf
  rw [← h1,← h2]
  linear_combination -hf

private theorem coefficient_zero_cusp_mean (F : ℂ → ℂ) (y : ℝ)
    (hp : ∀ x : ℝ, F (point (x+1) y)=F (point x y)) :
    coefficient 1 0 F y=D4BMCuspResponse.average F y := by
  rw [coefficient_zero_integral]
  change (∫ x in Ioc (0:ℝ) 1, F (point x y))=
    ∫ x in Ioc (-1/2:ℝ) (1/2), F (point x y)
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    ← intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2)]
  have hper : Function.Periodic (fun x : ℝ => F (point x y)) 1 := hp
  simpa only [zero_add,show (-1/2:ℝ)+1=1/2 by ring] using hper.intervalIntegral_add_eq 0 (-1/2)

private theorem reader_mean (r : XiZeroCopy) (y : Ioi (0:ℝ)) :
    coefficient 1 0 (physicalTest r) y =
      reflectedCompletedLambda ((r.1:ℂ)-1)*(y.val:ℂ)^(1-(r.1:ℂ)/2) := by
  rw [coefficient_zero_cusp_mean _ y (physicalTest_periodic r y)]
  let u := physicalAngularParameter r
  have he (x : ℝ) : physicalTest r (point x y)=principal u ![0,y.val]+tail u ![x,y.val] := by
    simp [physicalTest,scalar,D4BMGlobalAngularResponse.principal,tail,d4BMCompletedEisensteinCuspLeg,
      angularCoordinates,point,u]
  have ht : Continuous (fun x : ℝ => tail u ![x,y.val]) := by
    have hh : (fun x : ℝ => tail u ![x,y.val])=
        fun x => physicalTest r (point x y)-principal u ![0,y.val] := by
      funext x
      rw [he]
      ring
    rw [hh]
    exact (GaloisForLFunctions.RHTower.SelbergMaassMean.slice_continuous
      (physicalTest_smooth r).continuousOn y.2).sub continuous_const
  change (∫ x in Ioc (-1/2:ℝ) (1/2), physicalTest r (point x y))=_
  simp_rw [he]
  rw [integral_add (integrable_const _) ht.integrableOn_Ioc]
  have hm := D4BMCuspProjection.mean_tail u y.2
  change (∫ x in Ioc (-1/2:ℝ) (1/2), tail u ![x,y.val])=0 at hm
  rw [hm,add_zero]
  norm_num
  exact physicalScalar_principal r ![0,y.val]

private theorem native_mean (q : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    coefficient 1 0 (responsePlanar q b) y=responseMean q b y :=
  coefficient_zero_cusp_mean _ y (responsePlanar_periodic q b y.2)

private theorem native_derivative_mean (q : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    coefficient 1 0 (directional Complex.I (responsePlanar q b)) y=deriv (responseMean q b) y := by
  have h := coefficient_hasDerivAt 1 (by norm_num) 0
    ((responsePlanar_smooth q b).of_le (WithTop.coe_le_coe.mpr le_top)) y.2
  have hm : HasDerivAt (responseMean q b)
      (coefficient 1 0 (directional Complex.I (responsePlanar q b)) y) y := by
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds y.2] with t ht
    exact (native_mean q b ⟨t,ht⟩).symm
  exact hm.deriv.symm

private theorem reader_derivative_mean (r : XiZeroCopy) (y : Ioi (0:ℝ)) :
    coefficient 1 0 (directional Complex.I (physicalTest r)) y=
      reflectedCompletedLambda ((r.1:ℂ)-1)*(1-(r.1:ℂ)/2)*(y.val:ℂ)^(-(r.1:ℂ)/2) := by
  have h := coefficient_hasDerivAt 1 (by norm_num) 0
    ((physicalTest_smooth r).of_le (WithTop.coe_le_coe.mpr le_top)) y.2
  have hm : HasDerivAt (fun t : ℝ => reflectedCompletedLambda ((r.1:ℂ)-1)*(t:ℂ)^(1-(r.1:ℂ)/2))
      (coefficient 1 0 (directional Complex.I (physicalTest r)) y) y := by
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds y.2] with t ht
    exact (reader_mean r ⟨t,ht⟩).symm
  have hp := (GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := 1-(r.1:ℂ)/2) y.2).const_mul
    (reflectedCompletedLambda ((r.1:ℂ)-1))
  have he : 1-(r.1:ℂ)/2-1=-(r.1:ℂ)/2 := by ring
  rw [he] at hp
  simpa only [mul_assoc] using hm.unique hp

/-- Full cell flux of the native response and the independent original physical reader.
Both ordered products and their mean contributions are included. -/
def nativeGreenFlux (q r : XiZeroCopy) (b : Bool) (y : ℝ) : ℂ :=
  coefficient 1 0 (fun z =>
    (physicalAngularParameter r^2-1/4)*physicalTest r z*directional Complex.I (responsePlanar q b) z-
      parameter q b*responsePlanar q b z*directional Complex.I (physicalTest r) z) y

/-- The complete native flux is its actual nonconstant flux plus the two exact
source-selected mean products. No subtraction defines this flux. -/
theorem nativeGreenFlux_decomposition (q r : XiZeroCopy) (b : Bool) (y : Ioi (0:ℝ)) :
    nativeGreenFlux q r b y=
      (physicalAngularParameter r^2-1/4)*readerCurrent q r b y-
        parameter q b*readerReverseCurrent q r b y+
      (physicalAngularParameter r^2-1/4)*reflectedCompletedLambda ((r.1:ℂ)-1)*
        ((y.val:ℂ)^(1-(r.1:ℂ)/2)*deriv (responseMean q b) y)-
      parameter q b*(reflectedCompletedLambda ((r.1:ℂ)-1)*(1-(r.1:ℂ)/2))*
        ((y.val:ℂ)^(-(r.1:ℂ)/2)*responseMean q b y) := by
  have hf := (responsePlanar_smooth q b).continuousOn
  have hr := (physicalTest_smooth r).continuousOn
  have hv := (directional_smooth (responsePlanar_smooth q b) Complex.I).continuousOn
  have hrv := (directional_smooth (physicalTest_smooth r) Complex.I).continuousOn
  have he : (fun z => (physicalAngularParameter r^2-1/4)*physicalTest r z*
      directional Complex.I (responsePlanar q b) z-
      parameter q b*responsePlanar q b z*directional Complex.I (physicalTest r) z)=
    (fun z => (physicalAngularParameter r^2-1/4)*
      (directional Complex.I (responsePlanar q b) z*physicalTest r z)+
      (-parameter q b)*(responsePlanar q b z*directional Complex.I (physicalTest r) z)) := by
    funext z; ring
  rw [nativeGreenFlux,he,coefficient_zero_linear
    (F := fun z => directional Complex.I (responsePlanar q b) z*physicalTest r z)
    (G := fun z => responsePlanar q b z*directional Complex.I (physicalTest r) z)
    (hv.mul hr) (hf.mul hrv) _ _ y.2]
  simp only [readerCurrent,readerReverseCurrent,covariance,
    native_mean q b y,native_derivative_mean q b y,reader_mean r y,reader_derivative_mean r y]
  ring

/-- Every native term in the original coefficient-weighted Green flux vanishes
at the upper cusp. Original energy, complete forcing and actual reader suffice. -/
theorem nativeGreenFlux_tendsto_zero (q r : XiZeroCopy) (b : Bool) :
    Tendsto (nativeGreenFlux q r b) atTop (𝓝 0) := by
  have h := ((nativeGreenCovariance_tendsto_zero q r b).add
    ((nativeMean_derivative_reader_weight_tendsto_zero q r b).const_mul
      ((physicalAngularParameter r^2-1/4)*reflectedCompletedLambda ((r.1:ℂ)-1)))).sub
    ((nativeMean_reader_weight_tendsto_zero q r b).const_mul
      (parameter q b*(reflectedCompletedLambda ((r.1:ℂ)-1)*(1-(r.1:ℂ)/2))))
  apply (show Tendsto _ atTop (𝓝 (0:ℂ)) by simpa only [mul_zero,add_zero,sub_zero] using h).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  exact (nativeGreenFlux_decomposition q r b ⟨y,hy⟩).symm

open GaloisForLFunctions.HTGeometry.ScalarTwoJet

private theorem field_coordinates (q : XiZeroCopy) (b : Bool) (z : UpperHalfPlane) :
    fullAngularField q b (coordinates z)=fullAngular q b z := by
  change fullAngular q b (ofComplex (angularCoordinates.symm (angularCoordinates (z:ℂ))))=_
  rw [angularCoordinates.symm_apply_apply,ofComplex_apply]

private theorem full_cusp_value (q : XiZeroCopy) (b : Bool) {x y : ℝ}
    (hx : x ∈ Ioc (-1/2:ℝ) (1/2)) (hy : 3 < y) :
    fullAngularField q b ![x,y]=cuspResponse q b ![0,y]+responsePlanar q b (point x y) := by
  let z : UpperHalfPlane := ⟨point x y,by simp [point]; linarith⟩
  have hcoord : coordinates z=![x,y] := by
    ext j
    fin_cases j <;> simp [coordinates,z,point]
  have hfd : z ∈ ModularGroup.fd := by
    constructor
    · change 1 ≤ Complex.normSq (point x y)
      simp only [Complex.normSq_apply,point,Complex.add_re,Complex.add_im,Complex.ofReal_re,
        Complex.ofReal_im,Complex.mul_I_re,Complex.mul_I_im,neg_zero,add_zero,zero_add]
      nlinarith [sq_nonneg x]
    · change |(point x y).re| ≤ 1/2
      simpa [point] using abs_le.mpr ⟨by simpa only [neg_div] using hx.1.le,hx.2⟩
  rw [← hcoord,field_coordinates,fullAngular,globalCuspCutoff_eq_on_fd q b z hfd,hcoord]
  have hc : cutoff ![x,y]=1 := by
    change ((Real.smoothTransition (y-2):ℝ):ℂ)=1
    rw [Real.smoothTransition.one_of_one_le (by linarith)]
    rfl
  rw [cutoffResponse,hc,one_mul]
  have he : cuspResponse q b ![x,y]=cuspResponse q b ![0,y] := rfl
  rw [he]
  congr 1
  change globalResponse q b z=globalResponse q b (ofComplex (z:ℂ))
  rw [ofComplex_apply]

private theorem vertical_hasDerivAt {F : (Fin 2 → ℝ) → ℂ} {x y : ℝ}
    (hf : DifferentiableAt ℝ F ![x,y]) :
    HasDerivAt (fun t : ℝ => F ![x,t]) (coordDeriv 1 F ![x,y]) y := by
  let z : Fin 2 → ℝ := ![x,y]
  have hu (t : ℝ) : Function.update z 1 t=![x,t] := by
    ext i
    fin_cases i <;> simp [z,Function.update]
  have hh : HasFDerivAt F (fderiv ℝ F z) (Function.update z 1 y) := by
    rw [hu]
    exact hf.hasFDerivAt
  have h := hh.comp_hasDerivAt y (hasDerivAt_update z 1 y)
  simpa only [Function.comp_def,hu,z,coordDeriv] using h

private theorem full_cusp_vertical (q : XiZeroCopy) (b : Bool) {x y : ℝ}
    (hx : x ∈ Ioc (-1/2:ℝ) (1/2)) (hy : 3 < y) :
    coordDeriv 1 (fullAngularField q b) ![x,y]=
      deriv (fun t : ℝ => cuspResponse q b ![0,t]) y+
        directional Complex.I (responsePlanar q b) (point x y) := by
  have hy0 : 0 < y := by linarith
  have hH := vertical_hasDerivAt ((fullAngularField_smooth q b ![x,y] hy0).differentiableAt
    (by simp))
  have hN := GaloisForLFunctions.RHTower.SelbergMaassMean.slice_vertical
    ((responsePlanar_smooth q b).of_le (WithTop.coe_le_coe.mpr le_top)) x hy0
  have hp : HasDerivAt (fun t : ℝ => cuspResponse q b ![0,t])
      (coordDeriv 1 (fullAngularField q b) ![x,y]-directional Complex.I (responsePlanar q b) (point x y)) y := by
    apply (hH.sub hN).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hy] with t ht
    simp only [Pi.sub_apply]
    rw [full_cusp_value q b hx ht]
    ring
  linear_combination -hp.deriv

private theorem reader_vertical (r : XiZeroCopy) (x y : ℝ) :
    coordDeriv 1 (scalar (physicalAngularParameter r)) ![x,y]=
      directional Complex.I (physicalTest r) (point x y) := by
  change coordDeriv 1 (scalar (physicalAngularParameter r)) ![x,y]=
    fderiv ℝ ((scalar (physicalAngularParameter r)) ∘ angularCoordinates) (point x y) Complex.I
  have h := angularCoordinates_derivative (scalar (physicalAngularParameter r)) 1 (point x y)
  simpa only [direction,Matrix.cons_val_one,Matrix.cons_val_zero,
    show angularCoordinates (point x y)=![x,y] by simp [angularCoordinates,point]] using h.symm

private theorem vertical_periodic {F : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im})
    (hp : ∀ y : ℝ, 0 < y → ∀ x : ℝ, F (point (x+1) y)=F (point x y))
    (y : Ioi (0:ℝ)) (x : ℝ) :
    directional Complex.I F (point (x+1) y)=directional Complex.I F (point x y) := by
  have hf1 := hf.of_le (show (1 : WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)
  have h := GaloisForLFunctions.RHTower.SelbergMaassMean.slice_vertical hf1 (x+1) y.2
  have hh : HasDerivAt (fun t => F (point x t)) (directional Complex.I F (point (x+1) y)) y := by
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds y.2] with t ht
    exact (hp t ht x).symm
  exact hh.unique (GaloisForLFunctions.RHTower.SelbergMaassMean.slice_vertical hf1 x y.2)

/-- The complete original angular Green current, integrated over the actual cusp cell. -/
def sourceGreenFlux (q r : XiZeroCopy) (b : Bool) (y : ℝ) : ℂ :=
  ∫ x in Ioc (-1/2:ℝ) (1/2), D4BMMixedQuadraticCurrent.angularGreenCurrent q b r 1 ![x,y]

/-- The actual particular response and full squared source retained at the cusp.
No nonconstant source or reader tail is removed. -/
def particularGreenFlux (q r : XiZeroCopy) (b : Bool) (y : ℝ) : ℂ :=
  ∫ x in Ioc (-1/2:ℝ) (1/2),
    (physicalAngularParameter r^2-1/4)*physicalTest r (point x y)*
      deriv (fun t : ℝ => cuspResponse q b ![0,t]) y-
    parameter q b*(cuspResponse q b ![0,y]+scalar (center q) ![x,y] ^2/2)*
      directional Complex.I (physicalTest r) (point x y)

/-- Exact splitting of the actual mixed-current cusp face into its forced
particular/square contribution and complete native response contribution. -/
theorem sourceGreenFlux_decomposition (q r : XiZeroCopy) (b : Bool) (y : Ioi (3:ℝ)) :
    sourceGreenFlux q r b y=particularGreenFlux q r b y+nativeGreenFlux q r b y := by
  have hy0 : 0 < y.val := lt_trans (by norm_num : (0:ℝ)<3) y.2
  let z : Ioi (0:ℝ) := ⟨y.val,hy0⟩
  let K : ℂ → ℂ := fun w =>
    (physicalAngularParameter r^2-1/4)*physicalTest r w*directional Complex.I (responsePlanar q b) w-
      parameter q b*responsePlanar q b w*directional Complex.I (physicalTest r) w
  have hNper := responsePlanar_periodic q b hy0
  change ∀ x : ℝ, responsePlanar q b (point (x+1) y)=responsePlanar q b (point x y) at hNper
  have hRper := physicalTest_periodic r y
  have hNvper := vertical_periodic (responsePlanar_smooth q b)
    (fun _ ht => responsePlanar_periodic q b ht) z
  have hRvper := vertical_periodic (physicalTest_smooth r) (fun t _ => physicalTest_periodic r t) z
  have hK : nativeGreenFlux q r b y=∫ x in Ioc (-1/2:ℝ) (1/2), K (point x y) := by
    apply coefficient_zero_cusp_mean K y
    intro x
    dsimp only [K]
    rw [hNper,hRper,hNvper,hRvper]
  have cR := GaloisForLFunctions.RHTower.SelbergMaassMean.slice_continuous
    (physicalTest_smooth r).continuousOn hy0
  have cN := GaloisForLFunctions.RHTower.SelbergMaassMean.slice_continuous
    (responsePlanar_smooth q b).continuousOn hy0
  have cRv := GaloisForLFunctions.RHTower.SelbergMaassMean.slice_continuous
    (directional_smooth (physicalTest_smooth r) Complex.I).continuousOn hy0
  have cNv := GaloisForLFunctions.RHTower.SelbergMaassMean.slice_continuous
    (directional_smooth (responsePlanar_smooth q b) Complex.I).continuousOn hy0
  have cS : Continuous (fun x : ℝ => scalar (center q) ![x,y.val]) := by
    have he : (fun x : ℝ => scalar (center q) ![x,y.val])=
      fun x => principal (center q) ![0,y.val]+2*D4BMCuspProjection.series
        (D4BMCuspProjection.amplitude (center q) y) x := by
      funext x
      rw [← D4BMCuspProjection.tail_eq_series (center q) hy0 x]
      rfl
    rw [he]
    exact continuous_const.add (continuous_const.mul (D4BMCuspProjection.series_continuous _
      (D4BMCuspProjection.amplitude_norm_summable (center q) hy0)))
  let P : ℝ → ℂ := fun x =>
    (physicalAngularParameter r^2-1/4)*physicalTest r (point x y)*
      deriv (fun t : ℝ => cuspResponse q b ![0,t]) y-
    parameter q b*(cuspResponse q b ![0,y.val]+scalar (center q) ![x,y.val] ^2/2)*
      directional Complex.I (physicalTest r) (point x y)
  have cP : Continuous P := ((cR.const_mul _).mul_const _).sub
    (((continuous_const.add ((cS.pow 2).div_const 2)).const_mul _).mul cRv)
  have cK : Continuous (fun x : ℝ => K (point x y)) :=
    ((cR.const_mul _).mul cNv).sub ((cN.const_mul _).mul cRv)
  rw [hK]
  change (∫ x in Ioc (-1/2:ℝ) (1/2), D4BMMixedQuadraticCurrent.angularGreenCurrent q b r 1 ![x,y.val])=
    (∫ x in Ioc (-1/2:ℝ) (1/2), P x)+∫ x in Ioc (-1/2:ℝ) (1/2), K (point x y)
  rw [← integral_add cP.integrableOn_Ioc cK.integrableOn_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hH := full_cusp_value q b hx y.2
  have hHy := full_cusp_vertical q b hx y.2
  have hRy := reader_vertical r x y
  have hR : physicalTest r (point x y)=scalar (physicalAngularParameter r) ![x,y.val] := by
    simp [physicalTest,angularCoordinates,point]
  change (physicalAngularParameter r^2-1/4)*scalar (physicalAngularParameter r) ![x,y.val]*
    coordDeriv 1 (fullAngularField q b) ![x,y.val]-
    parameter q b*(fullAngularField q b ![x,y.val]+scalar (center q) ![x,y.val] ^2/2)*
      coordDeriv 1 (scalar (physicalAngularParameter r)) ![x,y.val]=_
  rw [hH,hHy,hRy]
  dsimp only [P,K]
  rw [hR]
  ring

/-- Only the explicit forced particular/square cusp contribution survives the
original mixed-current upper face. This is not its vanishing or extinction. -/
theorem sourceGreenFlux_sub_particular_tendsto_zero (q r : XiZeroCopy) (b : Bool) :
    Tendsto (fun y : ℝ => sourceGreenFlux q r b y-particularGreenFlux q r b y) atTop (𝓝 0) := by
  apply (nativeGreenFlux_tendsto_zero q r b).congr'
  filter_upwards [eventually_gt_atTop (3:ℝ)] with y hy
  rw [sourceGreenFlux_decomposition q r b ⟨y,hy⟩]
  ring

end
end RHTower.D4BMMixedNativeReaderFlux
