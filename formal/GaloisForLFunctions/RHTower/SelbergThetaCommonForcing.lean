import GaloisForLFunctions.RHTower.SelbergThetaNativeSource
import GaloisForLFunctions.RHTower.SelbergScatteringEntireXiPackets
/-!
Reflected causal theta modes give one literal second-order forcing at every Xi copy.
The full modular source is admitted to native L², is nonzero, and has an exact mean.
Its height equation keeps the unchanged entire Xi target. The positive theta profile
dominates both its value and first Euler derivative, supplying graph cutoff bounds.
The closed native operator equation and normalized occurrence are not asserted here.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate ContDiff
open GaloisForLFunctions.HTGeometry
set_option autoImplicit false
namespace RHTower.SelbergThetaCommonForcing
open SelbergThetaSourcePhase SelbergThetaSourceVariance SelbergThetaNativeSource
open D4BMGlobalAngularResponse
noncomputable section

private theorem parameter_ne_zero (q : XiZeroCopy) : xiSpectralPoint q ≠ 0 := by
  intro h
  have hz := mode_orientation q 0
  rw [h,Complex.zero_re,zero_mul] at hz
  exact (lt_irrefl 0) hz

/-- The reflected pair of actual causal theta modes, with its original spectral normalization. -/
def profile (q : XiZeroCopy) (x : ℝ) : ℂ :=
  -(mode q x-mode (xiZeroCopyReflectEquiv q) x)/(2*xiSpectralPoint q)

/-- Exact first derivative: the opposite spectral parameters cancel the source terms. -/
theorem profile_hasDerivAt (q : XiZeroCopy) (x : ℝ) :
    HasDerivAt (profile q)
      ((I/2)*(mode q x+mode (xiZeroCopyReflectEquiv q) x)) x := by
  have h := ((hasDerivAt_mode q x).sub (hasDerivAt_mode (xiZeroCopyReflectEquiv q) x)).neg.div_const
    (2*xiSpectralPoint q)
  apply h.congr_deriv
  rw [xiSpectralPoint_reflect]
  field_simp [parameter_ne_zero q]
  ring

/-- The reflected pair solves one second-order equation with the same complete theta forcing. -/
theorem profile_second_hasDerivAt (q : XiZeroCopy) (x : ℝ) :
    HasDerivAt (deriv (profile q))
      ((thetaCuspFullSource x:ℂ)-(xiSpectralPoint q)^2*profile q x) x := by
  have hd : deriv (profile q) = fun x => (I/2)*(mode q x+mode (xiZeroCopyReflectEquiv q) x) :=
    funext (fun x => (profile_hasDerivAt q x).deriv)
  rw [hd]
  have h := ((hasDerivAt_mode q x).add (hasDerivAt_mode (xiZeroCopyReflectEquiv q) x)).const_mul (I/2)
  apply h.congr_deriv
  rw [xiSpectralPoint_reflect]
  unfold profile
  field_simp [parameter_ne_zero q]
  ring_nf
  simp [Complex.I_sq,sub_eq_add_neg]

/-- Pointwise nonvanishing follows from the opposite strict orientations of the two actual modes. -/
theorem profile_ne_zero (q : XiZeroCopy) (x : ℝ) : profile q x ≠ 0 := by
  intro he
  have hdiff : mode q x-mode (xiZeroCopyReflectEquiv q) x = 0 := by
    have h := (div_eq_zero_iff).1 he
    rcases h with h | h
    · exact neg_eq_zero.mp h
    · exact False.elim ((mul_ne_zero (by norm_num) (parameter_ne_zero q)) h)
  have hq := mode_orientation q x
  have hr := mode_orientation (xiZeroCopyReflectEquiv q) x
  rw [xiSpectralPoint_reflect,Complex.neg_re] at hr
  have heq := congrArg Complex.re (sub_eq_zero.mp hdiff)
  rw [heq] at hq
  nlinarith

/-- Original half-density profile of the reflected source pair. -/
def heightProfile (q : XiZeroCopy) (y : ℝ) : ℂ :=
  (Real.exp (Real.log y/2):ℂ)*profile q (Real.log y/2)

/-- The full native field, retaining both complete original periodizations. -/
def source (q : XiZeroCopy) (z : UpperHalfPlane) : ℂ :=
  -(modeSource q z-modeSource (xiZeroCopyReflectEquiv q) z)/(2*xiSpectralPoint q)

/-- Native L2 admission of the literal reflected pair. -/
theorem source_memLp (q : XiZeroCopy) : MemLp (source q) 2 angularMeasure := by
  change MemLp (fun z => -(modeSource q z-modeSource (xiZeroCopyReflectEquiv q) z)/
    (2*xiSpectralPoint q)) 2 angularMeasure
  simpa only [div_eq_mul_inv, Pi.neg_apply, Pi.sub_apply] using
    (((modeSource_memLp q).sub (modeSource_memLp (xiZeroCopyReflectEquiv q))).neg).mul_const
      ((2*xiSpectralPoint q)⁻¹)

/-- Modular invariance of the complete reflected source. -/
theorem source_invariant (q : XiZeroCopy) (g : PSL2Z) (z : UpperHalfPlane) :
    source q (g • z) = source q z := by
  simp only [source,modeSource_invariant]


private theorem frequency_ne_zero (q : XiZeroCopy) : (xiSpectralPoint q).re ≠ 0 := by
  simpa [xiSpectralPoint,Complex.mul_re,Complex.mul_im] using xi_divisor_support_im_ne_zero q.1

private theorem source_orientation (q : XiZeroCopy) (z : UpperHalfPlane) :
    (xiSpectralPoint q).re*(modeSource q z).re < 0 := by
  have h := (Complex.re_le_norm ((positiveSource z:ℂ)+((xiSpectralPoint q).re:ℂ)*modeSource q z)).trans_lt
    (modeSource_strict_disk q z)
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero] at h
  linarith

/-- Full modular periodization preserves a nonzero reflected source at every point. -/
theorem source_ne_zero (q : XiZeroCopy) (z : UpperHalfPlane) : source q z ≠ 0 := by
  intro hz
  have hd : modeSource q z = modeSource (xiZeroCopyReflectEquiv q) z := by
    unfold source at hz
    have hneg := ((div_eq_zero_iff).mp hz).resolve_right
      (mul_ne_zero (by norm_num) (parameter_ne_zero q))
    exact sub_eq_zero.mp (neg_eq_zero.mp hneg)
  have hq := source_orientation q z
  have hr := source_orientation (xiZeroCopyReflectEquiv q) z
  rw [xiSpectralPoint_reflect,Complex.neg_re] at hr
  rw [hd] at hq
  nlinarith

private theorem shift_ne_zero (q : XiZeroCopy) (a : ℝ) :
    xiSpectralPoint q+(a:ℂ)*I ≠ 0 := by
  intro h
  apply frequency_ne_zero q
  have hr := congrArg Complex.re h
  simpa [Complex.mul_re] using hr

/-- The original mean denominator never vanishes at an actual Xi copy. -/
theorem mean_denominator_ne_zero (q : XiZeroCopy) : 1+(xiSpectralPoint q)^2 ≠ 0 := by
  have hm : xiSpectralPoint q-I ≠ 0 := by simpa [sub_eq_add_neg] using shift_ne_zero q (-1)
  have hp : xiSpectralPoint q+I ≠ 0 := by simpa using shift_ne_zero q 1
  have he : (xiSpectralPoint q-I)*(xiSpectralPoint q+I) = 1+(xiSpectralPoint q)^2 := by
    ring_nf
    simp [Complex.I_sq,add_comm]
  exact he ▸ mul_ne_zero hm hp

/-- Exact mean of the common-forcing source in the original native measure. -/
theorem source_integral (q : XiZeroCopy) :
    (∫ z, source q z ∂angularMeasure) = (sourceMass:ℂ)/(1+(xiSpectralPoint q)^2) := by
  have hi : Integrable (modeSource q) angularMeasure := MemLp.integrable (by norm_num) (modeSource_memLp q)
  have hj : Integrable (modeSource (xiZeroCopyReflectEquiv q)) angularMeasure :=
    MemLp.integrable (by norm_num) (modeSource_memLp (xiZeroCopyReflectEquiv q))
  simp only [source,div_eq_mul_inv]
  rw [integral_mul_const,integral_neg,integral_sub hi hj,modeSource_integral,modeSource_integral,
    xiSpectralPoint_reflect]
  have hm : xiSpectralPoint q-I ≠ 0 := by simpa [sub_eq_add_neg] using shift_ne_zero q (-1)
  have hp : -xiSpectralPoint q-I ≠ 0 := by
    simpa [neg_add_rev,sub_eq_add_neg,add_comm] using (neg_ne_zero.mpr (shift_ne_zero q 1))
  field_simp [hm,hp,parameter_ne_zero q,mean_denominator_ne_zero q]
  ring_nf
  simp [Complex.I_sq]


/-- First positive-height derivative of the original reflected-pair half-density. -/
def heightDerivative (q : XiZeroCopy) (y : ℝ) : ℂ :=
  (Real.exp (-Real.log y/2)/2:ℂ)*
    (profile q (Real.log y/2)+deriv (profile q) (Real.log y/2))

/-- Exact first derivative in the original height coordinate. -/
theorem height_hasDerivAt (q : XiZeroCopy) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (heightProfile q) (heightDerivative q y) y := by
  have ht := (Real.hasDerivAt_log hy.ne').div_const 2
  have hp := (profile_hasDerivAt q (Real.log y/2)).scomp y ht
  have he := ht.exp.ofReal_comp
  have h := he.mul hp
  apply h.congr_deriv
  rw [← (profile_hasDerivAt q (Real.log y/2)).deriv]
  unfold heightDerivative
  have hf : (Real.exp (Real.log y/2):ℂ)*(((y⁻¹)/2:ℝ):ℂ) =
      (Real.exp (-Real.log y/2)/2:ℂ) := by
    have hr : Real.exp (Real.log y/2)*(y⁻¹/2) = Real.exp (-Real.log y/2)/2 := by
      have hi : y⁻¹ = Real.exp (-Real.log y) := by rw [Real.exp_neg,Real.exp_log hy]
      rw [hi]
      have he : Real.exp (Real.log y/2)*Real.exp (-Real.log y) = Real.exp (-Real.log y/2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (Real.exp (Real.log y/2)*Real.exp (-Real.log y))/2 := by ring
        _ = _ := by rw [he]
    exact_mod_cast hr
  simp only [Complex.ofReal_mul,Complex.real_smul,Function.comp_apply] at h ⊢
  calc
    _ = ((Real.exp (Real.log y/2):ℂ)*(((y⁻¹)/2:ℝ):ℂ))*
        (profile q (Real.log y/2)+deriv (profile q) (Real.log y/2)) := by ring
    _ = _ := by rw [hf]

/-- Exact second height derivative, retaining the universal theta forcing. -/
theorem heightDerivative_hasDerivAt (q : XiZeroCopy) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (heightDerivative q)
      ((Real.exp (-(3/2:ℝ)*Real.log y)/4:ℂ)*
        ((thetaCuspFullSource (Real.log y/2):ℂ)-(1+(xiSpectralPoint q)^2)*
          profile q (Real.log y/2))) y := by
  have ht := (Real.hasDerivAt_log hy.ne').div_const 2
  have hp := (profile_hasDerivAt q (Real.log y/2)).scomp y ht
  have hp2 := (profile_second_hasDerivAt q (Real.log y/2)).scomp y ht
  have he := (ht.neg.exp.div_const 2).ofReal_comp
  have h := he.mul (hp.add hp2)
  simp only [Pi.mul_def,Pi.add_def,Pi.neg_def,Function.comp_def,
    Complex.ofReal_div,Complex.ofReal_ofNat] at h
  have hfun : (fun t : ℝ => (Real.exp (-(Real.log t/2)):ℂ)/2*
      (profile q (Real.log t/2)+deriv (profile q) (Real.log t/2))) = heightDerivative q := by
    funext t
    simp only [heightDerivative,neg_div]
  rw [hfun] at h
  apply h.congr_deriv
  rw [← (profile_hasDerivAt q (Real.log y/2)).deriv]
  simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_neg,Complex.real_smul]
  have hf : (Real.exp (-(Real.log y/2)):ℂ)*(y⁻¹:ℝ) =
      (Real.exp (-(3/2:ℝ)*Real.log y):ℂ) := by
    have hi : (y⁻¹:ℝ) = Real.exp (-Real.log y) := by rw [Real.exp_neg,Real.exp_log hy]
    rw [hi,← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  calc
    _ = ((Real.exp (-(Real.log y/2)):ℂ)*(y⁻¹:ℝ))/4*
        ((thetaCuspFullSource (Real.log y/2):ℂ)-(1+(xiSpectralPoint q)^2)*
          profile q (Real.log y/2)) := by push_cast; ring
    _ = _ := by rw [hf]


/-- Exact second derivative of the half-density on the positive-height chart. -/
theorem height_second_deriv (q : XiZeroCopy) (y : ℝ) (hy : 0 < y) :
    deriv (deriv (heightProfile q)) y =
      (Real.exp (-(3/2:ℝ)*Real.log y)/4:ℂ)*
        ((thetaCuspFullSource (Real.log y/2):ℂ)-(1+(xiSpectralPoint q)^2)*
          profile q (Real.log y/2)) := by
  have he : deriv (heightProfile q) =ᶠ[𝓝 y] heightDerivative q := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
    exact (height_hasDerivAt q t ht).deriv
  rw [he.deriv_eq]
  exact (heightDerivative_hasDerivAt q y hy).deriv

/-- The unchanged quarter-shifted native energy attached to the actual Xi copy. -/
def energy (q : XiZeroCopy) : ℂ := (5+(xiSpectralPoint q)^2)/4

/-- Exact original radial operator residual: every Xi copy has the same complete theta forcing. -/
theorem height_residual (q : XiZeroCopy) (y : ℝ) (hy : 0 < y) :
    heightProfile q y-(y:ℂ)^2*deriv (deriv (heightProfile q)) y-
      energy q*heightProfile q y = -(positiveProfile y:ℂ)/4 := by
  rw [height_second_deriv q y hy]
  have hf : (y:ℂ)^2*(Real.exp (-(3/2:ℝ)*Real.log y)/4:ℂ) =
      (Real.exp (Real.log y/2)/4:ℂ) := by
    have hr : y^2*Real.exp (-(3/2:ℝ)*Real.log y) = Real.exp (Real.log y/2) := by
      have hy2 : y^2 = Real.exp (Real.log y+Real.log y) := by rw [Real.exp_add,Real.exp_log hy,pow_two]
      calc
        _ = Real.exp (Real.log y+Real.log y)*Real.exp (-(3/2:ℝ)*Real.log y) := by rw [hy2]
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hc := congrArg (fun t : ℝ => (t:ℂ)) hr
    simp only [Complex.ofReal_mul,Complex.ofReal_pow] at hc
    linear_combination hc/4
  rw [← mul_assoc, hf]
  unfold heightProfile energy positiveProfile
  push_cast
  ring


/-- This forced source retains the original full Xi target, including the zero's real part. -/
theorem energy_full_target (q : XiZeroCopy) :
    SelbergScatteringEntireTransform.casimirTransform (energy q-1) =
      SelbergScatteringEntireXiPackets.xiEntireTarget q := by
  have he : energy q-1 = ((q.1:ℂ)/2+1/4)*(1-((q.1:ℂ)/2+1/4)) := by
    unfold energy xiSpectralPoint
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [he]
  exact SelbergScatteringEntireXiPackets.casimirTransform_quarter_exponent_shift _


private theorem mode_contDiff (q : XiZeroCopy) : ContDiff ℝ ∞ (mode q) := by
  have hd : deriv (mode q) = fun x => -I*xiSpectralPoint q*mode q x-I*(thetaCuspFullSource x:ℂ) :=
    funext (fun x => (hasDerivAt_mode q x).deriv)
  rw [contDiff_infty]
  intro n
  induction n with
  | zero =>
    rw [Nat.cast_zero,contDiff_zero]
    exact continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_mode q x).continuousAt)
  | succ n hn =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_mode q x).differentiableAt,by simp,?_⟩
    rw [hd]
    have hp : ContDiff ℝ (n:ℕ∞ω) (fun x => (thetaCuspFullSource x:ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_thetaCuspFullSource.of_le (by exact_mod_cast le_top))
    fun_prop

/-- Smoothness of the literal two-ended, reflected theta profile. -/
theorem profile_contDiff (q : XiZeroCopy) : ContDiff ℝ ∞ (profile q) := by
  have hu := mode_contDiff q
  have hv := mode_contDiff (xiZeroCopyReflectEquiv q)
  unfold profile
  fun_prop

/-- Smoothness in the original positive-height chart. -/
theorem height_contDiffAt (q : XiZeroCopy) (y : ℝ) (hy : 0 < y) :
    ContDiffAt ℝ ∞ (heightProfile q) y := by
  have hp := profile_contDiff q
  have hl : ContDiffAt ℝ ∞ Real.log y := Real.contDiffAt_log.mpr hy.ne'
  have ht : ContDiffAt ℝ ∞ (fun t : ℝ => Real.log t/2) y := hl.div_const 2
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp y (Real.contDiff_exp.contDiffAt.comp y ht)).mul
    (hp.contDiffAt.comp y ht)

private theorem modeProfile_eq (q : XiZeroCopy) (y : ℝ) :
    modeProfile q y = (Real.exp (Real.log y/2):ℂ)*mode q (Real.log y/2) := by
  unfold modeProfile positiveProfile sourceRatio
  push_cast
  field_simp [(thetaCuspFullSource_pos_all (Real.log y/2)).ne']

/-- The reflected height source is the exact combination of both original mode seeds. -/
theorem heightProfile_eq_pair (q : XiZeroCopy) (y : ℝ) :
    heightProfile q y = -(modeProfile q y-modeProfile (xiZeroCopyReflectEquiv q) y)/(2*xiSpectralPoint q) := by
  rw [modeProfile_eq,modeProfile_eq]
  unfold heightProfile profile
  ring

private theorem modeProfile_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, ‖modeProfile q y‖ ≤ C*positiveProfile y := by
  obtain ⟨C,hC,hb⟩ := sourceRatio_bounded q
  refine ⟨C,hC,fun y => ?_⟩
  have hp : 0 < positiveProfile y := by
    unfold positiveProfile
    exact mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all _)
  rw [modeProfile,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  nlinarith [hb (Real.log y/2)]

/-- A fixed original positive theta profile dominates the whole reflected source. -/
theorem heightProfile_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, ‖heightProfile q y‖ ≤ C*positiveProfile y := by
  obtain ⟨C,hC,hb⟩ := modeProfile_bound q
  obtain ⟨D,hD,hd⟩ := modeProfile_bound (xiZeroCopyReflectEquiv q)
  have hz : 0 < ‖2*xiSpectralPoint q‖ := norm_pos_iff.mpr (mul_ne_zero (by norm_num) (parameter_ne_zero q))
  refine ⟨(C+D)/‖2*xiSpectralPoint q‖,by positivity,fun y => ?_⟩
  rw [heightProfile_eq_pair,norm_div,norm_neg]
  calc
    _ ≤ (‖modeProfile q y‖+‖modeProfile (xiZeroCopyReflectEquiv q) y‖)/‖2*xiSpectralPoint q‖ :=
      div_le_div_of_nonneg_right (norm_sub_le _ _) hz.le
    _ ≤ (C*positiveProfile y+D*positiveProfile y)/‖2*xiSpectralPoint q‖ :=
      div_le_div_of_nonneg_right (add_le_add (hb y) (hd y)) hz.le
    _ = _ := by ring

/-- All cusp power bounds are supplied by the original theta profile. -/
theorem heightProfile_power_bound (q : XiZeroCopy) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖heightProfile q y‖ ≤ C*y^r := by
  obtain ⟨C,hC,hb⟩ := heightProfile_bound q
  obtain ⟨D,hD,hd⟩ := positiveProfile_power_bound r
  refine ⟨C*D,by positivity,fun y hy => ?_⟩
  calc
    _ ≤ C*positiveProfile y := hb y
    _ ≤ C*(D*y^r) := mul_le_mul_of_nonneg_left (hd y hy) hC.le
    _ = _ := by ring


/-- The original height Euler derivative is controlled by the two admitted mode seeds. -/
theorem height_euler (q : XiZeroCopy) (y : ℝ) (hy : 0 < y) :
    (y:ℂ)*deriv (heightProfile q) y = heightProfile q y/2+
      (I/4)*(modeProfile q y+modeProfile (xiZeroCopyReflectEquiv q) y) := by
  rw [(height_hasDerivAt q y hy).deriv]
  unfold heightDerivative
  rw [(profile_hasDerivAt q (Real.log y/2)).deriv,modeProfile_eq,modeProfile_eq]
  unfold heightProfile
  have hf : (y:ℂ)*(Real.exp (-Real.log y/2):ℂ) = (Real.exp (Real.log y/2):ℂ) := by
    have hr : y*Real.exp (-Real.log y/2) = Real.exp (Real.log y/2) := by
      calc
        _ = Real.exp (Real.log y)*Real.exp (-Real.log y/2) := by rw [Real.exp_log hy]
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    exact_mod_cast hr
  calc
    _ = ((y:ℂ)*(Real.exp (-Real.log y/2):ℂ))/2*
        (profile q (Real.log y/2)+(I/2)*(mode q (Real.log y/2)+mode (xiZeroCopyReflectEquiv q) (Real.log y/2))) := by ring
    _ = _ := by rw [hf]; ring

/-- One fixed positive theta majorant controls the actual first Euler derivative. -/
theorem height_euler_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y →
      ‖(y:ℂ)*deriv (heightProfile q) y‖ ≤ C*positiveProfile y := by
  obtain ⟨C,hC,hb⟩ := heightProfile_bound q
  obtain ⟨D,hD,hd⟩ := modeProfile_bound q
  obtain ⟨E,hE,he⟩ := modeProfile_bound (xiZeroCopyReflectEquiv q)
  refine ⟨C/2+(D+E)/4,by positivity,fun y hy => ?_⟩
  rw [height_euler q y hy]
  calc
    _ ≤ ‖heightProfile q y‖/2+(‖modeProfile q y‖+‖modeProfile (xiZeroCopyReflectEquiv q) y‖)/4 := by
      have h := norm_add_le (heightProfile q y/2)
        ((I/4)*(modeProfile q y+modeProfile (xiZeroCopyReflectEquiv q) y))
      norm_num [norm_div,norm_mul] at h
      exact h.trans (by nlinarith [norm_add_le (modeProfile q y) (modeProfile (xiZeroCopyReflectEquiv q) y)])
    _ ≤ (C/2+(D+E)/4)*positiveProfile y := by nlinarith [hb y,hd y,he y]

open D4BMModularCore D4BMJointSource

private theorem mode_rows_summable (q : XiZeroCopy) (z : UpperHalfPlane) :
    Summable (fun v : gammaSetHalf => modeProfile q (gammaSetMatrix v.1 • z).im) := by
  obtain ⟨C,_,hb⟩ := SelbergThetaNativeSource.modeProfile_power_bound q 2
  apply Summable.of_norm_bounded ((positiveCuspRows_summable 2 (by norm_num) z).mul_left C)
  intro v
  exact hb _ (gammaSetMatrix v.1 • z).im_pos

/-- Absolute convergence of every primitive row of the reflected pair. -/
theorem height_rows_summable (q : XiZeroCopy) (z : UpperHalfPlane) :
    Summable (fun v : gammaSetHalf => heightProfile q (gammaSetMatrix v.1 • z).im) := by
  obtain ⟨C,_,hb⟩ := heightProfile_power_bound q 2
  apply Summable.of_norm_bounded ((positiveCuspRows_summable 2 (by norm_num) z).mul_left C)
  intro v
  exact hb _ (gammaSetMatrix v.1 • z).im_pos

/-- The native source is the complete primitive-row sum of its literal height seed. -/
theorem source_eq_rows (q : XiZeroCopy) (z : UpperHalfPlane) :
    source q z = ∑' v : gammaSetHalf, heightProfile q (gammaSetMatrix v.1 • z).im := by
  have hq := mode_rows_summable q z
  have hr := mode_rows_summable (xiZeroCopyReflectEquiv q) z
  unfold source modeSource
  rw [periodize_cuspHeightSeed_eq_rows_of_rows_summable _ _ hq,
    periodize_cuspHeightSeed_eq_rows_of_rows_summable _ _ hr]
  simp_rw [heightProfile_eq_pair,div_eq_mul_inv]
  rw [tsum_mul_right,tsum_neg,hq.tsum_sub hr]

/-- Exact full modular periodization, including all translated and nonparabolic rows. -/
theorem source_eq_periodize (q : XiZeroCopy) (z : UpperHalfPlane) :
    source q z = periodize (cuspHeightSeed (heightProfile q)) z := by
  rw [source_eq_rows,periodize_cuspHeightSeed_eq_rows_of_rows_summable _ _ (height_rows_summable q z)]

end
end RHTower.SelbergThetaCommonForcing
