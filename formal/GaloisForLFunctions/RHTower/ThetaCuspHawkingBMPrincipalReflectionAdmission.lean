import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCircleGauss
import GaloisForLFunctions.HTGeometry.SmoothAngularAverage

/-! Exact circle mass and reflection cancellation for the original principal causal kernel.
The complete kernel retains both characteristic indicators. -/

open MeasureTheory Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMPrincipalReflection
open D4BMCausalKernel D4BMNativeCircle
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private theorem legendre_neg_one_flux {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun r : ℝ => ((r:ℂ)^2-1)*legendreKernelFirst (-1) r) 0 z := by
  have h := ((((hasDerivAt_id z).ofReal_comp).pow 2).sub_const (1:ℂ)).mul
    (legendreKernel_derivatives (-1) hz).2
  apply h.congr_deriv
  have he := legendreKernel_equation (-1) hz
  norm_num only [neg_add_cancel,mul_zero,zero_mul,sub_zero,pow_one,Pi.pow_apply,id_eq,
    Complex.ofReal_one,Nat.reduceSub] at he ⊢
  linear_combination he

private theorem legendre_neg_one_first {z : ℝ} (hz : 1 ≤ z) :
    legendreKernelFirst (-1) z=0 := by
  by_cases he : z=1
  · subst z
    have h := legendreKernel_equation (-1) (show (0:ℝ)<1 by norm_num)
    norm_num at h
    exact h
  have hcont : ContinuousOn
      (fun r : ℝ => ((r:ℂ)^2-1)*legendreKernelFirst (-1) r) (Icc 1 z) :=
    fun r hr => (legendre_neg_one_flux (by linarith [hr.1])).continuousAt.continuousWithinAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hz hcont
    (fun r hr => legendre_neg_one_flux (by linarith [hr.1]))
    intervalIntegrable_const
  have hf : ((z:ℂ)^2-1)*legendreKernelFirst (-1) z=0 := by simpa using hi.symm
  have hne : (z:ℂ)^2-1 ≠ 0 := by
    have : 1 < z := lt_of_le_of_ne hz (Ne.symm he)
    exact_mod_cast (show z^2-1 ≠ 0 by nlinarith)
  exact (mul_eq_zero.mp hf).resolve_left hne

/-- The original height circle has exactly unit mass, including arbitrarily large radii. -/
theorem average_height (d : ℝ) : average (fun theta => (height d theta:ℂ))=1 := by
  have hz := Real.one_le_cosh d
  have hcont : ContinuousOn (legendreKernel (-1)) (Icc 1 (Real.cosh d)) :=
    fun r hr => (legendreKernel_derivatives (-1) (by linarith [hr.1])).1.continuousAt.continuousWithinAt
  have hd (r : ℝ) (hr : r ∈ Ioo 1 (Real.cosh d)) : HasDerivAt (legendreKernel (-1)) 0 r := by
    have h := (legendreKernel_derivatives (-1) (z := r) (by linarith [hr.1])).1
    rw [legendre_neg_one_first hr.1.le] at h
    exact h
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hz hcont hd
    intervalIntegrable_const
  have he : legendreKernel (-1) (Real.cosh d)=1 := by
    exact sub_eq_zero.mp (by simpa only [intervalIntegral.integral_zero,legendreKernel_one] using hi.symm)
  simpa only [powerCircle,Complex.cpow_one] using (powerCircle_eq_legendre 1 d).trans he

private theorem height_continuous : Continuous (fun p : ℝ × ℝ => height p.1 p.2) := by
  have hc : Continuous (fun p : ℝ × ℝ => denominator p.1 p.2) := by unfold denominator; fun_prop
  exact continuous_const.div₀ hc (fun p => (denominator_pos p.1 p.2).ne')

private theorem height_positive (d theta : ℝ) : 0 < height d theta :=
  one_div_pos.mpr (denominator_pos _ _)

private theorem height_upper (d theta : ℝ) (hd : 0 ≤ d) : height d theta ≤ Real.exp d := by
  have hs : 0 ≤ Real.sinh d := Real.sinh_nonneg_iff.mpr hd
  have hb : Real.exp (-d) ≤ denominator d theta := by
    rw [← Real.cosh_sub_sinh]
    dsimp only [denominator]
    nlinarith [mul_nonneg hs (sub_nonneg.mpr (Real.cos_le_one theta))]
  have h := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 1 by norm_num) (Real.exp_pos (-d)) hb
  simpa only [height,Real.exp_neg,one_div,inv_inv] using h

private theorem heightRadial_bound (d theta : ℝ) : |heightRadial d theta| ≤ height d theta := by
  have hD := denominator_pos d theta
  have he : (denominator d theta)^2-(radialNumerator d theta)^2=1-(Real.cos theta)^2 := by
    dsimp only [denominator,radialNumerator]
    linear_combination (1-(Real.cos theta)^2)*(Real.cosh_sq_sub_sinh_sq d)
  have hcos : (Real.cos theta)^2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq theta,sq_nonneg (Real.sin theta)]
  have hn : |radialNumerator d theta| ≤ denominator d theta := by
    nlinarith [sq_abs (radialNumerator d theta)]
  rw [heightRadial,abs_div,abs_neg,abs_pow,abs_of_pos hD,height]
  apply (div_le_div_iff₀ (pow_pos hD 2) hD).mpr
  nlinarith [mul_le_mul_of_nonneg_right hn hD.le]

private def circlePowerFirst (m : ℂ) (d theta : ℝ) : ℂ :=
  m*(height d theta:ℂ)^(m-1)*(heightRadial d theta:ℂ)

private theorem circlePower_derivative (m : ℂ) (d theta : ℝ) :
    HasDerivAt (fun r => (height r theta:ℂ)^m) (circlePowerFirst m d theta) d := by
  have h := (Complex.hasStrictDerivAt_cpow_const
    (c := m) (Complex.ofReal_mem_slitPlane.mpr (height_positive d theta))).hasDerivAt
  convert! h.scomp d (height_radial_derivatives d theta).1.ofReal_comp using 1
  simp only [circlePowerFirst,smul_eq_mul]
  ring

private theorem circlePower_continuous (m : ℂ) :
    Continuous (fun p : ℝ × ℝ => (height p.1 p.2:ℂ)^m) :=
  (Complex.continuous_ofReal.comp height_continuous).cpow continuous_const
    (fun p => Complex.ofReal_mem_slitPlane.mpr (height_positive p.1 p.2))

private theorem circlePowerFirst_continuous (m : ℂ) :
    Continuous (fun p : ℝ × ℝ => circlePowerFirst m p.1 p.2) := by
  have hh : Continuous (fun p : ℝ × ℝ => (heightRadial p.1 p.2:ℂ)) := by
    have hD : Continuous (fun p : ℝ × ℝ => denominator p.1 p.2) := by unfold denominator; fun_prop
    have hN : Continuous (fun p : ℝ × ℝ => radialNumerator p.1 p.2) := by unfold radialNumerator; fun_prop
    exact Complex.continuous_ofReal.comp
      (hN.neg.div₀ (hD.pow 2) (fun p => pow_ne_zero 2 (denominator_pos p.1 p.2).ne'))
  exact (continuous_const.mul (circlePower_continuous (m-1))).mul hh

private theorem circlePowerFirst_bound (m : ℂ) (d theta : ℝ) :
    ‖circlePowerFirst m d theta‖ ≤ ‖m‖*(height d theta)^m.re := by
  have hp := height_positive d theta
  have he : (height d theta)^(m.re-1)*height d theta=(height d theta)^m.re := by
    calc
      _ = (height d theta)^(m.re-1)*(height d theta)^(1:ℝ) := by rw [Real.rpow_one]
      _ = (height d theta)^(m.re-1+1) := (Real.rpow_add hp _ _).symm
      _ = _ := by rw [sub_add_cancel]
  rw [circlePowerFirst,norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp,
    Complex.sub_re,Complex.one_re,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ (‖m‖*(height d theta)^(m.re-1))*height d theta :=
      mul_le_mul_of_nonneg_left (heightRadial_bound d theta) (by positivity)
    _ = ‖m‖*(height d theta)^m.re := by rw [mul_assoc,he]

private theorem circlePowerFirst_strip_bound (m : ℂ) (hm : 0 ≤ m.re) (hm2 : m.re ≤ 2)
    (d theta : ℝ) (hd : 0 ≤ d) :
    ‖circlePowerFirst m d theta‖ ≤ ‖m‖*(1+Real.exp d*height d theta) := by
  apply (circlePowerFirst_bound m d theta).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg m)
  have hp := height_positive d theta
  by_cases hh : height d theta ≤ 1
  · exact (Real.rpow_le_one hp.le hh hm).trans
      (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos d).le hp.le))
  · have hh' := le_of_lt (lt_of_not_ge hh)
    have h := Real.rpow_le_rpow_of_exponent_le hh' hm2
    rw [Real.rpow_two] at h
    nlinarith [mul_le_mul_of_nonneg_right (height_upper d theta hd) hp.le]

private theorem circlePower_smooth (m : ℂ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => (height p.1 p.2:ℂ)^m) := by
  have hD : ContDiff ℝ ∞ (fun p : ℝ × ℝ => denominator p.1 p.2) := by
    unfold denominator
    fun_prop
  have hH : ContDiff ℝ ∞ (fun p : ℝ × ℝ => height p.1 p.2) :=
    contDiff_const.div hD (fun p => (denominator_pos p.1 p.2).ne')
  have he : (fun p : ℝ × ℝ => (height p.1 p.2:ℂ)^m) =
      fun p => Complex.exp ((Real.log (height p.1 p.2):ℂ)*m) := by
    funext p
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (height_positive p.1 p.2).ne'),
      ← Complex.ofReal_log (height_positive p.1 p.2).le]
  rw [he]
  exact ((Complex.ofRealCLM.contDiff.comp
    (hH.log (fun p => (height_positive p.1 p.2).ne'))).mul contDiff_const).cexp

private theorem powerCircle_derivative (m : ℂ) (d : ℝ) :
    HasDerivAt (powerCircle m) (average (circlePowerFirst m d)) d := by
  have hF := circlePower_smooth m
  have h := GaloisForLFunctions.HTGeometry.SmoothAngularAverage.average_hasDerivAt hF d
  have he : (fun theta => GaloisForLFunctions.HTGeometry.SmoothAngularAverage.radialPartial
      (fun p : ℝ × ℝ => (height p.1 p.2:ℂ)^m) (d,theta)) = circlePowerFirst m d := by
    funext theta
    exact (GaloisForLFunctions.HTGeometry.SmoothAngularAverage.slice_hasDerivAt hF d theta).unique
      (circlePower_derivative m d theta)
  rw [he] at h
  exact h

private theorem height_integral (d : ℝ) :
    (∫ theta in Ioc 0 (2*Real.pi), height d theta)=2*Real.pi := by
  have h := average_height d
  change (1/(2*Real.pi:ℂ))*(∫ theta in Ioc 0 (2*Real.pi), (height d theta:ℂ))=1 at h
  have hI : (∫ theta in Ioc 0 (2*Real.pi), (height d theta:ℂ)) =
      ((∫ theta in Ioc 0 (2*Real.pi), height d theta : ℝ):ℂ) :=
    _root_.integral_complex_ofReal (f := fun theta => height d theta)
  rw [hI] at h
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hp] at h
  exact_mod_cast h

private theorem average_norm_le_height (f : ℝ → ℂ) (A B d : ℝ)
    (h : ∀ theta, ‖f theta‖ ≤ A+B*height d theta) : ‖average f‖ ≤ A+B := by
  let μ := volume.restrict (Ioc 0 (2*Real.pi))
  have hc : Continuous (fun theta => height d theta) :=
    height_continuous.comp (continuous_const.prodMk continuous_id)
  have hi : Integrable (fun theta => A+B*height d theta) μ :=
    (continuous_const.add (continuous_const.mul hc)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hb := norm_integral_le_of_norm_le hi (Eventually.of_forall h)
  have hsize : μ.real Set.univ=2*Real.pi := by
    simp [μ,Measure.real,Real.volume_Ioc,Real.pi_pos.le]
  have he : (∫ theta, A+B*height d theta ∂μ)=(2*Real.pi)*(A+B) := by
    rw [integral_add (integrable_const A)
      ((hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).const_mul B),
      integral_const,integral_const_mul,hsize]
    change (2*Real.pi)*A+B*(∫ theta in Ioc 0 (2*Real.pi), height d theta)=_
    rw [height_integral]
    ring
  rw [he] at hb
  have hp : 0 < 2*Real.pi := by positivity
  calc
    ‖average f‖ = (1/(2*Real.pi))*‖∫ theta, f theta ∂μ‖ := by
      change ‖(1/(2*Real.pi:ℂ))*(∫ theta, f theta ∂μ)‖=_
      rw [norm_mul,norm_div,norm_one,norm_mul,Complex.norm_ofNat,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    _ ≤ (1/(2*Real.pi))*((2*Real.pi)*(A+B)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = A+B := by field_simp

private theorem powerCircle_derivative_bound (m : ℂ) (hm : 0 ≤ m.re) (hm2 : m.re ≤ 2)
    (d : ℝ) (hd : 0 ≤ d) :
    ‖average (circlePowerFirst m d)‖ ≤ ‖m‖*(1+Real.exp d) := by
  have h := average_norm_le_height (circlePowerFirst m d) ‖m‖ (‖m‖*Real.exp d) d
    (fun theta => by
      simpa only [mul_add,mul_one,mul_assoc] using circlePowerFirst_strip_bound m hm hm2 d theta hd)
  simpa only [mul_add,mul_one] using h

private theorem legendre_first_large_radius (m : ℂ) (hm : 0 ≤ m.re) (hm2 : m.re ≤ 2)
    (d : ℝ) (hd : 1 ≤ d) : ‖legendreKernelFirst (-m) (Real.cosh d)‖ ≤ 8*‖m‖ := by
  have hd0 : 0 < d := by linarith
  have hs : 0 < Real.sinh d := Real.sinh_pos_iff.mpr hd0
  have hder : HasDerivAt (powerCircle m)
      ((Real.sinh d:ℂ)*legendreKernelFirst (-m) (Real.cosh d)) d := by
    rw [show powerCircle m = fun r => legendreKernel (-m) (Real.cosh r) from
      funext (powerCircle_eq_legendre m)]
    simpa only [Function.comp_def,Complex.real_smul] using
      (legendreKernel_derivatives (-m) (Real.cosh_pos d)).1.scomp d (Real.hasDerivAt_cosh d)
  have he := (powerCircle_derivative m d).unique hder
  have hb := powerCircle_derivative_bound m hm hm2 d hd0.le
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs] at hb
  have hE : 2 ≤ Real.exp d := by linarith [Real.add_one_le_exp d]
  have hN : Real.exp (-d) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hratio : 1+Real.exp d ≤ 8*Real.sinh d := by rw [Real.sinh_eq]; linarith
  have hscaled := mul_le_mul_of_nonneg_left hratio (norm_nonneg m)
  nlinarith

/-- Uniform control of the actual Legendre derivative on the closed physical exponent strip.
Its role is to bound the reflected difference, not either growing direct kernel separately. -/
theorem legendre_first_bounded (m : ℂ) (hm : 0 ≤ m.re) (hm2 : m.re ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 1 ≤ z → ‖legendreKernelFirst (-m) z‖ ≤ C := by
  have hc : ContinuousOn (legendreKernelFirst (-m)) (Icc 1 (Real.cosh 1)) :=
    fun z hz => (legendreKernel_derivatives (-m) (by linarith [hz.1])).2.continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C (8*‖m‖), le_trans (by positivity) (le_max_right _ _), fun z hz => ?_⟩
  by_cases hsmall : z ≤ Real.cosh 1
  · exact (hC z ⟨hz,hsmall⟩).trans (le_max_left _ _)
  · let d := Real.arcosh z
    have hd0 : 0 ≤ d := Real.arcosh_nonneg hz
    have he : Real.cosh d=z := Real.cosh_arcosh hz
    have hd : 1 ≤ d := by
      have h := Real.cosh_le_cosh.mp (show Real.cosh 1 ≤ Real.cosh d by rw [he]; exact le_of_not_ge hsmall)
      simpa only [abs_one,abs_of_nonneg hd0] using h
    rw [← he]
    exact (legendre_first_large_radius m hm hm2 d hd).trans (le_max_right _ _)

private theorem legendre_difference_bound (m : ℂ) (C : ℝ)
    (hC : ∀ z : ℝ, 1 ≤ z → ‖legendreKernelFirst (-m) z‖ ≤ C)
    (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    ‖legendreKernel (-m) y-legendreKernel (-m) x‖ ≤ C*|y-x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Ici (1:ℝ))
    (fun z hz => (legendreKernel_derivatives (-m) (lt_of_lt_of_le zero_lt_one hz)).1.hasDerivWithinAt)
    (fun z hz => hC z hz) (convex_Ici 1) hx hy
  simpa only [Real.norm_eq_abs] using h

private theorem legendre_near_characteristic_bound (m : ℂ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ z : ℝ, 1 ≤ z → ‖legendreKernelFirst (-m) z‖ ≤ C)
    (z : ℝ) (hz : 1 ≤ z) (hz3 : z ≤ 3) : ‖legendreKernel (-m) z‖ ≤ 2*C+1 := by
  have h := legendre_difference_bound m C hC 1 z le_rfl hz
  rw [legendreKernel_one,abs_of_nonneg (by linarith : 0 ≤ z-1)] at h
  have hb : ‖legendreKernel (-m) z-1‖ ≤ 2*C := h.trans (by nlinarith)
  calc
    ‖legendreKernel (-m) z‖ = ‖(legendreKernel (-m) z-1)+1‖ := by rw [sub_add_cancel]
    _ ≤ ‖legendreKernel (-m) z-1‖+‖(1:ℂ)‖ := norm_add_le _ _
    _ ≤ 2*C+1 := by rw [norm_one]; linarith

private theorem reflected_invariant_distance (h x y : ℝ) :
    |invariant h x y-invariant h x (-y)| ≤ 2 := by
  have he : invariant h x y-invariant h x (-y)=2*Real.tanh x*Real.tanh y := by
    simp only [invariant,Real.sinh_neg,Real.cosh_neg,Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos x).ne',(Real.cosh_pos y).ne']
    ring
  rw [he,abs_mul,abs_mul,abs_of_pos (show (0:ℝ)<2 by norm_num)]
  have hb := mul_le_mul (Real.abs_tanh_lt_one x).le (Real.abs_tanh_lt_one y).le
    (abs_nonneg _) (show (0:ℝ) ≤ 1 by norm_num)
  nlinarith

private theorem invariant_upper_of_reflection_absent (h x y : ℝ) (hh : 0 ≤ h)
    (ha : ¬ |x+y| ≤ h) : invariant h x y ≤ 3 := by
  have hc : Real.cosh h < Real.cosh (x+y) := by
    apply Real.cosh_lt_cosh.mpr
    simpa only [abs_of_nonneg hh] using lt_of_not_ge ha
  have hz : invariant h x (-y) < 1 := by
    simp only [invariant,Real.sinh_neg,Real.cosh_neg]
    rw [div_lt_iff₀ (mul_pos (Real.cosh_pos x) (Real.cosh_pos y))]
    rw [Real.cosh_add] at hc
    linarith
  have hb := reflected_invariant_distance h x y
  linarith [le_abs_self (invariant h x y-invariant h x (-y))]

/-- The complete reflected causal kernel is uniformly bounded for every physical principal
exponent. Both characteristic indicators and the original factor one half are retained. -/
theorem reflected_principal_kernel_bounded (m : ℂ) (hm : 0 ≤ m.re) (hm2 : m.re ≤ 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ h x y : ℝ,
      ‖((if |x-y| ≤ h then riemannKernel (-m) h x y else 0)-
        (if |x+y| ≤ h then riemannKernel (-m) h x (-y) else 0))/2‖ ≤ B := by
  obtain ⟨C,hC0,hC⟩ := legendre_first_bounded m hm hm2
  refine ⟨C+1,by positivity,fun h x y => ?_⟩
  by_cases hp : |x-y| ≤ h
  · have hh : 0 ≤ h := (abs_nonneg _).trans hp
    have hz : 1 ≤ invariant h x y := invariant_causal ⟨h,x,y,hp⟩
    by_cases hn : |x+y| ≤ h
    · have hz' : 1 ≤ invariant h x (-y) :=
        invariant_causal ⟨h,x,-y,by simpa only [sub_neg_eq_add] using hn⟩
      have hb := legendre_difference_bound m C hC _ _ hz' hz
      have hi := mul_le_mul_of_nonneg_left (reflected_invariant_distance h x y) hC0
      simp only [if_pos hp,if_pos hn,riemannKernel,norm_div,Complex.norm_ofNat]
      apply (div_le_iff₀ (show (0:ℝ)<2 by norm_num)).mpr
      nlinarith
    · have hb := legendre_near_characteristic_bound m C hC0 hC _ hz
        (invariant_upper_of_reflection_absent h x y hh hn)
      simp only [if_pos hp,if_neg hn,sub_zero,riemannKernel,norm_div,Complex.norm_ofNat]
      apply (div_le_iff₀ (show (0:ℝ)<2 by norm_num)).mpr
      linarith
  · by_cases hn : |x+y| ≤ h
    · have hh : 0 ≤ h := (abs_nonneg _).trans hn
      have hz : 1 ≤ invariant h x (-y) :=
        invariant_causal ⟨h,x,-y,by simpa only [sub_neg_eq_add] using hn⟩
      have hz3 := invariant_upper_of_reflection_absent h x (-y) hh
        (by simpa only [sub_eq_add_neg] using hp)
      have hb := legendre_near_characteristic_bound m C hC0 hC _ hz hz3
      simp only [if_neg hp,if_pos hn,zero_sub,riemannKernel,norm_div,norm_neg,Complex.norm_ofNat]
      apply (div_le_iff₀ (show (0:ℝ)<2 by norm_num)).mpr
      linarith
    · simp only [if_neg hp,if_neg hn,sub_zero,zero_div,norm_zero]
      positivity

/-- The same bound applies to the corpus's original Dirichlet kernel at the actual
principal frequency parametrization, with no restriction on time or spatial coordinates. -/
theorem principal_dirichlet_kernel_bounded (m : ℂ) (hm : 0 ≤ m.re) (hm2 : m.re ≤ 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ h x y : ℝ,
      ‖dirichletCausalKernel (Complex.I*(m-1/2)) h x y‖ ≤ B := by
  have he : -(1:ℂ)/2+Complex.I*(Complex.I*(m-1/2)) = -m := by
    ring_nf
    rw [Complex.I_sq]
    ring
  simpa only [dirichletCausalKernel,bmRiemannKernel,he] using
    reflected_principal_kernel_bounded m hm hm2

end
end RHTower.D4BMPrincipalReflection
