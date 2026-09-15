import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalJacobiMoment
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import GaloisForLFunctions.HTGeometry.ClockParametricIntegralHolomorphy

/-! Source-normalized Jacobi monodromy and finite exponential type of its compact contour. -/

open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false

/-- The original polynomial-coordinate source lifted to the logarithmic cover. -/
def fundamentalJacobiLogKernel (n : ℕ) (w s u : ℂ) : ℂ :=
  Complex.exp ((w+1)*u) * (2-Complex.exp u)^(2*s) * (1-Complex.exp u)^n

/-- Compact lifted-circle period of the original Jacobi source. -/
def fundamentalJacobiContour (n : ℕ) (w s : ℂ) : ℂ :=
  I * ∫ t in (0:ℝ)..(2*Real.pi), fundamentalJacobiLogKernel n w s ((t:ℂ)*I)

private theorem two_sub_exp_slit {u : ℂ} (hu : u.re ≤ 0) :
    2-Complex.exp u ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have he : ‖Complex.exp u‖ ≤ 1 := by
    rw [Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr hu
  have hr := (Complex.re_le_norm (Complex.exp u)).trans he
  change 0 < 2-(Complex.exp u).re
  linarith

theorem fundamentalJacobiLogKernel_differentiableAt (n : ℕ) (w s : ℂ)
    {u : ℂ} (hu : u.re ≤ 0) :
    DifferentiableAt ℂ (fundamentalJacobiLogKernel n w s) u := by
  have hp : DifferentiableAt ℂ (fun z : ℂ => (2-Complex.exp z)^(2*s)) u :=
    ((Complex.hasStrictDerivAt_cpow_const (two_sub_exp_slit hu)).hasDerivAt.differentiableAt).comp u
      ((differentiableAt_const (2:ℂ)).sub Complex.differentiableAt_exp)
  have he : DifferentiableAt ℂ (fun z : ℂ => Complex.exp ((w+1)*z)) u := by fun_prop
  exact (he.mul hp).mul
    (((differentiableAt_const (1:ℂ)).sub Complex.differentiableAt_exp).pow n)

theorem fundamentalJacobiLogKernel_period (n : ℕ) (w s u : ℂ) :
    fundamentalJacobiLogKernel n w s (u+2*Real.pi*I) =
      Complex.exp (2*Real.pi*I*w) * fundamentalJacobiLogKernel n w s u := by
  have hu : Complex.exp (u+2*Real.pi*I)=Complex.exp u := by
    rw [Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]
  have hw : Complex.exp ((w+1)*(u+2*Real.pi*I)) =
      Complex.exp (2*Real.pi*I*w)*Complex.exp ((w+1)*u) := by
    rw [show (w+1)*(u+2*Real.pi*I)=2*Real.pi*I*w+(w+1)*u+2*Real.pi*I by ring,
      Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one,Complex.exp_add]
  simp only [fundamentalJacobiLogKernel,hu,hw]
  ring

/-- Exact finite-cutoff contour identity; no endpoint estimate is supplied. -/
theorem fundamentalJacobiLogKernel_rectangle (n : ℕ) (w s : ℂ)
    {a : ℝ} (ha : a ≤ 0) :
    (Complex.exp (2*Real.pi*I*w)-1) *
      (∫ x in a..0, fundamentalJacobiLogKernel n w s (x:ℂ)) =
      fundamentalJacobiContour n w s -
        I * ∫ t in (0:ℝ)..(2*Real.pi),
          fundamentalJacobiLogKernel n w s ((a:ℂ)+(t:ℂ)*I) := by
  have hd : DifferentiableOn ℂ (fundamentalJacobiLogKernel n w s)
      (uIcc ((a:ℂ)).re (2*Real.pi*I:ℂ).re ×ℂ
        uIcc ((a:ℂ)).im (2*Real.pi*I:ℂ).im) := by
    intro u hu
    apply (fundamentalJacobiLogKernel_differentiableAt n w s ?_).differentiableWithinAt
    have h : u.re ∈ uIcc a 0 := by simpa using hu.1
    rw [uIcc_of_le ha] at h
    exact h.2
  have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (fundamentalJacobiLogKernel n w s) (a:ℂ) (2*Real.pi*I:ℂ) hd
  norm_num at hr
  have ht : (∫ x in a..0,
      fundamentalJacobiLogKernel n w s ((x:ℂ)+2*Real.pi*I)) =
      Complex.exp (2*Real.pi*I*w) *
        (∫ x in a..0, fundamentalJacobiLogKernel n w s (x:ℂ)) := by
    simp_rw [fundamentalJacobiLogKernel_period]
    exact intervalIntegral.integral_const_mul _ _
  rw [ht] at hr
  change _ = I * _ - I * _
  linear_combination -hr

private theorem fundamentalJacobiLogKernel_real (n : ℕ) (w s : ℂ)
    {x : ℝ} (hx : 0 < x) :
    fundamentalJacobiLogKernel n w s (Real.log x:ℂ) =
      (x:ℂ)^(w+1) * fundamentalJacobiCore n s x := by
  have he : Complex.exp (Real.log x:ℂ)=(x:ℂ) := by
    rw [Complex.ofReal_log hx.le,Complex.exp_log (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [fundamentalJacobiLogKernel,he,Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr hx.ne') (w+1),← Complex.ofReal_log hx.le]
  simp only [fundamentalJacobiCore,Complex.ofReal_sub,Complex.ofReal_ofNat]
  rw [mul_comm (w+1) (Real.log x:ℂ)]
  ring

/-- The logarithmic contour's horizontal leg is the actual original Jacobi integral. -/
theorem fundamentalJacobiLogKernel_real_integral (n : ℕ) (w s : ℂ)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    (∫ x in (Real.log e)..0, fundamentalJacobiLogKernel n w s (x:ℂ)) =
      ∫ x in e..1, (x:ℂ)^w*fundamentalJacobiCore n s x := by
  have hc : ContinuousOn Real.log (uIcc e 1) := by
    intro x hx
    rw [uIcc_of_le he1] at hx
    exact (Real.hasDerivAt_log (he.trans_le hx.1).ne').continuousAt.continuousWithinAt
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := fun u : ℝ => fundamentalJacobiLogKernel n w s (u:ℂ))
    (f := Real.log) (f' := fun x => x⁻¹) (a := e) (b := 1) hc
    (fun x hx => by
      rw [min_eq_left he1,max_eq_right he1] at hx
      exact Real.hasDerivAt_log (he.trans hx.1).ne')
    (fun x hx => by
      rw [min_eq_left he1,max_eq_right he1] at hx
      exact inv_nonneg.mpr (he.trans hx.1).le)
  rw [Real.log_one] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le he1] at hx
  have hx0 := he.trans_le hx.1
  dsimp only [Function.comp_apply]
  rw [Complex.real_smul,fundamentalJacobiLogKernel_real n w s hx0,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx0.ne'),Complex.cpow_one,
    Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hx0.ne']

/-- The full monodromy identity at every positive original radial cutoff. -/
theorem fundamentalJacobiContour_cutoff (n : ℕ) (w s : ℂ)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    (Complex.exp (2*Real.pi*I*w)-1) *
      (∫ x in e..1, (x:ℂ)^w*fundamentalJacobiCore n s x) =
      fundamentalJacobiContour n w s - I * ∫ t in (0:ℝ)..(2*Real.pi),
        fundamentalJacobiLogKernel n w s ((Real.log e:ℂ)+(t:ℂ)*I) := by
  have ha : Real.log e ≤ 0 := Real.log_nonpos he.le he1
  simpa only [fundamentalJacobiLogKernel_real_integral n w s he he1] using
    fundamentalJacobiLogKernel_rectangle n w s ha

/-- The same source core on the complex disk, used to control its small-circle remainder. -/
def fundamentalJacobiComplexCore (n : ℕ) (s z : ℂ) : ℂ :=
  (2-z)^(2*s)*(1-z)^n

def fundamentalJacobiComplexCoreFirst (n : ℕ) (s z : ℂ) : ℂ :=
  -(2*s)*(2-z)^(2*s-1)*(1-z)^n - (n:ℂ)*(2-z)^(2*s)*(1-z)^(n-1)

private theorem two_sub_slit {z : ℂ} (hz : z.re < 2) :
    2-z ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  change 0 < 2-z.re
  linarith

theorem fundamentalJacobiComplexCore_hasDerivAt (n : ℕ) (s : ℂ)
    {z : ℂ} (hz : z.re < 2) :
    HasDerivAt (fundamentalJacobiComplexCore n s)
      (fundamentalJacobiComplexCoreFirst n s z) z := by
  have hp := ((hasDerivAt_const z (2:ℂ)).sub (hasDerivAt_id z)).cpow_const
    (c := 2*s) (two_sub_slit hz)
  have hn := ((hasDerivAt_const z (1:ℂ)).sub (hasDerivAt_id z)).pow n
  exact (hp.mul hn).congr_deriv (by
    dsimp only [fundamentalJacobiComplexCoreFirst]
    simp only [zero_sub,mul_neg,mul_one,Pi.pow_apply,Pi.sub_apply,id_eq]
    ring)

theorem fundamentalJacobiComplexCoreFirst_continuousAt (n : ℕ) (s : ℂ)
    {z : ℂ} (hz : z.re < 2) :
    ContinuousAt (fundamentalJacobiComplexCoreFirst n s) z := by
  have hp (c : ℂ) : ContinuousAt (fun z : ℂ => (2-z)^c) z :=
    (((hasDerivAt_const z (2:ℂ)).sub (hasDerivAt_id z)).cpow_const
      (c := c) (two_sub_slit hz)).continuousAt
  have hn : ContinuousAt (fun z : ℂ => 1-z) z := by fun_prop
  exact (((hp _).const_mul (-(2*s))).mul (hn.pow n)).sub
    (((hp _).const_mul (n:ℂ)).mul (hn.pow (n-1)))

/-- Source-derived complex first-remainder bound on the whole unit disk. -/
theorem fundamentalJacobiComplexCore_first_bound (n : ℕ) (s : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖fundamentalJacobiComplexCore n s z-(2:ℂ)^(2*s)‖ ≤ C*‖z‖ := by
  have hr {z : ℂ} (hz : z ∈ Metric.closedBall (0:ℂ) 1) : z.re < 2 := by
    have hn : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall,dist_zero_right] using hz
    have h := (Complex.re_le_norm z).trans hn
    linarith
  have hc : ContinuousOn (fundamentalJacobiComplexCoreFirst n s) (Metric.closedBall (0:ℂ) 1) :=
    fun z hz => (fundamentalJacobiComplexCoreFirst_continuousAt n s (hr hz)).continuousWithinAt
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro z hz
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fundamentalJacobiComplexCore n s) (f' := fundamentalJacobiComplexCoreFirst n s)
    (fun y hy => (fundamentalJacobiComplexCore_hasDerivAt n s (hr hy)).hasDerivWithinAt)
    (fun y hy => (hC y hy).trans (le_max_left C 0))
    (convex_closedBall (0:ℂ) 1) (by simp : (0:ℂ) ∈ Metric.closedBall (0:ℂ) 1)
    (by simpa [Metric.mem_closedBall,dist_zero_right] using hz)
  simpa only [fundamentalJacobiComplexCore,sub_zero,one_pow,mul_one] using h

private theorem jacobi_circle_power_integral (w : ℂ) (hw : w+1≠0) :
    I * (∫ t in (0:ℝ)..(2*Real.pi), Complex.exp ((w+1)*((t:ℂ)*I))) =
      (Complex.exp (2*Real.pi*I*w)-1)/(w+1) := by
  have he (t : ℝ) : (w+1)*((t:ℂ)*I)=((w+1)*I)*(t:ℂ) := by ring
  simp_rw [he]
  rw [integral_exp_mul_complex (mul_ne_zero hw Complex.I_ne_zero)]
  have ht : Complex.exp (((w+1)*I)*((2*Real.pi:ℝ):ℂ)) =
      Complex.exp (2*Real.pi*I*w) := by
    rw [show ((w+1)*I)*((2*Real.pi:ℝ):ℂ)=2*Real.pi*I*w+2*Real.pi*I by push_cast;ring,
      Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]
  rw [ht]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  field_simp

private theorem jacobi_logKernel_circle (n : ℕ) (w s : ℂ)
    {e : ℝ} (he : 0 < e) (t : ℝ) :
    fundamentalJacobiLogKernel n w s ((Real.log e:ℂ)+(t:ℂ)*I) =
      (e:ℂ)^(w+1)*Complex.exp ((w+1)*((t:ℂ)*I))*
        fundamentalJacobiComplexCore n s ((e:ℂ)*Complex.exp ((t:ℂ)*I)) := by
  have he' : Complex.exp (Real.log e:ℂ)=(e:ℂ) := by
    rw [Complex.ofReal_log he.le,Complex.exp_log (Complex.ofReal_ne_zero.mpr he.ne')]
  rw [fundamentalJacobiLogKernel,Complex.exp_add,he',mul_add,Complex.exp_add,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr he.ne') (w+1),
    ← Complex.ofReal_log he.le]
  rw [mul_comm (w+1) (Real.log e:ℂ)]
  simp only [fundamentalJacobiComplexCore,mul_assoc]

/-- The exact small-circle remainder after restoring the source's original first coefficient. -/
def fundamentalJacobiCircleRemainder (n : ℕ) (w s : ℂ) (e : ℝ) : ℂ :=
  (e:ℂ)^(w+1) * (I * ∫ t in (0:ℝ)..(2*Real.pi),
    Complex.exp ((w+1)*((t:ℂ)*I)) *
      (fundamentalJacobiComplexCore n s ((e:ℂ)*Complex.exp ((t:ℂ)*I))-(2:ℂ)^(2*s)))

private theorem jacobi_circle_core_continuous (n : ℕ) (s : ℂ)
    {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) :
    Continuous (fun t : ℝ => fundamentalJacobiComplexCore n s ((e:ℂ)*Complex.exp ((t:ℂ)*I))) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hr : ((e:ℂ)*Complex.exp ((t:ℂ)*I)).re < 2 := by
    have hn : ‖(e:ℂ)*Complex.exp ((t:ℂ)*I)‖=e := by
      rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg he]
    have h := Complex.re_le_norm ((e:ℂ)*Complex.exp ((t:ℂ)*I))
    rw [hn] at h
    linarith
  have ha : ContinuousAt (fun t : ℝ => (e:ℂ)*Complex.exp ((t:ℂ)*I)) t := by fun_prop
  exact (fundamentalJacobiComplexCore_hasDerivAt n s hr).continuousAt.comp (f := fun t : ℝ => (e:ℂ)*Complex.exp ((t:ℂ)*I)) ha

/-- The finite cutoff and its prescribed counterterm equal the compact contour minus one
source-controlled small-circle remainder. -/
theorem fundamentalJacobiContour_restored_cutoff (n : ℕ) (w s : ℂ) (hw : w+1≠0)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    (Complex.exp (2*Real.pi*I*w)-1) *
      ((∫ x in e..1, (x:ℂ)^w*fundamentalJacobiCore n s x)+
        (2:ℂ)^(2*s)*(e:ℂ)^(w+1)/(w+1)) =
      fundamentalJacobiContour n w s - fundamentalJacobiCircleRemainder n w s e := by
  have hc := jacobi_circle_core_continuous n s he.le he1
  have hp : Continuous (fun t : ℝ => Complex.exp ((w+1)*((t:ℂ)*I))) := by fun_prop
  have hr : fundamentalJacobiCircleRemainder n w s e =
      I * (∫ t in (0:ℝ)..(2*Real.pi),
        fundamentalJacobiLogKernel n w s ((Real.log e:ℂ)+(t:ℂ)*I)) -
      (Complex.exp (2*Real.pi*I*w)-1)*((2:ℂ)^(2*s)*(e:ℂ)^(w+1)/(w+1)) := by
    simp only [fundamentalJacobiCircleRemainder,jacobi_logKernel_circle n w s he,mul_sub,mul_assoc]
    have h1 : IntervalIntegrable (fun t : ℝ => Complex.exp ((w+1)*((t:ℂ)*I))*
        fundamentalJacobiComplexCore n s ((e:ℂ)*Complex.exp ((t:ℂ)*I))) volume 0 (2*Real.pi) :=
      (hp.mul hc).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun t : ℝ => Complex.exp ((w+1)*((t:ℂ)*I))*(2:ℂ)^(2*s))
        volume 0 (2*Real.pi) := (hp.mul continuous_const).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub h1 h2,
      intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul]
    have hv := jacobi_circle_power_integral w hw
    simp only [mul_assoc] at hv
    linear_combination -(e:ℂ)^(w+1)*(2:ℂ)^(2*s)*hv
  have h := fundamentalJacobiContour_cutoff n w s he he1
  rw [hr]
  linear_combination h

/-- The restored small-circle source is bounded by the required vanishing power. -/
theorem fundamentalJacobiCircleRemainder_bound (n : ℕ) (w s : ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ e : ℝ, 0 < e → e ≤ 1 →
      ‖fundamentalJacobiCircleRemainder n w s e‖ ≤ K*e^(w.re+2) := by
  obtain ⟨C,hC0,hC⟩ := fundamentalJacobiComplexCore_first_bound n s
  let B : ℝ := Real.exp (2*Real.pi*|w.im|)
  refine ⟨2*Real.pi*B*C,by dsimp [B];positivity,?_⟩
  intro e he he1
  have hp (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 2*Real.pi) :
      ‖Complex.exp ((w+1)*((t:ℂ)*I))‖ ≤ B := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hr : ((w+1)*((t:ℂ)*I)).re = -w.im*t := by simp [Complex.mul_re]
    rw [hr]
    calc
      -w.im*t ≤ |w.im| *t := mul_le_mul_of_nonneg_right (neg_le_abs _) ht0
      _ ≤ |w.im| *(2*Real.pi) := mul_le_mul_of_nonneg_left ht1 (abs_nonneg _)
      _ = _ := by ring
  have hnorm (t : ℝ) : ‖(e:ℂ)*Complex.exp ((t:ℂ)*I)‖=e := by
    rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos he]
  have hcore (t : ℝ) :
      ‖fundamentalJacobiComplexCore n s ((e:ℂ)*Complex.exp ((t:ℂ)*I))-(2:ℂ)^(2*s)‖ ≤ C*e := by
    simpa only [hnorm] using hC ((e:ℂ)*Complex.exp ((t:ℂ)*I)) (by rw [hnorm];exact he1)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 2*Real.pi)
    (f := fun t : ℝ => Complex.exp ((w+1)*((t:ℂ)*I))*
      (fundamentalJacobiComplexCore n s ((e:ℂ)*Complex.exp ((t:ℂ)*I))-(2:ℂ)^(2*s)))
    (C := B*(C*e)) (fun t ht => by
      rw [uIoc_of_le (by positivity : (0:ℝ)≤2*Real.pi)] at ht
      rw [norm_mul]
      exact mul_le_mul (hp t ht.1.le ht.2) (hcore t) (norm_nonneg _)
        (by dsimp [B];positivity))
  rw [sub_zero,abs_of_pos (by positivity : (0:ℝ)<2*Real.pi)] at hi
  rw [mul_comm (B*(C*e)) (2*Real.pi)] at hi
  calc
    ‖fundamentalJacobiCircleRemainder n w s e‖ =
        e^(w.re+1)*‖∫ t in (0:ℝ)..(2*Real.pi), Complex.exp ((w+1)*((t:ℂ)*I))*
          (fundamentalJacobiComplexCore n s ((e:ℂ)*Complex.exp ((t:ℂ)*I))-(2:ℂ)^(2*s))‖ := by
      rw [fundamentalJacobiCircleRemainder,norm_mul,norm_mul,Complex.norm_I,one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos he]
      simp
    _ ≤ e^(w.re+1)*((2*Real.pi)*(B*(C*e))) :=
      mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg he.le _)
    _ = (2*Real.pi*B*C)*e^(w.re+2) := by
      rw [show w.re+2=(w.re+1)+1 by ring,Real.rpow_add he (w.re+1) 1,Real.rpow_one]
      ring

/-- The actual restored inner contour tends to zero throughout the first-subtraction chamber. -/
theorem fundamentalJacobiCircleRemainder_tendsto_zero (n : ℕ) (w s : ℂ)
    (hw : -2 < w.re) :
    Tendsto (fundamentalJacobiCircleRemainder n w s) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨K,_,hK⟩ := fundamentalJacobiCircleRemainder_bound n w s
  have hp : 0 < w.re+2 := by linarith
  have hl : Tendsto (fun e : ℝ => K*e^(w.re+2)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := ((Real.continuousAt_rpow_const 0 (w.re+2) (Or.inr hp.le)).const_mul K).tendsto
    simpa only [Real.zero_rpow hp.ne',mul_zero] using h.mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ hl
  have he1a : ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < 1 := Iio_mem_nhds (by norm_num)
  have he1 : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < 1 :=
    he1a.filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,he1] with e he he1
  exact hK e he he1.le

/-- The compact contour equals the existing source-fixed finite part times its exact monodromy.
The original endpoint constant is retained; no continuation or matching hypothesis is added. -/
theorem fundamentalJacobiContour_eq_moment (n : ℕ) (w s : ℂ)
    (hw : -2 < w.re) (hw1 : w+1≠0) :
    fundamentalJacobiContour n w s =
      (Complex.exp (2*Real.pi*I*w)-1)*fundamentalJacobiMoment n w s := by
  have hl := (fundamentalJacobiMoment_cutoff n w s hw hw1).const_mul
    (Complex.exp (2*Real.pi*I*w)-1)
  have hr := (tendsto_const_nhds (x := fundamentalJacobiContour n w s)).sub
    (fundamentalJacobiCircleRemainder_tendsto_zero n w s hw)
  simp only [sub_zero] at hr
  apply (tendsto_nhds_unique_of_eventuallyEq hl hr ?_).symm
  have he1a : ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < 1 := Iio_mem_nhds (by norm_num)
  have he1 : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < 1 :=
    he1a.filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,he1] with e he he1
  exact fundamentalJacobiContour_restored_cutoff n w s hw1 he he1.le

private theorem jacobi_circle_base_slit (t : ℝ) :
    2-Complex.exp ((t:ℂ)*I) ∈ Complex.slitPlane :=
  two_sub_exp_slit (by simp)

/-- Every affine physical-parameter specialization of the actual compact source contour is entire. -/
theorem fundamentalJacobiContour_affine_entire (n : ℕ) (alpha beta : ℂ) :
    Differentiable ℂ (fun w => fundamentalJacobiContour n w (alpha*w+beta)) := by
  let F : ℝ → ℂ → ℂ := fun t w => fundamentalJacobiLogKernel n w (alpha*w+beta) ((t:ℂ)*I)
  have hc : Continuous (fun p : ℝ × ℂ => F p.1 p.2) := by
    have hb : Continuous (fun p : ℝ × ℂ => 2-Complex.exp ((p.1:ℂ)*I)) := by fun_prop
    have hp : Continuous (fun p : ℝ × ℂ => (2-Complex.exp ((p.1:ℂ)*I))^(2*(alpha*p.2+beta))) :=
      hb.cpow (by fun_prop) (fun p => jacobi_circle_base_slit p.1)
    have he : Continuous (fun p : ℝ × ℂ => Complex.exp ((p.2+1)*((p.1:ℂ)*I))) := by fun_prop
    exact (he.mul hp).mul (by fun_prop)
  have hd (t : ℝ) : Differentiable ℂ (F t) := by
    intro w
    have hb : 2-Complex.exp ((t:ℂ)*I) ≠ 0 := Complex.slitPlane_ne_zero (jacobi_circle_base_slit t)
    have hp : DifferentiableAt ℂ (fun w : ℂ => (2-Complex.exp ((t:ℂ)*I))^(2*(alpha*w+beta))) w := by
      exact ((show DifferentiableAt ℂ (fun w : ℂ => 2*(alpha*w+beta)) w by fun_prop).const_cpow
        (Or.inl hb))
    have he : DifferentiableAt ℂ (fun w : ℂ => Complex.exp ((w+1)*((t:ℂ)*I))) w := by fun_prop
    exact (he.mul hp).mul_const _
  intro w
  have hi := GaloisForLFunctions.HTGeometry.differentiableAt_intervalIntegral_of_holomorphic
    (a := (0:ℝ)) (b := 2*Real.pi) (ρ := |w.im|+1) (ρ' := |w.im|+2)
    (by linarith) hc (fun t => (hd t).differentiableOn)
    (z := w) (by change |w.im| < |w.im|+1;linarith)
  exact hi.const_mul I

/-- Every affine physical source specialization of the compact contour has finite exponential type. -/
theorem fundamentalJacobiContour_affine_growth (n : ℕ) (alpha beta : ℂ) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧ ∀ w : ℂ,
      ‖fundamentalJacobiContour n w (alpha*w+beta)‖ ≤ C*Real.exp (A*‖w‖) := by
  have hc : Continuous (fun t : ℝ => Complex.log (2-Complex.exp ((t:ℂ)*I))) :=
    (show Continuous (fun t : ℝ => 2-Complex.exp ((t:ℂ)*I)) by fun_prop).clog
      jacobi_circle_base_slit
  obtain ⟨L0,hL0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.continuousOn : ContinuousOn _ (Icc (0:ℝ) (2*Real.pi)))
  let L : ℝ := max L0 0
  have hL : 0 ≤ L := le_max_right _ _
  have hLb (t : ℝ) (ht : t ∈ Icc (0:ℝ) (2*Real.pi)) :
      ‖Complex.log (2-Complex.exp ((t:ℂ)*I))‖ ≤ L := (hL0 t ht).trans (le_max_left _ _)
  let A : ℝ := 2*Real.pi+2*L*‖alpha‖
  let C : ℝ := 2*Real.pi*2^n*Real.exp (2*L*‖beta‖)
  refine ⟨A,C,by dsimp [A];positivity,by dsimp [C];positivity,?_⟩
  intro w
  have hp (t : ℝ) (ht : t ∈ Icc (0:ℝ) (2*Real.pi)) :
      ‖(2-Complex.exp ((t:ℂ)*I))^(2*(alpha*w+beta))‖ ≤
        Real.exp ((2*L*‖alpha‖)*‖w‖+2*L*‖beta‖) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero (jacobi_circle_base_slit t)),
      Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have ha : ‖2*(alpha*w+beta)‖ ≤ 2*(‖alpha‖*‖w‖+‖beta‖) := by
      calc
        _ = 2*‖alpha*w+beta‖ := by norm_num [norm_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (by simpa only [norm_mul] using norm_add_le (alpha*w) beta) (by norm_num)
    calc
      _ ≤ ‖Complex.log (2-Complex.exp ((t:ℂ)*I)) * (2*(alpha*w+beta))‖ := Complex.re_le_norm _
      _ = ‖Complex.log (2-Complex.exp ((t:ℂ)*I))‖ * ‖2*(alpha*w+beta)‖ := norm_mul _ _
      _ ≤ L*(2*(‖alpha‖*‖w‖+‖beta‖)) := mul_le_mul (hLb t ht) ha (norm_nonneg _) hL
      _ = _ := by ring
  have he (t : ℝ) (ht : t ∈ Icc (0:ℝ) (2*Real.pi)) :
      ‖Complex.exp ((w+1)*((t:ℂ)*I))‖ ≤ Real.exp (2*Real.pi*‖w‖) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hr : ((w+1)*((t:ℂ)*I)).re = -w.im*t := by simp [Complex.mul_re]
    rw [hr]
    calc
      -w.im*t ≤ |w.im| * t := mul_le_mul_of_nonneg_right (neg_le_abs _) ht.1
      _ ≤ ‖w‖*t := mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm w) ht.1
      _ ≤ ‖w‖*(2*Real.pi) := mul_le_mul_of_nonneg_left ht.2 (norm_nonneg _)
      _ = _ := by ring
  have hn (t : ℝ) : ‖(1-Complex.exp ((t:ℂ)*I))^n‖ ≤ (2:ℝ)^n := by
    rw [norm_pow]
    have hb : ‖1-Complex.exp ((t:ℂ)*I)‖ ≤ 2 := by
      calc
        _ ≤ ‖(1:ℂ)‖+‖Complex.exp ((t:ℂ)*I)‖ := norm_sub_le _ _
        _ = _ := by rw [norm_one,Complex.norm_exp_ofReal_mul_I];norm_num
    exact pow_le_pow_left₀ (norm_nonneg _) hb n
  have hf (t : ℝ) (ht : t ∈ Icc (0:ℝ) (2*Real.pi)) :
      ‖fundamentalJacobiLogKernel n w (alpha*w+beta) ((t:ℂ)*I)‖ ≤
        2^n*Real.exp (2*L*‖beta‖)*Real.exp (A*‖w‖) := by
    rw [fundamentalJacobiLogKernel,norm_mul,norm_mul]
    calc
      _ ≤ (Real.exp (2*Real.pi*‖w‖)*Real.exp ((2*L*‖alpha‖)*‖w‖+2*L*‖beta‖))*2^n :=
        mul_le_mul (mul_le_mul (he t ht) (hp t ht) (norm_nonneg _) (Real.exp_pos _).le)
          (hn t) (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [← Real.exp_add,show 2*Real.pi*‖w‖+((2*L*‖alpha‖)*‖w‖+2*L*‖beta‖)=
          2*L*‖beta‖+A*‖w‖ by dsimp [A];ring,Real.exp_add]
        ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 2*Real.pi)
    (f := fun t => fundamentalJacobiLogKernel n w (alpha*w+beta) ((t:ℂ)*I))
    (C := 2^n*Real.exp (2*L*‖beta‖)*Real.exp (A*‖w‖)) (fun t ht => by
      rw [uIoc_of_le (by positivity : (0:ℝ)≤2*Real.pi)] at ht
      exact hf t ⟨ht.1.le,ht.2⟩)
  rw [sub_zero,abs_of_pos (by positivity : (0:ℝ)<2*Real.pi)] at hi
  rw [fundamentalJacobiContour,norm_mul,Complex.norm_I,one_mul]
  calc
    _ ≤ (2^n*Real.exp (2*L*‖beta‖)*Real.exp (A*‖w‖))*(2*Real.pi) := hi
    _ = C*Real.exp (A*‖w‖) := by dsimp [C];ring

end
end RHTower.D4BMJointSource
