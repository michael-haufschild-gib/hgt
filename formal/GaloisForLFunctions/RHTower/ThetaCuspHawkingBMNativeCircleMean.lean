import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCircleSource
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-! The complete theta-source circle average and its original angular Darboux equation. -/
namespace RHTower.D4BMNativeCircle
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

def average (F : ℝ → ℂ) : ℂ :=
  (1/(2*Real.pi:ℂ)) * ∫ theta in Ioc 0 (2*Real.pi), F theta
def mean (q : XiZeroCopy) (d x k : ℝ) : ℂ := average (fun theta => source q d theta x k)

private def parameterDerivative (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  deriv (fun t => F (t,p.2)) p.1

private theorem partial_slice {F : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ F) (t theta : ℝ) :
    HasDerivAt (fun r => F (r,theta)) (fderiv ℝ F (t,theta) (1,0)) t :=
  ((hf.contDiffAt.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t theta))

private theorem partial_smooth {F : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (parameterDerivative F) := by
  have he : parameterDerivative F=fun p => fderiv ℝ F p (1,0) :=
    funext (fun p => (partial_slice hf p.1 p.2).deriv)
  rw [he]
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (hf.contDiffAt.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

private theorem average_hasDerivAt {F : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ F) (t : ℝ) :
    HasDerivAt (fun r => average (fun theta => F (r,theta)))
      (average (fun theta => parameterDerivative F (t,theta))) t := by
  have hd := partial_smooth hf
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hd.continuous.continuousOn : ContinuousOn (parameterDerivative F)
      (Icc (t-1) (t+1) ×ˢ Icc 0 (2*Real.pi)))
  have hn : Ioo (t-1) (t+1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hc (r : ℝ) : Continuous (fun theta => F (r,theta)) :=
    hf.continuous.comp (continuous_const.prodMk continuous_id)
  have hdc (r : ℝ) : Continuous (fun theta => parameterDerivative F (r,theta)) :=
    hd.continuous.comp (continuous_const.prodMk continuous_id)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc 0 (2*Real.pi)))
    (F := fun r theta => F (r,theta)) (F' := fun r theta => parameterDerivative F (r,theta))
    (bound := fun _ => C) hn
    (Filter.Eventually.of_forall (fun r => (hc r).aestronglyMeasurable.restrict))
    ((hc t).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((hdc t).aestronglyMeasurable.restrict)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with theta htheta
        intro r hr
        exact hC (r,theta) ⟨⟨hr.1.le,hr.2.le⟩,⟨htheta.1.le,htheta.2⟩⟩)
    (integrable_const C)
    (by filter_upwards with theta
        intro r hr
        exact (partial_slice hf r theta).differentiableAt.hasDerivAt)).2
  exact h.const_mul (1/(2*Real.pi:ℂ))

private theorem average_derivative {F : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ F) (t : ℝ) :
    deriv (fun r => average (fun theta => F (r,theta))) t=
      average (fun theta => deriv (fun r => F (r,theta)) t) :=
  (average_hasDerivAt hf t).deriv

private theorem average_second {F : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ F) (t : ℝ) :
    deriv (deriv (fun r => average (fun theta => F (r,theta)))) t=
      average (fun theta => deriv (deriv (fun r => F (r,theta))) t) := by
  have he : deriv (fun r => average (fun theta => F (r,theta)))=
      fun r => average (fun theta => parameterDerivative F (r,theta)) :=
    funext (fun r => (average_hasDerivAt hf r).deriv)
  rw [he,(average_hasDerivAt (partial_smooth hf) t).deriv]
  rfl

private theorem radial_family (q : XiZeroCopy) (x k : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => source q p.1 p.2 x k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hp : 0 < logCircle p.1 p.2 x k 1 := by
    dsimp [logCircle,circle,height]
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hs : ContDiffAt ℝ ∞ (fullSquarePotential q) (logCircle p.1 p.2 x k) :=
    contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q _ hp n)
  apply hs.comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

private theorem horizontal_family (q : XiZeroCopy) (d k : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => source q d p.2 p.1 k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hp : 0 < logCircle d p.2 p.1 k 1 := by
    dsimp [logCircle,circle,height]
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hs : ContDiffAt ℝ ∞ (fullSquarePotential q) (logCircle d p.2 p.1 k) :=
    contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q _ hp n)
  apply hs.comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

private theorem height_family (q : XiZeroCopy) (d x : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => source q d p.2 x p.1) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hp : 0 < logCircle d p.2 x p.1 1 := by
    dsimp [logCircle,circle,height]
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hs : ContDiffAt ℝ ∞ (fullSquarePotential q) (logCircle d p.2 x p.1) :=
    contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q _ hp n)
  apply hs.comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

private theorem average_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    average (fun theta => f theta+g theta)=average f+average g := by
  dsimp [average]
  rw [integral_add (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
  ring
private theorem average_sub {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    average (fun theta => f theta-g theta)=average f-average g := by
  dsimp [average]
  rw [integral_sub (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
  ring
private theorem average_const_mul (c : ℂ) (f : ℝ → ℂ) :
    average (fun theta => c*f theta)=c*average f := by
  dsimp [average]
  rw [integral_const_mul]
  ring

private theorem first_slice_continuous {F : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ F) (t : ℝ) :
    Continuous (fun theta => deriv (fun r => F (r,theta)) t) :=
  (partial_smooth hf).continuous.comp (continuous_const.prodMk continuous_id)
private theorem second_slice_continuous {F : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ F) (t : ℝ) :
    Continuous (fun theta => deriv (deriv (fun r => F (r,theta))) t) :=
  (partial_smooth (partial_smooth hf)).continuous.comp (continuous_const.prodMk continuous_id)

private theorem theta_smooth (q : XiZeroCopy) (d x k : ℝ) :
    ContDiff ℝ ∞ (fun theta => source q d theta x k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro theta
  have hp : 0 < logCircle d theta x k 1 := by
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hs : ContDiffAt ℝ ∞ (fullSquarePotential q) (logCircle d theta x k) :=
    contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q _ hp n)
  apply hs.comp theta
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

private theorem source_periodic (q : XiZeroCopy) (d x k theta : ℝ) :
    source q d (theta+2*Real.pi) x k=source q d theta x k := by
  simp [source,logCircle,circle,offset,height,denominator,Real.sin_add_two_pi,Real.cos_add_two_pi]

/-- Negating native radius is exactly the same upper-half-plane point after a
half-turn of the original angular chart. -/
theorem logCircle_neg_radius_eq_halfTurn (d theta x k : ℝ) :
    logCircle (-d) theta x k = logCircle d (theta + Real.pi) x k := by
  funext i
  fin_cases i <;> simp [logCircle, circle, offset, height, denominator]

/-- The source on a negative-radius chart is the source on that same literal
circle after its forced angular half-turn. -/
theorem source_neg_radius_eq_halfTurn (q : XiZeroCopy) (d theta x k : ℝ) :
    source q (-d) theta x k = source q d (theta + Real.pi) x k := by
  unfold source
  rw [logCircle_neg_radius_eq_halfTurn]

private theorem smooth_derivative {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (deriv f) :=
  (contDiff_infty_iff_deriv.mp hf).2

private theorem periodic_derivative {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : ∀ theta, f (theta+2*Real.pi)=f theta) (theta : ℝ) :
    deriv f (theta+2*Real.pi)=deriv f theta := by
  have h := ((hf.contDiffAt.differentiableAt (by simp)).hasDerivAt).scomp theta
    ((hasDerivAt_id theta).add_const (2*Real.pi))
  have he : (fun t => f (t+2*Real.pi))=f := funext hp
  simpa only [Function.comp_def,id_eq,one_smul,he] using h.deriv.symm

private theorem average_periodic_derivative {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : ∀ theta, f (theta+2*Real.pi)=f theta) : average (deriv f)=0 := by
  have hT : 0 ≤ 2*Real.pi := by positivity
  have h := intervalIntegral.integral_deriv_of_contDiffOn_Icc
    ((hf.of_le (by simp : (1:WithTop ℕ∞) ≤ ∞)).contDiffOn) hT
  rw [intervalIntegral.integral_of_le hT] at h
  dsimp [average]
  rw [h,show f (2*Real.pi)=f 0 by simpa using hp 0,sub_self,mul_zero]

/-- The original circle average has the full radial Darboux action on the original theta source. -/
theorem mean_radial_action (q : XiZeroCopy) (d x k : ℝ) :
    (Real.sinh d:ℂ)^(2 : ℕ)*deriv (deriv (fun r => mean q r x k)) d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*deriv (fun r => mean q r x k) d=
      (Real.sinh d:ℂ)^(2 : ℕ)*average (fun theta =>
        scalarLaplacian (fullSquarePotential q) (logCircle d theta x k)) := by
  have hf := radial_family q x k
  have hr := first_slice_continuous hf d
  have hrr := second_slice_continuous hf d
  have ht := theta_smooth q d x k
  have htt := (smooth_derivative (smooth_derivative ht)).continuous
  have hz : average (deriv (deriv (fun theta => source q d theta x k)))=0 :=
    average_periodic_derivative (smooth_derivative ht) (periodic_derivative ht (source_periodic q d x k))
  have h := congrArg average (funext (fun theta => source_darboux_integrand q d theta x k))
  erw [average_add ((hrr.const_mul ((Real.sinh d:ℂ)^(2 : ℕ))).add
      (hr.const_mul ((Real.sinh d:ℂ)*(Real.cosh d:ℂ)))) htt,
    average_add (hrr.const_mul ((Real.sinh d:ℂ)^(2 : ℕ)))
      (hr.const_mul ((Real.sinh d:ℂ)*(Real.cosh d:ℂ))),average_const_mul,average_const_mul,
    average_const_mul,hz,add_zero] at h
  rw [← average_second hf d,← average_derivative hf d] at h
  exact h

private theorem horizontal_theta_smooth (q : XiZeroCopy) (d x k : ℝ) :
    ContDiff ℝ ∞ (fun theta => deriv (fun r => source q d theta r k) x) := by
  have he : (fun theta => deriv (fun r => source q d theta r k) x)=
      fun theta => coordDeriv 0 (fullSquarePotential q) (logCircle d theta x k) :=
    funext (fun theta => source_horizontal_derivative q d theta x k)
  rw [he]
  apply contDiff_iff_contDiffAt.mpr
  intro theta
  have hp : 0 < logCircle d theta x k 1 := by
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hs : ContDiffAt ℝ ∞ (fullSquarePotential q) (logCircle d theta x k) :=
    contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q _ hp n)
  apply (coordDeriv_contDiffAt (m := ∞) (by simpa using hs) 0).comp theta
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

private theorem horizontal_theta_periodic (q : XiZeroCopy) (d x k theta : ℝ) :
    deriv (fun r => source q d (theta+2*Real.pi) r k) x=
      deriv (fun r => source q d theta r k) x :=
  congrArg (fun f : ℝ → ℂ => deriv f x) (funext (fun r => source_periodic q d r k theta))

/-- The actual base-point Laplacian commutes with averaging the complete original theta half-square. -/
theorem mean_laplacian_commutes (q : XiZeroCopy) (d x k : ℝ) :
    (Real.exp k:ℂ)^(2 : ℕ)*deriv (deriv (fun r => mean q d r k)) x+
      deriv (deriv (fun r => mean q d x r)) k-deriv (fun r => mean q d x r) k=
      average (fun theta => scalarLaplacian (fullSquarePotential q) (logCircle d theta x k)) := by
  have hx := horizontal_family q d k
  have hk := height_family q d x
  have hxx := second_slice_continuous hx x
  have hkk := second_slice_continuous hk k
  have hk1 := first_slice_continuous hk k
  have hg := horizontal_theta_smooth q d x k
  have hgp := (smooth_derivative hg).continuous
  have hz := average_periodic_derivative hg (horizontal_theta_periodic q d x k)
  have hQ : (fun theta => coordDeriv 0 (fullSquarePotential q) (logCircle d theta x k))=
      fun theta => deriv (fun r => source q d theta r k) x :=
    funext (fun theta => (source_horizontal_derivative q d theta x k).symm)
  have he (theta : ℝ) : scalarLaplacian (fullSquarePotential q) (logCircle d theta x k)=
      (Real.exp k:ℂ)^(2 : ℕ)*deriv (deriv (fun r => source q d theta r k)) x+
      deriv (deriv (fun r => source q d theta x r)) k-deriv (fun r => source q d theta x r) k+
      2*(Real.exp k:ℂ)*deriv (fun t => deriv (fun r => source q d t r k) x) theta := by
    have h := source_base_laplacian_integrand q d theta x k
    rw [hQ] at h
    linear_combination -h
  have h := congrArg average (funext he)
  erw [average_add (((hxx.const_mul ((Real.exp k:ℂ)^(2 : ℕ))).add hkk).sub hk1)
      (hgp.const_mul (2*(Real.exp k:ℂ))),
    average_sub ((hxx.const_mul ((Real.exp k:ℂ)^(2 : ℕ))).add hkk) hk1,
    average_add (hxx.const_mul ((Real.exp k:ℂ)^(2 : ℕ))) hkk,
    average_const_mul,average_const_mul,hz,mul_zero,add_zero] at h
  rw [← average_second hx x,← average_second hk k,← average_derivative hk k] at h
  exact h.symm

/-- The full native theta circle average solves the original hyperbolic Darboux equation. -/
theorem mean_darboux (q : XiZeroCopy) (d x k : ℝ) :
    (Real.sinh d:ℂ)^(2 : ℕ)*deriv (deriv (fun r => mean q r x k)) d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*deriv (fun r => mean q r x k) d=
      (Real.sinh d:ℂ)^(2 : ℕ)*((Real.exp k:ℂ)^(2 : ℕ)*deriv (deriv (fun r => mean q d r k)) x+
        deriv (deriv (fun r => mean q d x r)) k-deriv (fun r => mean q d x r) k) := by
  rw [mean_radial_action,mean_laplacian_commutes]

private theorem average_constant (c : ℂ) : average (fun _ => c)=c := by
  have hT : 0 ≤ 2*Real.pi := by positivity
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  dsimp [average]
  rw [← intervalIntegral.integral_of_le hT]
  simp only [intervalIntegral.integral_const,sub_zero,Complex.real_smul,Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  field_simp [hpi]

/-- Radius zero recovers the actual original theta half-square with unit normalization. -/
theorem mean_zero (q : XiZeroCopy) (x k : ℝ) :
    mean q 0 x k=fullSquarePotential q ![x,Real.exp k] := by
  have he : (fun theta => source q 0 theta x k)=fun _ => fullSquarePotential q ![x,Real.exp k] := by
    funext theta
    simp [source,logCircle,circle,offset,height,denominator]
  rw [mean,he,average_constant]

/-- The actual native-circle mean is even in signed radius.  This forces the
zero-radius odd germ to vanish, but does not by itself regularize the cap's
`arcosh (max 1 ·)` corner. -/
theorem mean_neg_radius (q : XiZeroCopy) (d x k : ℝ) :
    mean q (-d) x k = mean q d x k := by
  have hsource : (fun theta => source q (-d) theta x k) =
      fun theta => source q d (theta + Real.pi) x k := by
    funext theta
    exact source_neg_radius_eq_halfTurn q d theta x k
  rw [mean, hsource]
  unfold average
  congr 1
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hperiod : Function.Periodic (fun theta => source q d theta x k) (2 * Real.pi) :=
    fun theta => source_periodic q d x k theta
  change (∫ theta in Ioc (0 : ℝ) (2 * Real.pi),
      source q d (theta + Real.pi) x k) =
    ∫ theta in Ioc (0 : ℝ) (2 * Real.pi), source q d theta x k
  calc
    (∫ theta in Ioc (0 : ℝ) (2 * Real.pi), source q d (theta + Real.pi) x k) =
        ∫ theta in (0 : ℝ)..2 * Real.pi, source q d (theta + Real.pi) x k :=
      (intervalIntegral.integral_of_le hpi).symm
    _ = ∫ theta in Real.pi..2 * Real.pi + Real.pi, source q d theta x k :=
      by
        simpa only [zero_add] using
          intervalIntegral.integral_comp_add_right
            (a := (0 : ℝ)) (b := 2 * Real.pi)
            (fun theta => source q d theta x k) Real.pi
    _ = ∫ theta in (0 : ℝ)..2 * Real.pi, source q d theta x k := by
      simpa only [zero_add, add_comm] using (hperiod.intervalIntegral_add_eq 0 Real.pi).symm
    _ = ∫ theta in Ioc (0 : ℝ) (2 * Real.pi), source q d theta x k :=
      intervalIntegral.integral_of_le hpi

private theorem average_finite_smooth (n : ℕ) {F : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ F) :
    ContDiff ℝ n (fun r => average (fun theta => F (r,theta))) := by
  have hd : Differentiable ℝ (fun r => average (fun theta => F (r,theta))) :=
    fun r => (average_hasDerivAt hf r).differentiableAt
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr hd.continuous
  | succ n ih =>
    change ContDiff ℝ ((n:WithTop ℕ∞)+1) _
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨hd,by simp,?_⟩
    have he : deriv (fun r => average (fun theta => F (r,theta)))=
        fun r => average (fun theta => parameterDerivative F (r,theta)) :=
      funext (fun r => (average_hasDerivAt hf r).deriv)
    rw [he]
    exact ih (partial_smooth hf) (fun r => (average_hasDerivAt (partial_smooth hf) r).differentiableAt)

/-- Every radial derivative of the actual finite circle average exists, including at radius zero. -/
theorem mean_radial_smooth (q : XiZeroCopy) (x k : ℝ) : ContDiff ℝ ∞ (fun d => mean q d x k) :=
  contDiff_infty.mpr (fun n => average_finite_smooth n (radial_family q x k))

end
end RHTower.D4BMNativeCircle
