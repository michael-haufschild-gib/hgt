import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCharacteristicContact
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceCircleGrowth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Source-derived characteristic remainders of the original theta kernel.

The literal circle mean is even in its radial argument. Compact smoothness of
its averaged source Laplacian and the original characteristic Volterra identity
then give a quadratic remainder after the value and Laplacian contact jet.
Original global theta growth extends this to every nonnegative characteristic
argument with any estimate exponent strictly between sourceGrowthExponent and 2.

The constants here are pointwise in the angular centre. Uniform angular passage,
the full cap integral, and complete left-QNM action extinction are not proved here.
-/

set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped ContDiff
namespace RHTower.D4BMCapReaderRemainder
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMNativeCircle D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse
noncomputable section

private def circleMean (F : Point → ℂ) (d X k : ℝ) : ℂ :=
  average (fun theta => F (logCircle d theta X k))

private theorem circleMean_even (F : Point → ℂ) (X k : ℝ) :
    Function.Even (fun d => circleMean F d X k) := by
  intro d
  have hc (theta : ℝ) : logCircle (-d) theta X k=logCircle d (theta+Real.pi) X k := by
    simp only [logCircle,circle,offset,height,denominator,Real.cosh_neg,Real.sinh_neg,
      Real.sin_add_pi,Real.cos_add_pi,neg_mul,mul_neg,sub_neg_eq_add]
  have hp : Function.Periodic (fun theta => F (logCircle d theta X k)) (2*Real.pi) := by
    intro theta
    apply congrArg F
    simp only [logCircle,circle,offset,height,denominator,Real.sin_add_two_pi,Real.cos_add_two_pi]
  unfold circleMean D4BMNativeCircle.average
  simp_rw [hc]
  congr 1
  rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi),
    ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
  rw [intervalIntegral.integral_comp_add_right (f := fun theta => F (logCircle d theta X k)) Real.pi]
  simpa only [zero_add,add_zero,add_comm] using hp.intervalIntegral_add_eq Real.pi 0

private theorem circleMean_zero (F : Point → ℂ) (X k : ℝ) :
    circleMean F 0 X k=F ![X,Real.exp k] := by
  have hc (theta : ℝ) : logCircle 0 theta X k=![X,Real.exp k] := by
    simp [logCircle,circle,offset,height,denominator]
  unfold circleMean D4BMNativeCircle.average
  simp_rw [hc]
  rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
  simp only [intervalIntegral.integral_const,sub_zero,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

private theorem even_derivative_zero (f : ℝ → ℂ) (hf : Function.Even f) : deriv f 0=0 := by
  have he : (fun x : ℝ => f (-x))=f := funext hf
  have hd := deriv_comp_neg (f := f) (x := (0:ℝ))
  rw [he,neg_zero] at hd
  linear_combination (1/2:ℂ)*hd
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

private theorem laplace_circle_smooth (q : XiZeroCopy) (X k : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      scalarLaplacian (fullSquarePotential q) (logCircle p.1 p.2 X k)) := by
  have hp (p : ℝ × ℝ) : 0 < logCircle p.1 p.2 X k 1 :=
    mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have he : (fun p : ℝ × ℝ => scalarLaplacian (fullSquarePotential q) (logCircle p.1 p.2 X k))=
      fun p => (logCircle p.1 p.2 X k 1:ℂ)^2*
        (coordDeriv 0 (coordDeriv 0 (fullSquarePotential q)) (logCircle p.1 p.2 X k)+
         coordDeriv 1 (coordDeriv 1 (fullSquarePotential q)) (logCircle p.1 p.2 X k)) := by
    funext p
    exact scalarLaplacian_eq _ _ (hp p)
  rw [he]
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hs : ContDiffAt ℝ ∞ (fullSquarePotential q) (logCircle p.1 p.2 X k) :=
    contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q _ (hp p) n)
  have hj (i : Fin 2) : ContDiffAt ℝ ∞ (coordDeriv i (coordDeriv i (fullSquarePotential q)))
      (logCircle p.1 p.2 X k) :=
    coordDeriv_contDiffAt (m := ∞)
      (by simpa using coordDeriv_contDiffAt (m := ∞) (by simpa using hs) i) i
  have hc : ContDiffAt ℝ ∞ (fun r : ℝ × ℝ => logCircle r.1 r.2 X k) p := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
    all_goals fun_prop (disch := exact (denominator_pos _ _).ne')
  have hy : ContDiffAt ℝ ∞ (fun r : ℝ × ℝ => (logCircle r.1 r.2 X k 1:ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiffAt_pi.mp hc 1)
  exact (hy.pow 2).mul (((hj 0).comp p hc).add ((hj 1).comp p hc))


private theorem actionMean_smooth (q : XiZeroCopy) (X k : ℝ) :
    ContDiff ℝ ∞ (fun d => circleMean (scalarLaplacian (fullSquarePotential q)) d X k) :=
  contDiff_infty.mpr (fun n => average_finite_smooth n (laplace_circle_smooth q X k))

private theorem smooth_even_quadratic_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (he : Function.Even f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : Icc (0:ℝ) 2, ‖f d-f 0‖ ≤ C*d.val^2 := by
  have hf1 := (contDiff_infty_iff_deriv.mp hf).2
  have hf2 := (contDiff_infty_iff_deriv.mp hf1).2
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf2.continuous.continuousOn
    (s := Icc (0:ℝ) 2)
  let C := max B 0
  have hc : 0 ≤ C := le_max_right _ _
  have hd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 2) : ‖deriv f t‖ ≤ C*t := by
    have hh := (convex_Icc (0:ℝ) 2).norm_image_sub_le_of_norm_deriv_le
      (fun u _ => hf1.differentiable (by simp) u)
      (fun u hu => (hB u hu).trans (show B ≤ C from le_max_left B 0))
      (show (0:ℝ) ∈ Icc 0 2 by constructor <;> norm_num) ht
    simpa only [even_derivative_zero f he,sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] using hh
  refine ⟨C,hc,fun d => ?_⟩
  have hm := (convex_Icc (0:ℝ) d.val).norm_image_sub_le_of_norm_deriv_le
    (fun u _ => hf.differentiable (by simp) u)
    (fun u (hu : u ∈ Icc (0:ℝ) d.val) => (hd u ⟨hu.1,hu.2.trans d.property.2⟩).trans
      (mul_le_mul_of_nonneg_left hu.2 hc))
    (show (0:ℝ) ∈ Icc 0 d.val from ⟨le_rfl,d.property.1⟩)
    (show d.val ∈ Icc 0 d.val from ⟨d.property.1,le_rfl⟩)
  simpa only [sub_zero,Real.norm_eq_abs,abs_of_nonneg d.property.1,mul_assoc,pow_two] using hm

private theorem arcosh_small_bound (u : Icc (0:ℝ) 1) :
    0 ≤ Real.arcosh (1+u.val) ∧ Real.arcosh (1+u.val) ≤ 2 ∧
      (Real.arcosh (1+u.val))^2 ≤ 3*u.val := by
  have hu : 1 ≤ 1+u.val := le_add_of_nonneg_right u.property.1
  have hd := Real.arcosh_nonneg hu
  have hs := Real.self_le_sinh_iff.mpr hd
  have hh := Real.cosh_sq_sub_sinh_sq (Real.arcosh (1+u.val))
  rw [Real.cosh_arcosh hu] at hh
  have hs0 := Real.sinh_nonneg_iff.mpr hd
  have hsq : (Real.arcosh (1+u.val))^2 ≤ 3*u.val := by
    nlinarith [u.property.1,u.property.2]
  refine ⟨hd,?_,hsq⟩
  nlinarith [u.property.2]

/-- The original averaged theta Laplacian has a linear characteristic remainder. -/
theorem angularAction_small_bound (q : XiZeroCopy) (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Icc (0:ℝ) 1,
      ‖angularAction q (1+u.val) X k-scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]‖ ≤ C*u.val := by
  obtain ⟨B,hB,hb⟩ := smooth_even_quadratic_bound
    (fun d => circleMean (scalarLaplacian (fullSquarePotential q)) d X k)
    (actionMean_smooth q X k) (circleMean_even _ X k)
  refine ⟨3*B,by positivity,fun u => ?_⟩
  obtain ⟨h0,h2,hsq⟩ := arcosh_small_bound u
  have hh := hb (⟨Real.arcosh (1+u.val),h0,h2⟩ : Icc (0:ℝ) 2)
  have he : angularAction q (1+u.val) X k=
      circleMean (scalarLaplacian (fullSquarePotential q)) (Real.arcosh (1+u.val)) X k := by
    exact mean_laplacian_commutes q (Real.arcosh (1+u.val)) X k
  rw [circleMean_zero] at hh
  rw [he]
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hsq hB])


private theorem action_continuousOn (q : XiZeroCopy) (X k : ℝ) :
    ContinuousOn (fun z => angularAction q z X k) (Ici 1) := by
  have he : (fun z => angularAction q z X k)=
      fun z => circleMean (scalarLaplacian (fullSquarePotential q)) (Real.arcosh z) X k :=
    funext (fun z => mean_laplacian_commutes q (Real.arcosh z) X k)
  rw [he]
  exact (actionMean_smooth q X k).continuous.comp_continuousOn Real.continuousOn_arcosh

/-- The actual characteristic derivative has a source-derived Lipschitz remainder. -/
theorem characteristicFirst_small_bound (q : XiZeroCopy) (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Icc (0:ℝ) 1,
      ‖characteristicFirst q (1+u.val) X k-
        scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2‖ ≤ C*u.val := by
  obtain ⟨B,hB,hb⟩ := angularAction_small_bound q X k
  let G := scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]
  refine ⟨B+‖G‖,by positivity,fun u => ?_⟩
  let I := ∫ t in (0:ℝ)..1, angularAction q (1+t*u.val) X k
  have hi : IntervalIntegrable (fun t => angularAction q (1+t*u.val) X k) volume 0 1 := by
    have ht : ContinuousOn (fun t : ℝ => 1+t*u.val) (Icc 0 1) := by fun_prop
    have hc := (action_continuousOn q X k).comp ht (fun t ht => by
      change 1 ≤ 1+t*u.val
      exact le_add_of_nonneg_right (mul_nonneg ht.1 u.property.1))
    exact hc.intervalIntegrable_of_Icc (by norm_num)
  have hn : ‖I-G‖ ≤ B*u.val := by
    have he : I-G = ∫ t in (0:ℝ)..1, (angularAction q (1+t*u.val) X k-G) := by
      rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
      simp only [intervalIntegral.integral_const,sub_zero,one_smul]
      rfl
    rw [he]
    have hm := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => angularAction q (1+t*u.val) X k-G)
      (a := (0:ℝ)) (b := 1) (C := B*u.val) (fun t ht => by
        have ht' : t ∈ Icc (0:ℝ) 1 := by
          rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
          exact ⟨ht.1.le,ht.2⟩
        have htu : t*u.val ∈ Icc (0:ℝ) 1 := ⟨mul_nonneg ht'.1 u.property.1,
          (mul_le_mul_of_nonneg_right ht'.2 u.property.1).trans (by simpa using u.property.2)⟩
        exact (hb ⟨t*u.val,htu⟩).trans (mul_le_mul_of_nonneg_left
          (by nlinarith [u.property.1,ht'.2] : t*u.val ≤ u.val) hB))
    simpa using hm
  have hu : 0 ≤ u.val := u.property.1
  have hp : 0 < 2+u.val := by linarith
  have hc : (2+(u.val:ℂ)) ≠ 0 := by exact_mod_cast hp.ne'
  have he : characteristicFirst q (1+u.val) X k-G/2=
      (I-G-G*(u.val:ℂ)/2)/(2+(u.val:ℂ)) := by
    simp only [characteristicFirst,add_sub_cancel_left,Complex.ofReal_add,Complex.ofReal_one]
    change I/((1+(u.val:ℂ))+1)-G/2=_
    rw [show (1+(u.val:ℂ))+1=2+(u.val:ℂ) by ring]
    field_simp
    ring
  change ‖characteristicFirst q (1+u.val) X k-G/2‖ ≤ _
  rw [he,norm_div]
  have hd : ‖(2+(u.val:ℂ))‖=2+u.val := by
    rw [← Complex.ofReal_ofNat 2,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  rw [hd]
  apply (div_le_iff₀ hp).mpr
  have hm := norm_sub_le (I-G) (G*(u.val:ℂ)/2)
  have hg : ‖G*(u.val:ℂ)/2‖=‖G‖*u.val/2 := by
    simp only [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu,Complex.norm_ofNat]
  rw [hg] at hm
  nlinarith [norm_nonneg G,mul_nonneg hB hu,mul_nonneg (norm_nonneg G) hu,
    mul_nonneg (add_nonneg hB (norm_nonneg G)) (sq_nonneg u.val)]

/-- Quadratic remainder of the original theta circle kernel after its source contact jet. -/
theorem angularKernel_quadratic_remainder (q : XiZeroCopy) (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Icc (0:ℝ) 1,
      ‖angularKernel q (1+u.val) X k-fullSquarePotential q ![X,Real.exp k]-
        (scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*(u.val:ℂ)‖ ≤ C*u.val^2 := by
  obtain ⟨C,hC,hc⟩ := characteristicFirst_small_bound q X k
  refine ⟨C,hC,fun u => ?_⟩
  let G := scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2
  have hu : 1 ≤ 1+u.val := by linarith [u.property.1]
  have hi : IntervalIntegrable (fun r => characteristicFirst q r X k) volume 1 (1+u.val) :=
    ((characteristicFirst_continuousOn q X k).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hu
  have he : angularKernel q (1+u.val) X k-fullSquarePotential q ![X,Real.exp k]-G*(u.val:ℂ)=
      ∫ r in (1:ℝ)..(1+u.val), (characteristicFirst q r X k-G) := by
    rw [angularKernel_source_integral q X k ⟨1+u.val,hu⟩,
      intervalIntegral.integral_sub hi intervalIntegrable_const]
    simp only [add_sub_cancel_left,intervalIntegral.integral_const,Complex.real_smul]
    ring
  change ‖angularKernel q (1+u.val) X k-fullSquarePotential q ![X,Real.exp k]-G*(u.val:ℂ)‖ ≤ _
  rw [he]
  have hm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1:ℝ)) (b := 1+u.val) (C := C*u.val) (fun r hr => by
      rw [uIoc_of_le hu] at hr
      have ht : r-1 ∈ Icc (0:ℝ) 1 := by constructor <;> linarith [hr.1,hr.2,u.property.2]
      have hh := hc ⟨r-1,ht⟩
      simp only [add_sub_cancel] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hr.2] : r-1 ≤ u.val) hC))
  simpa only [add_sub_cancel_left,abs_of_nonneg u.property.1,mul_assoc,pow_two] using hm


private theorem arcosh_large_bound (u : Ici (1:ℝ)) :
    Real.arcosh (1+u.val) ≤ Real.log 4+Real.log u.val := by
  have hu : (1:ℝ) ≤ u.val := u.property
  have hu0 : 0 < u.val := zero_lt_one.trans_le hu
  have hz : 1 ≤ 1+u.val := by linarith
  have hp : 0 ≤ Real.log 4+Real.log u.val :=
    add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg hu)
  have he : Real.exp (Real.log 4+Real.log u.val)=4*u.val := by
    rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4),Real.exp_log hu0]
  have hc : 1+u.val ≤ Real.cosh (Real.log 4+Real.log u.val) := by
    rw [Real.cosh_eq,he]
    linarith [Real.exp_pos (-(Real.log 4+Real.log u.val))]
  have hh := Real.cosh_le_cosh.mp ((Real.cosh_arcosh hz).trans_le hc)
  simpa only [abs_of_nonneg (Real.arcosh_nonneg hz),abs_of_nonneg hp] using hh

/-- A global fractional remainder of the literal theta kernel, with the original source jet.
The exponent is an estimate parameter, not a modified physical frequency. -/
theorem angularKernel_fractional_remainder (q : XiZeroCopy) (X k : ℝ)
    (p : Ioo (sourceGrowthExponent q) 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Ici (0:ℝ),
      ‖angularKernel q (1+u.val) X k-fullSquarePotential q ![X,Real.exp k]-
        (scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)*(u.val:ℂ)‖ ≤ C*u.val^p.val := by
  obtain ⟨B,hB,hb⟩ := angularKernel_quadratic_remainder q X k
  obtain ⟨D,hD,hd⟩ := mean_global_growth q
  let a := sourceGrowthExponent q
  let A := D*Real.exp (a*(Real.log 4+|k|))
  let Q := fullSquarePotential q ![X,Real.exp k]
  let G := scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2
  have ha : 1 ≤ a := (sourceGrowthExponent_bounds q).1
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hp : 1 ≤ p.val := ha.trans p.property.1.le
  have hA : 0 ≤ A := by positivity
  let C := B+A+‖Q‖+‖G‖
  have hC : 0 ≤ C := by positivity
  refine ⟨C,hC,fun u => ?_⟩
  have hu0 : 0 ≤ u.val := u.property
  have hpow0 := Real.rpow_nonneg hu0 p.val
  by_cases hu : u.val ≤ 1
  · have hh := hb ⟨u.val,hu0,hu⟩
    have ht : u.val^2 ≤ u.val^p.val := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_ge' hu0 hu (zero_le_one.trans hp) p.property.2.le
    exact hh.trans ((mul_le_mul_of_nonneg_left ht hB).trans
      (mul_le_mul_of_nonneg_right (show B ≤ C by dsimp [C]; linarith [norm_nonneg Q,norm_nonneg G]) hpow0))
  · have hu1 : 1 ≤ u.val := (lt_of_not_ge hu).le
    have hupos : 0 < u.val := zero_lt_one.trans_le hu1
    have hz : 1 ≤ 1+u.val := by linarith
    have hm : ‖angularKernel q (1+u.val) X k‖ ≤ A*u.val^p.val := by
      apply (hd _ X k (Real.arcosh_nonneg hz)).trans
      calc
        _ ≤ D*Real.exp (a*(Real.log 4+Real.log u.val+|k|)) := by
          apply mul_le_mul_of_nonneg_left _ hD
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left
            (add_le_add (arcosh_large_bound ⟨u.val,hu1⟩) (le_rfl : |k| ≤ |k|)) ha0
        _ = A*u.val^a := by
          rw [Real.rpow_def_of_pos hupos]
          dsimp [A]
          rw [mul_assoc,← Real.exp_add]
          congr 2
          ring
        _ ≤ A*u.val^p.val := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hu1 p.property.1.le) hA
    have h1 := Real.one_le_rpow hu1 (zero_le_one.trans hp)
    have hs := Real.self_le_rpow_of_one_le hu1 hp
    have hQ : ‖Q‖ ≤ ‖Q‖*u.val^p.val := by nlinarith [norm_nonneg Q]
    have hG : ‖G*(u.val:ℂ)‖ ≤ ‖G‖*u.val^p.val := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu0]
      exact mul_le_mul_of_nonneg_left hs (norm_nonneg G)
    apply ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)).trans
    change ‖angularKernel q (1+u.val) X k‖+‖Q‖+‖G*(u.val:ℂ)‖ ≤ _
    have hh := add_le_add (add_le_add hm hQ) hG
    apply hh.trans
    calc
      _ = (A+‖Q‖+‖G‖)*u.val^p.val := by ring
      _ ≤ C*u.val^p.val := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith only [hB]) hpow0

end
end RHTower.D4BMCapReaderRemainder
