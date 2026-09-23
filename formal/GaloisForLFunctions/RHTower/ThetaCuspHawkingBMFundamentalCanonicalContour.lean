import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalJacobiMonodromy
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceClearedPrincipal
import GaloisForLFunctions.HTGeometry.ExponentialTypeZeroDensity

/-!
# Source-defined candidate numerator of the complete fundamental QNM action

The fixed-source logarithmic Jacobi derivative has its exact compact-contour monodromy.
The candidate assembled from scalar, logarithmic, forcing and fixed-onset factors is entire
of finite exponential type. Its actual source residue and positive onset give a nonzero
anchor, hence a linear zero count. Identification with the canonical physical cutoff and
the affine angular counting comparison remain separate obligations. [BRIDGE]
-/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false

private theorem logMoment_base_slit (t : ℝ) :
    2-Complex.exp ((t:ℂ)*I) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hr := Complex.re_le_norm (Complex.exp ((t:ℂ)*I))
  rw [Complex.norm_exp_ofReal_mul_I] at hr
  change 0 < 2-(Complex.exp ((t:ℂ)*I)).re
  linarith

private def jacobiWeightedContour (k : ℝ → ℂ) (n : ℕ) (w s : ℂ) : ℂ :=
  I*∫t in (0:ℝ)..(2*Real.pi), fundamentalJacobiLogKernel n w s ((t:ℂ)*I)*k t

/-- The original tortoise weight on the lifted source contour. -/
def fundamentalJacobiTortoiseWeight (t : ℝ) : ℂ :=
  ((t:ℂ)*I-Complex.log (2-Complex.exp ((t:ℂ)*I)))/2

/-- The compact contour of the logarithmically weighted original source. -/
def fundamentalJacobiTortoiseContour (n : ℕ) (w s : ℂ) : ℂ :=
  jacobiWeightedContour fundamentalJacobiTortoiseWeight n w s

/-- Directional derivative of the original finite part, with the polynomial source
coefficients held fixed. This direction inserts the tortoise factor exactly. -/
def fundamentalJacobiTortoiseMoment (n : ℕ) (w s : ℂ) : ℂ :=
  deriv (fun u : ℂ => fundamentalJacobiMoment n (w+u/2) (s-u/4)) 0

private theorem tortoiseWeight_continuous : Continuous fundamentalJacobiTortoiseWeight := by
  have hl : Continuous (fun t : ℝ => Complex.log (2-Complex.exp ((t:ℂ)*I))) :=
    (show Continuous (fun t : ℝ => 2-Complex.exp ((t:ℂ)*I)) by fun_prop).clog logMoment_base_slit
  exact ((show Continuous (fun t : ℝ => (t:ℂ)*I) by fun_prop).sub hl).div_const 2

private theorem weightedContour_entire (k : ℝ → ℂ) (hk : Continuous k) (n : ℕ) (alpha beta : ℂ) :
    Differentiable ℂ (fun w => jacobiWeightedContour k n w (alpha*w+beta)) := by
  let F : ℝ → ℂ → ℂ := fun t w => fundamentalJacobiLogKernel n w (alpha*w+beta) ((t:ℂ)*I)*k t
  have hc : Continuous (fun p : ℝ × ℂ => F p.1 p.2) := by
    have hb : Continuous (fun p : ℝ × ℂ => 2-Complex.exp ((p.1:ℂ)*I)) := by fun_prop
    have hp : Continuous (fun p : ℝ × ℂ => (2-Complex.exp ((p.1:ℂ)*I))^(2*(alpha*p.2+beta))) :=
      hb.cpow (by fun_prop) (fun p => logMoment_base_slit p.1)
    have he : Continuous (fun p : ℝ × ℂ => Complex.exp ((p.2+1)*((p.1:ℂ)*I))) := by fun_prop
    exact ((he.mul hp).mul (by fun_prop)).mul (hk.comp continuous_fst)
  have hd (t : ℝ) : Differentiable ℂ (F t) := by
    intro w
    have hb : 2-Complex.exp ((t:ℂ)*I) ≠ 0 := Complex.slitPlane_ne_zero (logMoment_base_slit t)
    have hp : DifferentiableAt ℂ (fun w : ℂ => (2-Complex.exp ((t:ℂ)*I))^(2*(alpha*w+beta))) w := by
      exact ((show DifferentiableAt ℂ (fun w : ℂ => 2*(alpha*w+beta)) w by fun_prop).const_cpow
        (Or.inl hb))
    have he : DifferentiableAt ℂ (fun w : ℂ => Complex.exp ((w+1)*((t:ℂ)*I))) w := by fun_prop
    exact ((he.mul hp).mul_const _).mul_const _
  intro w
  have hi := GaloisForLFunctions.HTGeometry.differentiableAt_intervalIntegral_of_holomorphic
    (a := (0:ℝ)) (b := 2*Real.pi) (ρ := |w.im|+1) (ρ' := |w.im|+2)
    (by linarith) hc (fun t => (hd t).differentiableOn)
    (z := w) (by change |w.im| < |w.im|+1;linarith)
  exact hi.const_mul I


private theorem weightedContour_growth (k : ℝ → ℂ) (D : ℝ) (hD : 0 < D)
    (hkb : ∀ t ∈ Icc (0:ℝ) (2*Real.pi), ‖k t‖ ≤ D) (n : ℕ) (alpha beta : ℂ) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧ ∀ w : ℂ,
      ‖jacobiWeightedContour k n w (alpha*w+beta)‖ ≤ C*Real.exp (A*‖w‖) := by
  have hc : Continuous (fun t : ℝ => Complex.log (2-Complex.exp ((t:ℂ)*I))) :=
    (show Continuous (fun t : ℝ => 2-Complex.exp ((t:ℂ)*I)) by fun_prop).clog
      logMoment_base_slit
  obtain ⟨L0,hL0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.continuousOn : ContinuousOn _ (Icc (0:ℝ) (2*Real.pi)))
  let L : ℝ := max L0 0
  have hL : 0 ≤ L := le_max_right _ _
  have hLb (t : ℝ) (ht : t ∈ Icc (0:ℝ) (2*Real.pi)) :
      ‖Complex.log (2-Complex.exp ((t:ℂ)*I))‖ ≤ L := (hL0 t ht).trans (le_max_left _ _)
  let A : ℝ := 2*Real.pi+2*L*‖alpha‖
  let C : ℝ := D*(2*Real.pi*2^n*Real.exp (2*L*‖beta‖))
  refine ⟨A,C,by dsimp [A];positivity,by dsimp [C];positivity,?_⟩
  intro w
  have hp (t : ℝ) (ht : t ∈ Icc (0:ℝ) (2*Real.pi)) :
      ‖(2-Complex.exp ((t:ℂ)*I))^(2*(alpha*w+beta))‖ ≤
        Real.exp ((2*L*‖alpha‖)*‖w‖+2*L*‖beta‖) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero (logMoment_base_slit t)),
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
  have hfk (t : ℝ) (ht : t ∈ Icc (0:ℝ) (2*Real.pi)) :
      ‖fundamentalJacobiLogKernel n w (alpha*w+beta) ((t:ℂ)*I)*k t‖ ≤
        (2^n*Real.exp (2*L*‖beta‖)*Real.exp (A*‖w‖))*D := by
    rw [norm_mul]
    exact mul_le_mul (hf t ht) (hkb t ht) (norm_nonneg _) (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 2*Real.pi)
    (f := fun t => fundamentalJacobiLogKernel n w (alpha*w+beta) ((t:ℂ)*I)*k t)
    (C := (2^n*Real.exp (2*L*‖beta‖)*Real.exp (A*‖w‖))*D) (fun t ht => by
      rw [uIoc_of_le (by positivity : (0:ℝ)≤2*Real.pi)] at ht
      exact hfk t ⟨ht.1.le,ht.2⟩)
  rw [sub_zero,abs_of_pos (by positivity : (0:ℝ)<2*Real.pi)] at hi
  rw [jacobiWeightedContour,norm_mul,Complex.norm_I,one_mul]
  calc
    _ ≤ ((2^n*Real.exp (2*L*‖beta‖)*Real.exp (A*‖w‖))*D)*(2*Real.pi) := hi
    _ = C*Real.exp (A*‖w‖) := by dsimp [C];ring

/-- The actual logarithmic source contour is entire on every affine physical curve. -/
theorem fundamentalJacobiTortoiseContour_affine_entire (n : ℕ) (alpha beta : ℂ) :
    Differentiable ℂ (fun w => fundamentalJacobiTortoiseContour n w (alpha*w+beta)) :=
  weightedContour_entire _ tortoiseWeight_continuous n alpha beta

/-- The actual logarithmic source contour has finite exponential type on each affine curve. -/
theorem fundamentalJacobiTortoiseContour_affine_growth (n : ℕ) (alpha beta : ℂ) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧ ∀ w : ℂ,
      ‖fundamentalJacobiTortoiseContour n w (alpha*w+beta)‖ ≤ C*Real.exp (A*‖w‖) := by
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (tortoiseWeight_continuous.continuousOn :
      ContinuousOn fundamentalJacobiTortoiseWeight (Icc (0:ℝ) (2*Real.pi)))
  exact weightedContour_growth _ (max D 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    (fun t ht => (hD t ht).trans (le_max_left _ _)) n alpha beta

/-- The source-fixed parameter direction differentiates to the original tortoise weight. -/
theorem fundamentalJacobiLogKernel_tortoise_hasDerivAt (n : ℕ) (w s : ℂ) (t : ℝ) (v : ℂ) :
    HasDerivAt (fun u : ℂ => fundamentalJacobiLogKernel n (w+u/2) (s-u/4) ((t:ℂ)*I))
      (fundamentalJacobiLogKernel n (w+v/2) (s-v/4) ((t:ℂ)*I)*fundamentalJacobiTortoiseWeight t) v := by
  have he0 := ((((hasDerivAt_id v).div_const (2:ℂ)).const_add w).add_const 1).mul_const ((t:ℂ)*I)
  have he := he0.cexp
  have hp0 := (((hasDerivAt_id v).div_const (4:ℂ)).const_sub s).const_mul (2:ℂ)
  have hp := hp0.const_cpow (c := 2-Complex.exp ((t:ℂ)*I))
    (Or.inl (Complex.slitPlane_ne_zero (logMoment_base_slit t)))
  apply ((he.mul hp).mul_const ((1-Complex.exp ((t:ℂ)*I))^n)).congr_deriv
  dsimp only [fundamentalJacobiLogKernel,fundamentalJacobiTortoiseWeight,id_eq]
  ring

/-- Differentiation of the actual compact source contour retains the fixed-source logarithm. -/
theorem fundamentalJacobiContour_tortoise_hasDerivAt (n : ℕ) (w s : ℂ) :
    HasDerivAt (fun u : ℂ => fundamentalJacobiContour n (w+u/2) (s-u/4))
      (fundamentalJacobiTortoiseContour n w s) 0 := by
  let F : ℝ → ℂ → ℂ := fun t u => fundamentalJacobiLogKernel n (w+u/2) (s-u/4) ((t:ℂ)*I)
  have hc : Continuous (fun p : ℝ × ℂ => F p.1 p.2) := by
    have hb : Continuous (fun p : ℝ × ℂ => 2-Complex.exp ((p.1:ℂ)*I)) := by fun_prop
    have hp : Continuous (fun p : ℝ × ℂ => (2-Complex.exp ((p.1:ℂ)*I))^(2*(s-p.2/4))) :=
      hb.cpow (by fun_prop) (fun p => logMoment_base_slit p.1)
    have he : Continuous (fun p : ℝ × ℂ => Complex.exp ((w+p.2/2+1)*((p.1:ℂ)*I))) := by fun_prop
    exact (he.mul hp).mul (by fun_prop)
  have hd (t : ℝ) (u : ℂ) := fundamentalJacobiLogKernel_tortoise_hasDerivAt n w s t u
  have hi := GaloisForLFunctions.HTGeometry.hasDerivAt_intervalIntegral_of_holomorphic
    (a := (0:ℝ)) (b := 2*Real.pi) (ρ := 1) (ρ' := 2) (by norm_num) hc
    (fun t u _ => (hd t u).differentiableAt.differentiableWithinAt)
    (z := (0:ℂ)) (by norm_num [GaloisForLFunctions.HTGeometry.imStrip])
  have hv (t : ℝ) : deriv (F t) 0 =
      fundamentalJacobiLogKernel n w s ((t:ℂ)*I)*fundamentalJacobiTortoiseWeight t := by
    simpa only [zero_div,add_zero,sub_zero] using (hd t 0).deriv
  apply (hi.const_mul I).congr_deriv
  simp_rw [hv]
  rfl

/-- The exact monodromy correction for the derivative of the original source finite part.
It keeps both source parameters independent before the physical specialization. -/
theorem fundamentalJacobiTortoiseMoment_monodromy (n : ℕ) (w s : ℂ)
    (hw : -2 < w.re) (hw1 : w+1 ≠ 0)
    (hE : Complex.exp (2*Real.pi*I*w)-1 ≠ 0) :
    (Complex.exp (2*Real.pi*I*w)-1)^(2 : ℕ)*fundamentalJacobiTortoiseMoment n w s =
      (Complex.exp (2*Real.pi*I*w)-1)*fundamentalJacobiTortoiseContour n w s-
        Real.pi*I*Complex.exp (2*Real.pi*I*w)*fundamentalJacobiContour n w s := by
  let E : ℂ → ℂ := fun u => Complex.exp (2*Real.pi*I*(w+u/2))-1
  have hEd : HasDerivAt E (Real.pi*I*Complex.exp (2*Real.pi*I*w)) 0 := by
    have h := (((((hasDerivAt_id (0:ℂ)).div_const (2:ℂ)).const_add w).const_mul
      (2*Real.pi*I)).cexp).sub_const 1
    apply h.congr_deriv
    dsimp only [id_eq]
    ring
  have hE0 : E 0 ≠ 0 := by simpa only [E,zero_div,add_zero] using hE
  have hr : ∀ᶠ u : ℂ in 𝓝 0, -2 < (w+u/2).re :=
    (isOpen_lt continuous_const (by fun_prop : Continuous (fun u : ℂ => (w+u/2).re))).mem_nhds
      (by simpa only [mem_setOf_eq,zero_div,add_zero] using hw)
  have h1 : ∀ᶠ u : ℂ in 𝓝 0, w+u/2+1 ≠ 0 :=
    (show ContinuousAt (fun u : ℂ => w+u/2+1) 0 by fun_prop).eventually_ne
      (by simpa only [zero_div,add_zero] using hw1)
  have he := hEd.continuousAt.eventually_ne hE0
  have heq : (fun u : ℂ => fundamentalJacobiMoment n (w+u/2) (s-u/4)) =ᶠ[𝓝 0]
      (fun u => fundamentalJacobiContour n (w+u/2) (s-u/4)/E u) := by
    filter_upwards [hr,h1,he] with u hu hu1 huE
    apply (eq_div_iff huE).mpr
    rw [fundamentalJacobiContour_eq_moment n (w+u/2) (s-u/4) hu hu1]
    dsimp only [E]
    ring
  have hd := ((fundamentalJacobiContour_tortoise_hasDerivAt n w s).div hEd hE0).congr_of_eventuallyEq heq
  rw [fundamentalJacobiTortoiseMoment,hd.deriv]
  simp only [E,zero_div,add_zero,sub_zero]
  field_simp [hE]

/-- The first original Mellin pole has its exact source residue on the compact contour. -/
theorem fundamentalJacobiContour_neg_one (n : ℕ) (s : ℂ) :
    fundamentalJacobiContour n (-1) s=2*Real.pi*I*(2:ℂ)^(2*s) := by
  have hperiod : Complex.exp (2*Real.pi*I*(-1))=1 := by
    rw [show (2*Real.pi*I*(-1):ℂ)=-(2*Real.pi*I) by ring,
      Complex.exp_neg,Complex.exp_two_pi_mul_I,inv_one]
  have heq : fundamentalJacobiCircleRemainder n (-1) s =ᶠ[𝓝[>] (0:ℝ)]
      (fun _ => fundamentalJacobiContour n (-1) s-2*Real.pi*I*(2:ℂ)^(2*s)) := by
    have he1 : ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < 1 := Iio_mem_nhds (by norm_num)
    filter_upwards [self_mem_nhdsWithin,he1.filter_mono nhdsWithin_le_nhds] with e he he1
    have hcore : Continuous (fun t : ℝ =>
        fundamentalJacobiComplexCore n s ((e:ℂ)*Complex.exp ((t:ℂ)*I))) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      have hn : ‖(e:ℂ)*Complex.exp ((t:ℂ)*I)‖=e := by
        rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg he.le]
      have hr := Complex.re_le_norm ((e:ℂ)*Complex.exp ((t:ℂ)*I))
      rw [hn] at hr
      exact (fundamentalJacobiComplexCore_hasDerivAt n s (by linarith :
        ((e:ℂ)*Complex.exp ((t:ℂ)*I)).re < 2)).continuousAt.comp
        (f := fun t : ℝ => (e:ℂ)*Complex.exp ((t:ℂ)*I)) (by fun_prop)
    have hexp : Complex.exp (Real.log e:ℂ)=(e:ℂ) := by
      rw [Complex.ofReal_log he.le,Complex.exp_log (Complex.ofReal_ne_zero.mpr he.ne')]
    have hcut := fundamentalJacobiContour_cutoff n (-1) s he he1.le
    rw [hperiod] at hcut
    simp only [sub_self,zero_mul] at hcut
    have hk (t : ℝ) : fundamentalJacobiLogKernel n (-1) s ((Real.log e:ℂ)+(t:ℂ)*I)=
        fundamentalJacobiComplexCore n s ((e:ℂ)*Complex.exp ((t:ℂ)*I)) := by
      simp only [fundamentalJacobiLogKernel,neg_add_cancel,zero_mul,Complex.exp_zero,one_mul,
        Complex.exp_add,hexp,fundamentalJacobiComplexCore]
    simp_rw [hk] at hcut
    simp only [fundamentalJacobiCircleRemainder,neg_add_cancel,Complex.cpow_zero,zero_mul,
      Complex.exp_zero,one_mul]
    rw [intervalIntegral.integral_sub (hcore.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [sub_zero,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat]
    linear_combination hcut
  have hz := fundamentalJacobiCircleRemainder_tendsto_zero n (-1) s (by norm_num)
  have hc := hz.congr' heq
  have h := tendsto_nhds_unique hc (tendsto_const_nhds (x :=
    fundamentalJacobiContour n (-1) s-2*Real.pi*I*(2:ℂ)^(2*s)))
  exact sub_eq_zero.mp h.symm

open D4BMModularCore

/-- The original compact onset correction depends only on the independent source gap. -/
theorem onsetCorrection_source_gap (s w : ℂ) :
    onsetCorrection (2*s) w=onsetCorrection 0 (w-2*s) := by
  unfold onsetCorrection
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t _
  rw [show (2*s-w)=0-(w-2*s) by ring]

/-- Clearing retains the actual fixed-onset transform, with its source rate held fixed. -/
theorem clearedOnset_source_gap (s w : ℂ) (hgap : w-2*s ≠ 0) :
    clearedOnset 0 (w-2*s)=(w-2*s)*continuedOnset s w := by
  rw [clearedOnset,continuedOnset]
  simp only [mul_zero,sub_zero]
  rw [onsetCorrection_source_gap s w]
  field_simp [hgap]

/-- The cleared frequency derivative differentiates the gap at fixed source rate. -/
theorem clearedOnset_source_gap_derivative (s w : ℂ) (hgap : w-2*s ≠ 0) :
    (w-2*s)^(2 : ℕ)*deriv (continuedOnset s) w=
      (w-2*s)*deriv (clearedOnset 0) (w-2*s)-clearedOnset 0 (w-2*s) := by
  have hF := ((clearedOnset_entire 0) (w-2*s)).hasDerivAt.comp w
    ((hasDerivAt_id w).sub_const (2*s))
  have hg := (hasDerivAt_id w).sub_const (2*s)
  have he : continuedOnset s =ᶠ[𝓝 w]
      (fun u => clearedOnset 0 (u-2*s)/(u-2*s)) := by
    filter_upwards [hg.continuousAt.eventually_ne hgap] with u hu
    exact (eq_div_iff hu).mpr (((clearedOnset_source_gap s u hu).trans (mul_comm _ _)).symm)
  have hd := (hF.div hg hgap).congr_of_eventuallyEq he
  rw [hd.deriv]
  simp only [Function.comp_apply,mul_one,id_eq]
  field_simp [hgap]

/-- The complete scalar Jacobi source, including its degree-four coefficient. -/
def fundamentalSourceContour (w s a : ℂ) : ℂ :=
  2*a^(2 : ℕ)*(fundamentalMomentConstant s*fundamentalJacobiContour 2 w s+
    fundamentalMomentQuadratic w s*fundamentalJacobiContour 4 w s)

/-- The logarithmic source contour keeps the polynomial coefficients fixed. -/
def fundamentalSourceTortoiseContour (w s a : ℂ) : ℂ :=
  2*a^(2 : ℕ)*(fundamentalMomentConstant s*fundamentalJacobiTortoiseContour 2 w s+
    fundamentalMomentQuadratic w s*fundamentalJacobiTortoiseContour 4 w s)

/-- The forcing combination after boundary-preserving integration by parts. -/
def fundamentalJacobiForcingContour (n : ℕ) (w s : ℂ) : ℂ :=
  (n:ℂ)*fundamentalJacobiContour (n-1) w (s-1/2)+
    (2*s-1)*fundamentalJacobiContour n w (s-1)

def fundamentalSourceForcingContour (w s a : ℂ) : ℂ :=
  2*a^(2 : ℕ)*(fundamentalMomentConstant s*fundamentalJacobiForcingContour 2 w s+
    fundamentalMomentQuadratic w s*fundamentalJacobiForcingContour 4 w s)

/-- The candidate numerator of the complete unit-source action on the true/true
physical parameter curve. Its identification with the canonical cutoff is a separate obligation. -/
def fundamentalCanonicalContourNumerator (w : ℂ) : ℂ :=
  let s := -2*w-4
  let gap := 5*w+8
  let mu := (w+1)*(w+2)
  let E := Complex.exp (2*Real.pi*I*w)-1
  let F := clearedOnset 0 gap
  let D := gap*deriv (clearedOnset 0) gap-F
  (mu-2)*(D*E*fundamentalSourceContour w s 1+
    gap*F*(E*fundamentalSourceTortoiseContour w s 1-
      Real.pi*I*Complex.exp (2*Real.pi*I*w)*fundamentalSourceContour w s 1))+
    gap*F*E*fundamentalSourceForcingContour w s 1

/-- Exact source residue at the auxiliary nonzero anchor. -/
theorem fundamentalSourceContour_neg_one :
    fundamentalSourceContour (-1) (-2) 1=-3*Real.pi*I/8 := by
  rw [fundamentalSourceContour,fundamentalJacobiContour_neg_one,fundamentalJacobiContour_neg_one]
  norm_num [fundamentalMomentConstant,fundamentalMomentQuadratic,Complex.cpow_neg,Complex.cpow_ofNat]
  ring

/-- The full candidate numerator has a nonzero anchor determined by the actual source and onset.
The onset derivative and forcing terms are retained in the numerator definition. -/
theorem fundamentalCanonicalContourNumerator_neg_one :
    fundamentalCanonicalContourNumerator (-1)=27*(Real.pi:ℂ)^(2 : ℕ)/4*continuedOnset (-2) (-1) := by
  have hp : Complex.exp (2*Real.pi*I*(-1))=1 := by
    rw [show (2*Real.pi*I*(-1):ℂ)=-(2*Real.pi*I) by ring,
      Complex.exp_neg,Complex.exp_two_pi_mul_I,inv_one]
  have hF := clearedOnset_source_gap (-2) (-1) (by norm_num)
  norm_num only at hF
  dsimp only [fundamentalCanonicalContourNumerator]
  norm_num only
  rw [hp]
  simp only [sub_self,mul_zero,zero_mul,zero_add,zero_sub,add_zero]
  rw [fundamentalSourceContour_neg_one,hF]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Positivity at the anchor comes from the original nonnegative onset, whose plateau has positive measure. -/
theorem continuedOnset_anchor_re_pos : 0 < (continuedOnset (-2) (-1)).re := by
  let f : ℝ → ℝ := fun u => Real.smoothTransition u*Real.exp (-3*u)
  have hi := onsetTransform_integrable (-4) (-1) (by norm_num)
  have hf (u : ℝ) : ((Real.smoothTransition u:ℂ)*Complex.exp (((-4:ℂ)-(-1))*(u:ℂ))).re=f u := by
    norm_num [f,Complex.exp_re]
  have hri : IntegrableOn f (Ioi (0:ℝ)) := by
    change Integrable f (volume.restrict (Ioi (0:ℝ)))
    convert hi.re using 1
    funext u
    exact (hf u).symm
  have ht : (continuedOnset (-2) (-1)).re=∫u in Ioi (0:ℝ), f u := by
    have ho := onsetTransform_eq (-4) (-1) (by norm_num)
    have hv : continuedOnset (-2) (-1)=onsetTransform (-4) (-1) := by
      rw [ho,continuedOnset]
      norm_num
    rw [hv,onsetTransform]
    have hh := integral_re hi
    simp only [RCLike.re_eq_complex_re,hf] at hh
    exact hh.symm
  rw [ht]
  apply (integral_pos_iff_support_of_nonneg
    (fun u => mul_nonneg (Real.smoothTransition.nonneg u) (Real.exp_pos _).le) hri).mpr
  have hs : Ioo (1:ℝ) 2 ⊆ Function.support f := by
    intro u hu
    change f u ≠ 0
    dsimp only [f]
    rw [Real.smoothTransition.one_of_one_le hu.1.le,one_mul]
    exact Real.exp_ne_zero _
  have hm : 0 < (volume.restrict (Ioi (0:ℝ))) (Ioo (1:ℝ) 2) := by
    rw [Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr (show Ioo (1:ℝ) 2 ⊆ Ioi 0 from fun u hu => by change 0<u;linarith [hu.1])]
    norm_num
  exact hm.trans_le (measure_mono hs)

/-- The proposed complete numerator is not identically zero; no observed zero or numerical input is used. -/
theorem fundamentalCanonicalContourNumerator_anchor_ne_zero :
    fundamentalCanonicalContourNumerator (-1) ≠ 0 := by
  rw [fundamentalCanonicalContourNumerator_neg_one]
  apply mul_ne_zero
  · apply div_ne_zero
    · exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
    · norm_num
  · intro h
    have hp := continuedOnset_anchor_re_pos
    rw [h] at hp
    exact (lt_irrefl (0:ℝ)) hp

private def sourceExpBound (f : ℂ → ℂ) : Prop :=
  ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧ ∀ w : ℂ, ‖f w‖ ≤ C*Real.exp (A*‖w‖)

private theorem sourceExpBound_const (c : ℂ) : sourceExpBound (fun _ => c) := by
  refine ⟨0,‖c‖+1,le_rfl,by positivity,?_⟩
  intro w
  simp only [zero_mul,Real.exp_zero,mul_one]
  linarith

private theorem sourceExpBound_id : sourceExpBound (fun w : ℂ => w) := by
  refine ⟨1,1,by norm_num,by norm_num,?_⟩
  intro w
  simp only [one_mul]
  have h := Real.add_one_le_exp ‖w‖
  linarith

private theorem sourceExpBound_add {f g : ℂ → ℂ} (hf : sourceExpBound f) (hg : sourceExpBound g) :
    sourceExpBound (fun w => f w+g w) := by
  obtain ⟨A,C,hA,hC,hf⟩ := hf
  obtain ⟨B,D,hB,hD,hg⟩ := hg
  refine ⟨max A B,C+D,le_trans hA (le_max_left _ _),add_pos hC hD,?_⟩
  intro w
  calc
    _ ≤ ‖f w‖+‖g w‖ := norm_add_le _ _
    _ ≤ C*Real.exp (A*‖w‖)+D*Real.exp (B*‖w‖) := add_le_add (hf w) (hg w)
    _ ≤ C*Real.exp (max A B*‖w‖)+D*Real.exp (max A B*‖w‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (le_max_left A B) (norm_nonneg w))) hC.le
      · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (le_max_right A B) (norm_nonneg w))) hD.le
    _ = _ := by ring

private theorem sourceExpBound_mul {f g : ℂ → ℂ} (hf : sourceExpBound f) (hg : sourceExpBound g) :
    sourceExpBound (fun w => f w*g w) := by
  obtain ⟨A,C,hA,hC,hf⟩ := hf
  obtain ⟨B,D,hB,hD,hg⟩ := hg
  refine ⟨A+B,C*D,add_nonneg hA hB,mul_pos hC hD,?_⟩
  intro w
  rw [norm_mul]
  calc
    _ ≤ (C*Real.exp (A*‖w‖))*(D*Real.exp (B*‖w‖)) :=
      mul_le_mul (hf w) (hg w) (norm_nonneg _) (by positivity)
    _ = C*D*Real.exp ((A+B)*‖w‖) := by rw [add_mul,Real.exp_add];ring

private theorem sourceExpBound_sub {f g : ℂ → ℂ} (hf : sourceExpBound f) (hg : sourceExpBound g) :
    sourceExpBound (fun w => f w-g w) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using
    sourceExpBound_add hf (sourceExpBound_mul (sourceExpBound_const (-1)) hg)

private theorem sourceExpBound_affine {f : ℂ → ℂ} (hf : sourceExpBound f) (a b : ℂ) :
    sourceExpBound (fun w => f (a*w+b)) := by
  obtain ⟨A,C,hA,hC,hf⟩ := hf
  refine ⟨A*‖a‖,C*Real.exp (A*‖b‖),mul_nonneg hA (norm_nonneg _),by positivity,?_⟩
  intro w
  calc
    _ ≤ C*Real.exp (A*‖a*w+b‖) := hf _
    _ ≤ C*Real.exp (A*(‖a‖*‖w‖+‖b‖)) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hA
      simpa only [norm_mul] using norm_add_le (a*w) b
    _ = _ := by rw [mul_add,Real.exp_add];ring

private theorem sourceExpBound_deriv {f : ℂ → ℂ} (hd : Differentiable ℂ f) (hf : sourceExpBound f) :
    sourceExpBound (deriv f) := by
  obtain ⟨A,C,hA,hC,hf⟩ := hf
  refine ⟨A,C*Real.exp A,hA,by positivity,?_⟩
  intro w
  have hb : ∀ z ∈ Metric.sphere w 1, ‖f z‖ ≤ C*Real.exp (A*(‖w‖+1)) := by
    intro z hz
    have hr : ‖z-w‖=1 := by simpa only [Metric.mem_sphere,dist_eq_norm] using hz
    have hn : ‖z‖ ≤ ‖w‖+1 := by
      have h := norm_add_le (z-w) w
      rw [sub_add_cancel,hr] at h
      linarith
    exact (hf z).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hA)) hC.le)
  have hdc : DiffContOnCl ℂ f (Metric.ball w 1) :=
    ⟨hd.differentiableOn,hd.continuous.continuousOn⟩
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ)<1) hdc hb
  rw [div_one,mul_add,mul_one,Real.exp_add] at h
  calc
    _ ≤ C*(Real.exp (A*‖w‖)*Real.exp A) := h
    _ = _ := by ring

private theorem sourceExpBound_onsetCorrection : sourceExpBound (onsetCorrection 0) := by
  refine ⟨1,1,by norm_num,by norm_num,?_⟩
  intro w
  have hb (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) :
      ‖((Real.smoothTransition t:ℂ)-1)*Complex.exp ((0-w)*(t:ℂ))‖ ≤ Real.exp ‖w‖ := by
    have hc : ‖(Real.smoothTransition t:ℂ)-1‖ ≤ 1 := by
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (Real.smoothTransition.le_one t))]
      linarith [Real.smoothTransition.nonneg t]
    have he : ‖Complex.exp ((0-w)*(t:ℂ))‖ ≤ Real.exp ‖w‖ := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have h := Complex.re_le_norm ((0-w)*(t:ℂ))
      simp only [zero_sub,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos ht.1] at h
      simpa only [zero_sub] using h.trans (mul_le_of_le_one_right (norm_nonneg w) ht.2)
    rw [norm_mul]
    exact (mul_le_mul hc he (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  unfold onsetCorrection
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := Real.exp ‖w‖)
    (f := fun t => ((Real.smoothTransition t:ℂ)-1)*Complex.exp ((0-w)*(t:ℂ)))
    (fun t ht => hb t (by simpa only [uIoc_of_le zero_le_one] using ht))
  simpa only [sub_zero,abs_one,mul_one,one_mul] using h

private theorem sourceExpBound_clearedOnset : sourceExpBound (clearedOnset 0) := by
  simpa only [sourceExpBound,clearedOnset,mul_zero,sub_zero] using
    sourceExpBound_add (sourceExpBound_const 1) (sourceExpBound_mul sourceExpBound_id sourceExpBound_onsetCorrection)

private theorem sourceExpBound_exp : sourceExpBound Complex.exp := by
  refine ⟨1,1,by norm_num,by norm_num,?_⟩
  intro w
  simpa only [Complex.norm_exp,one_mul] using Real.exp_le_exp.mpr (Complex.re_le_norm w)

/-- The candidate for the complete source action has an entire numerator on its physical curve. -/
theorem fundamentalCanonicalContourNumerator_entire :
    Differentiable ℂ fundamentalCanonicalContourNumerator := by
  let S : ℂ → ℂ := fun w => -2*w-4
  have hJ (n : ℕ) (c : ℂ) :
      Differentiable ℂ (fun w => fundamentalJacobiContour n w (S w-c)) := by
    simpa only [S,sub_eq_add_neg,add_assoc] using
      fundamentalJacobiContour_affine_entire n (-2) (-4-c)
  have hX (n : ℕ) : Differentiable ℂ (fun w => fundamentalJacobiTortoiseContour n w (S w)) := by
    simpa only [S,sub_eq_add_neg] using fundamentalJacobiTortoiseContour_affine_entire n (-2) (-4)
  have hS : Differentiable ℂ S := by fun_prop
  have hA : Differentiable ℂ (fun w => fundamentalMomentConstant (S w)) := by
    unfold fundamentalMomentConstant
    fun_prop
  have hB : Differentiable ℂ (fun w => fundamentalMomentQuadratic w (S w)) := by
    unfold fundamentalMomentQuadratic
    fun_prop
  have hM : Differentiable ℂ (fun w => fundamentalSourceContour w (S w) 1) := by
    have h2 := hJ 2 0
    have h4 := hJ 4 0
    simp only [sub_zero] at h2 h4
    exact (((hA.mul h2).add (hB.mul h4))).const_mul (2*(1:ℂ)^(2 : ℕ))
  have hMX : Differentiable ℂ (fun w => fundamentalSourceTortoiseContour w (S w) 1) := by
    have h2 := hX 2
    have h4 := hX 4
    exact (((hA.mul h2).add (hB.mul h4))).const_mul (2*(1:ℂ)^(2 : ℕ))
  have hY (n : ℕ) : Differentiable ℂ (fun w => fundamentalJacobiForcingContour n w (S w)) := by
    have h1 := hJ (n-1) (1/2)
    have h2 := hJ n 1
    exact (h1.const_mul (n:ℂ)).add (((hS.const_mul 2).sub_const 1).mul h2)
  have hMY : Differentiable ℂ (fun w => fundamentalSourceForcingContour w (S w) 1) := by
    have h2 := hY 2
    have h4 := hY 4
    exact (((hA.mul h2).add (hB.mul h4))).const_mul (2*(1:ℂ)^(2 : ℕ))
  have hF := clearedOnset_entire 0
  have hD := hF.deriv
  have hg : Differentiable ℂ (fun w : ℂ => 5*w+8) := (differentiable_id.const_mul 5).add_const 8
  have hFc := hF.comp hg
  have hDc := hD.comp hg
  have hmu : Differentiable ℂ (fun w : ℂ => (w+1)*(w+2)) :=
    (differentiable_id.add_const (1:ℂ)).mul (differentiable_id.add_const (2:ℂ))
  have hR : Differentiable ℂ (fun w : ℂ => Complex.exp (2*Real.pi*I*w)) :=
    (differentiable_id.const_mul (2*Real.pi*I:ℂ)).cexp
  have hE := hR.sub_const 1
  have hDg := (hg.mul hDc).sub hFc
  exact ((hmu.sub_const 2).mul
    (((hDg.mul hE).mul hM).add
      ((hg.mul hFc).mul ((hE.mul hMX).sub ((hR.const_mul (Real.pi*I)).mul hM))))).add
    (((hg.mul hFc).mul hE).mul hMY)

/-- All temporal, logarithmic and forcing summands of the candidate numerator jointly have
finite exponential type. No growth assumption is supplied for any source factor. -/
theorem fundamentalCanonicalContourNumerator_growth :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧ ∀ w : ℂ,
      ‖fundamentalCanonicalContourNumerator w‖ ≤ C*Real.exp (A*‖w‖) := by
  let S : ℂ → ℂ := fun w => -2*w-4
  have hC := sourceExpBound_const
  have hid := sourceExpBound_id
  have hS : sourceExpBound S :=
    sourceExpBound_sub (sourceExpBound_mul (hC (-2)) hid) (hC 4)
  have hmu : sourceExpBound (fun w : ℂ => (w+1)*(w+2)) :=
    sourceExpBound_mul (sourceExpBound_add hid (hC 1)) (sourceExpBound_add hid (hC 2))
  have hA : sourceExpBound (fun w => fundamentalMomentConstant (S w)) := by
    simpa only [fundamentalMomentConstant,pow_two,div_eq_mul_inv] using
      sourceExpBound_mul (sourceExpBound_add (sourceExpBound_add
        (sourceExpBound_mul (hC 5) (sourceExpBound_mul hS hS))
        (sourceExpBound_mul (hC 15) hS)) (hC 4)) (hC (4:ℂ)⁻¹)
  have hB : sourceExpBound (fun w => fundamentalMomentQuadratic w (S w)) := by
    simpa only [fundamentalMomentQuadratic,div_eq_mul_inv] using
      sourceExpBound_mul (sourceExpBound_mul
        (sourceExpBound_mul hS (sourceExpBound_sub hS (hC 1)))
        (sourceExpBound_sub
          (sourceExpBound_mul (sourceExpBound_add hS (hC 2))
            (sourceExpBound_add (sourceExpBound_mul (hC 2) hS) (hC 3)))
          (sourceExpBound_mul hmu (hC (2:ℂ)⁻¹)))) (hC (4:ℂ)⁻¹)
  have hJ (n : ℕ) (c : ℂ) : sourceExpBound (fun w => fundamentalJacobiContour n w (S w-c)) := by
    simpa only [sourceExpBound,S,sub_eq_add_neg,add_assoc] using
      fundamentalJacobiContour_affine_growth n (-2) (-4-c)
  have hJ0 (n : ℕ) : sourceExpBound (fun w => fundamentalJacobiContour n w (S w)) := by
    simpa only [sub_zero] using hJ n 0
  have hX (n : ℕ) : sourceExpBound (fun w => fundamentalJacobiTortoiseContour n w (S w)) := by
    simpa only [sourceExpBound,S,sub_eq_add_neg] using fundamentalJacobiTortoiseContour_affine_growth n (-2) (-4)
  have hM : sourceExpBound (fun w => fundamentalSourceContour w (S w) 1) := by
    simpa only [fundamentalSourceContour,one_pow,mul_one] using
      sourceExpBound_mul (hC 2) (sourceExpBound_add (sourceExpBound_mul hA (hJ0 2))
        (sourceExpBound_mul hB (hJ0 4)))
  have hMX : sourceExpBound (fun w => fundamentalSourceTortoiseContour w (S w) 1) := by
    simpa only [fundamentalSourceTortoiseContour,one_pow,mul_one] using
      sourceExpBound_mul (hC 2) (sourceExpBound_add (sourceExpBound_mul hA (hX 2))
        (sourceExpBound_mul hB (hX 4)))
  have hY (n : ℕ) : sourceExpBound (fun w => fundamentalJacobiForcingContour n w (S w)) :=
    sourceExpBound_add (sourceExpBound_mul (hC (n:ℂ)) (hJ (n-1) (1/2)))
      (sourceExpBound_mul (sourceExpBound_sub (sourceExpBound_mul (hC 2) hS) (hC 1)) (hJ n 1))
  have hMY : sourceExpBound (fun w => fundamentalSourceForcingContour w (S w) 1) := by
    simpa only [fundamentalSourceForcingContour,one_pow,mul_one] using
      sourceExpBound_mul (hC 2) (sourceExpBound_add (sourceExpBound_mul hA (hY 2))
        (sourceExpBound_mul hB (hY 4)))
  have hg : sourceExpBound (fun w : ℂ => 5*w+8) :=
    sourceExpBound_add (sourceExpBound_mul (hC 5) hid) (hC 8)
  have hF := sourceExpBound_affine sourceExpBound_clearedOnset 5 8
  have hDf := sourceExpBound_affine
    (sourceExpBound_deriv (clearedOnset_entire 0) sourceExpBound_clearedOnset) 5 8
  have hD := sourceExpBound_sub (sourceExpBound_mul hg hDf) hF
  have hR : sourceExpBound (fun w : ℂ => Complex.exp (2*Real.pi*I*w)) := by
    simpa only [add_zero] using sourceExpBound_affine sourceExpBound_exp (2*Real.pi*I) 0
  have hE := sourceExpBound_sub hR (hC 1)
  change sourceExpBound fundamentalCanonicalContourNumerator
  exact sourceExpBound_add
    (sourceExpBound_mul (sourceExpBound_sub hmu (hC 2))
      (sourceExpBound_add (sourceExpBound_mul (sourceExpBound_mul hD hE) hM)
        (sourceExpBound_mul (sourceExpBound_mul hg hF)
          (sourceExpBound_sub (sourceExpBound_mul hE hMX)
            (sourceExpBound_mul (sourceExpBound_mul (hC (Real.pi*I)) hR) hM)))))
    (sourceExpBound_mul (sourceExpBound_mul (sourceExpBound_mul hg hF) hE) hMY)

/-- The source-defined candidate numerator has only linearly many zeros in growing disks.
The nonzero anchor is proved from the original source residue and positive onset. -/
theorem fundamentalCanonicalContourNumerator_zeroCount_linear :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 1 ≤ r →
      (↑(∑ᶠ u, (MeromorphicOn.divisor fundamentalCanonicalContourNumerator
        (Metric.closedBall (-1) r)) u) : ℝ) ≤ K*(1+r) := by
  obtain ⟨A,C,hA,hC,hG⟩ := fundamentalCanonicalContourNumerator_growth
  exact RHTower.exponentialType_zeroCount_linear
    fundamentalCanonicalContourNumerator_entire fundamentalCanonicalContourNumerator_anchor_ne_zero
    hA (le_max_right C 1) (fun w => (hG w).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 1) (Real.exp_pos _).le))

end
end RHTower.D4BMJointSource
