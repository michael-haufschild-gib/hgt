import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCircleReconstruction

/-! The actual base Laplacian of the full angular circle mean. -/
namespace RHTower.D4BMFullAngularCircleAction
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMNativeCircle D4BMCausalKernel
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

private theorem field_smooth (q : XiZeroCopy) (branch : Bool) (p : Point)
    (hp : 0 < p 1) (n : ℕ) : ContDiffAt ℝ n (fullAngularField q branch) p :=
  (contDiffAt_infty.mp (fullAngularField_smooth q branch p hp)) n

private def source (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) : ℂ :=
  fullAngularField q branch (logCircle d theta x k)

private theorem logCircle_pos (d theta x k : ℝ) : 0 < logCircle d theta x k 1 :=
  mul_pos (Real.exp_pos k) (one_div_pos.mpr (denominator_pos d theta))

private theorem linear_coordinates (L : Point →L[ℝ] ℂ) (v : Point) :
    L v = (v 0:ℂ)*L (Pi.single 0 1)+(v 1:ℂ)*L (Pi.single 1 1) := by
  rw [pi_eq_sum_univ' v,map_sum]
  simp [Fin.sum_univ_two,Complex.real_smul]

private def fieldFirst (q : XiZeroCopy) (branch : Bool) (p v : Point) : ℂ :=
  fderiv ℝ (fullAngularField q branch) p v
private def fieldSecond (q : XiZeroCopy) (branch : Bool) (p v a : Point) : ℂ :=
  fderiv ℝ (fderiv ℝ (fullAngularField q branch)) p v v+fieldFirst q branch p a

private theorem first_coordinates (q : XiZeroCopy) (branch : Bool) (p v : Point) :
    fieldFirst q branch p v=(v 0:ℂ)*coordDeriv 0 (fullAngularField q branch) p+
      (v 1:ℂ)*coordDeriv 1 (fullAngularField q branch) p :=
  linear_coordinates _ _

private theorem second_coordinates (q : XiZeroCopy) (branch : Bool) (p v a : Point) (hp : 0 < p 1) :
    fieldSecond q branch p v a =
      (v 0:ℂ)^2*coordDeriv 0 (coordDeriv 0 (fullAngularField q branch)) p+
      (v 0:ℂ)*(v 1:ℂ)*(coordDeriv 0 (coordDeriv 1 (fullAngularField q branch)) p+
        coordDeriv 1 (coordDeriv 0 (fullAngularField q branch)) p)+
      (v 1:ℂ)^2*coordDeriv 1 (coordDeriv 1 (fullAngularField q branch)) p+
      (a 0:ℂ)*coordDeriv 0 (fullAngularField q branch) p+
      (a 1:ℂ)*coordDeriv 1 (fullAngularField q branch) p := by
  have hf := field_smooth q branch p hp 2
  have he (i j : Fin 2) : coordDeriv i (coordDeriv j (fullAngularField q branch)) p=
      fderiv ℝ (fderiv ℝ (fullAngularField q branch)) p (Pi.single i 1) (Pi.single j 1) := by
    change fderiv ℝ (coordDeriv j (fullAngularField q branch)) p (Pi.single i 1)=_
    rw [(ScalarTwoJet.coordDeriv_hasFDerivAt hf j).fderiv]
    rfl
  simp only [he,fieldSecond,first_coordinates]
  rw [linear_coordinates]
  have hl (w : Point) : fderiv ℝ (fderiv ℝ (fullAngularField q branch)) p v w=
      (v 0:ℂ)*fderiv ℝ (fderiv ℝ (fullAngularField q branch)) p (Pi.single 0 1) w+
      (v 1:ℂ)*fderiv ℝ (fderiv ℝ (fullAngularField q branch)) p (Pi.single 1 1) w := by
    conv_lhs => arg 1; rw [pi_eq_sum_univ' v,map_sum]
    simp [Fin.sum_univ_two,Complex.real_smul]
  rw [hl,hl]
  ring

private theorem field_path_first (q : XiZeroCopy) (branch : Bool) {g : ℝ → Point} {v : Point} {t : ℝ}
    (hg : HasDerivAt g v t) (hp : 0 < g t 1) :
    HasDerivAt (fun s => fullAngularField q branch (g s)) (fieldFirst q branch (g t) v) t :=
  ((field_smooth q branch _ hp 1).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hg

private theorem field_path_second (q : XiZeroCopy) (branch : Bool) {g v : ℝ → Point} {a : Point} {t : ℝ}
    (hg : HasDerivAt g (v t) t) (hv : HasDerivAt v a t) (hp : 0 < g t 1) :
    HasDerivAt (fun s => fieldFirst q branch (g s) (v s)) (fieldSecond q branch (g t) (v t) a) t := by
  have hf := field_smooth q branch _ hp 2
  have h := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t hg
  exact h.clm_apply hv


private theorem logCircle_angular (d theta x k : ℝ) :
    HasDerivAt (fun t => logCircle d t x k) (angularVelocity d theta k) theta ∧
    HasDerivAt (fun t => angularVelocity d t k) (angularAcceleration d theta k) theta := by
  obtain ⟨hA,hAA⟩ := offset_angular_derivatives d theta
  obtain ⟨hB,hBB⟩ := height_angular_derivatives d theta
  constructor
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (hA.const_mul (Real.exp k)).const_add x
    · exact hB.const_mul (Real.exp k)
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hAA.const_mul (Real.exp k)
    · exact hBB.const_mul (Real.exp k)

private theorem logCircle_horizontal (d theta x k : ℝ) :
    HasDerivAt (fun t => logCircle d theta t k) (Pi.single 0 1) x := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [logCircle,circle] using (hasDerivAt_id x).add_const (Real.exp k*offset d theta)
  · simpa [logCircle,circle] using hasDerivAt_const x (Real.exp k*height d theta)

private theorem logCircle_height (d theta x k : ℝ) :
    HasDerivAt (fun t => logCircle d theta x t) (heightVelocity d theta k) k ∧
    HasDerivAt (fun t => heightVelocity d theta t) (heightVelocity d theta k) k := by
  constructor
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ((Real.hasDerivAt_exp k).mul_const (offset d theta)).const_add x
    · exact (Real.hasDerivAt_exp k).mul_const (height d theta)
  · apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (Real.hasDerivAt_exp k).mul_const (offset d theta)
    · exact (Real.hasDerivAt_exp k).mul_const (height d theta)


private def horizontalFirst (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) : ℂ :=
  fieldFirst q branch (logCircle d theta x k) (Pi.single 0 1)
private def horizontalSecond (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) : ℂ :=
  fieldSecond q branch (logCircle d theta x k) (Pi.single 0 1) 0
private def logHeightFirst (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) : ℂ :=
  fieldFirst q branch (logCircle d theta x k) (heightVelocity d theta k)
private def logHeightSecond (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) : ℂ :=
  fieldSecond q branch (logCircle d theta x k) (heightVelocity d theta k) (heightVelocity d theta k)


private theorem horizontal_first (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) :
    HasDerivAt (fun t => source q branch d theta t k) (horizontalFirst q branch d theta x k) x :=
  field_path_first q branch (logCircle_horizontal d theta x k) (logCircle_pos d theta x k)
private theorem horizontal_second (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) :
    HasDerivAt (fun t => horizontalFirst q branch d theta t k) (horizontalSecond q branch d theta x k) x :=
  field_path_second q branch (logCircle_horizontal d theta x k) (hasDerivAt_const x _)
    (logCircle_pos d theta x k)
private theorem height_first (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) :
    HasDerivAt (fun t => source q branch d theta x t) (logHeightFirst q branch d theta x k) k :=
  field_path_first q branch (logCircle_height d theta x k).1 (logCircle_pos d theta x k)
private theorem height_second (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) :
    HasDerivAt (fun t => logHeightFirst q branch d theta x t) (logHeightSecond q branch d theta x k) k :=
  field_path_second q branch (logCircle_height d theta x k).1
    (logCircle_height d theta x k).2 (logCircle_pos d theta x k)


private def horizontalAngularDerivative (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) : ℂ :=
  (Real.exp k:ℂ)*(offsetAngular d theta:ℂ)*
    coordDeriv 0 (coordDeriv 0 (fullAngularField q branch)) (logCircle d theta x k)+
  (Real.exp k:ℂ)*(heightAngular d theta:ℂ)*
    coordDeriv 1 (coordDeriv 0 (fullAngularField q branch)) (logCircle d theta x k)

private theorem horizontal_angular (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) :
    HasDerivAt (fun t => coordDeriv 0 (fullAngularField q branch) (logCircle d t x k))
      (horizontalAngularDerivative q branch d theta x k) theta := by
  have hf := field_smooth q branch _ (logCircle_pos d theta x k) 2
  apply ((ScalarTwoJet.coordDeriv_hasFDerivAt hf 0).comp_hasDerivAt theta
    (logCircle_angular d theta x k).1).congr_deriv
  rw [linear_coordinates]
  dsimp [horizontalAngularDerivative,angularVelocity,coordDeriv]
  rw [(ScalarTwoJet.coordDeriv_hasFDerivAt hf 0).fderiv]
  simp only [Complex.ofReal_mul,ContinuousLinearMap.flip_apply]

private theorem base_source (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) :
    (Real.exp k:ℂ)^2*horizontalSecond q branch d theta x k+logHeightSecond q branch d theta x k-
      logHeightFirst q branch d theta x k-
      scalarLaplacian (fullAngularField q branch) (logCircle d theta x k)=
      -2*(Real.exp k:ℂ)*horizontalAngularDerivative q branch d theta x k := by
  have hp := logCircle_pos d theta x k
  have hf := field_smooth q branch _ hp 2
  obtain ⟨hx,hy⟩ := base_laplacian_coefficients d theta
  have hxC : 1+(offset d theta:ℂ)^2-(height d theta:ℂ)^2 = -2*(offsetAngular d theta:ℂ) := by
    exact_mod_cast hx
  have hyC : 2*(offset d theta:ℂ)*(height d theta:ℂ) = -2*(heightAngular d theta:ℂ) := by
    exact_mod_cast hy
  dsimp [horizontalSecond,logHeightSecond,logHeightFirst,horizontalAngularDerivative]
  rw [second_coordinates q branch _ _ _ hp,second_coordinates q branch _ _ _ hp,first_coordinates,
    scalarLaplacian_eq _ _ hp,coordDeriv_commute hf 0 1]
  simp only [heightVelocity,Pi.single_eq_same,Pi.single_eq_of_ne (by decide : (1:Fin 2) ≠ 0),
    Pi.zero_apply,Complex.ofReal_zero,Complex.ofReal_one,Matrix.cons_val_zero,
    Matrix.cons_val_one,Complex.ofReal_mul]
  have he : (logCircle d theta x k 1:ℂ)=(Real.exp k:ℂ)*(height d theta:ℂ) := by
    simp [logCircle,circle]
  rw [he]
  linear_combination
    (Real.exp k:ℂ)^2*coordDeriv 0 (coordDeriv 0 (fullAngularField q branch)) (logCircle d theta x k)*hxC+
    (Real.exp k:ℂ)^2*coordDeriv 1 (coordDeriv 0 (fullAngularField q branch)) (logCircle d theta x k)*hyC

/-- The actual base-point hyperbolic Laplacian differs from the transported source Laplacian
by an explicit derivative around the original circle. -/
private theorem source_base_laplacian_integrand (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) :
    (Real.exp k:ℂ)^2*deriv (deriv (fun t => source q branch d theta t k)) x+
      deriv (deriv (fun t => source q branch d theta x t)) k-
      deriv (fun t => source q branch d theta x t) k-
      scalarLaplacian (fullAngularField q branch) (logCircle d theta x k)=
      -2*(Real.exp k:ℂ)*deriv (fun t => coordDeriv 0 (fullAngularField q branch) (logCircle d t x k)) theta := by
  have hx : deriv (fun t => source q branch d theta t k)=fun t => horizontalFirst q branch d theta t k :=
    funext (fun t => (horizontal_first q branch d theta t k).deriv)
  have hk : deriv (fun t => source q branch d theta x t)=fun t => logHeightFirst q branch d theta x t :=
    funext (fun t => (height_first q branch d theta x t).deriv)
  rw [hx,hk,(horizontal_second q branch d theta x k).deriv,(height_second q branch d theta x k).deriv,
    (horizontal_angular q branch d theta x k).deriv]
  exact base_source q branch d theta x k

/-- Horizontal base differentiation is the full-field derivative at the circle point. -/
private theorem source_horizontal_derivative (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) :
    deriv (fun t => source q branch d theta t k) x=
      coordDeriv 0 (fullAngularField q branch) (logCircle d theta x k) :=
  (horizontal_first q branch d theta x k).deriv


private def mean (q : XiZeroCopy) (branch : Bool) (d x k : ℝ) : ℂ := D4BMNativeCircle.average (fun theta => source q branch d theta x k)

private theorem mean_eq (q : XiZeroCopy) (branch : Bool) (d x k : ℝ) :
    mean q branch d x k=D4BMFullAngularCircle.angularMean q branch d x k := rfl

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
    HasDerivAt (fun r => D4BMNativeCircle.average (fun theta => F (r,theta)))
      (D4BMNativeCircle.average (fun theta => parameterDerivative F (t,theta))) t := by
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
    deriv (fun r => D4BMNativeCircle.average (fun theta => F (r,theta))) t=
      D4BMNativeCircle.average (fun theta => deriv (fun r => F (r,theta)) t) :=
  (average_hasDerivAt hf t).deriv

private theorem average_second {F : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ F) (t : ℝ) :
    deriv (deriv (fun r => D4BMNativeCircle.average (fun theta => F (r,theta)))) t=
      D4BMNativeCircle.average (fun theta => deriv (deriv (fun r => F (r,theta))) t) := by
  have he : deriv (fun r => D4BMNativeCircle.average (fun theta => F (r,theta)))=
      fun r => D4BMNativeCircle.average (fun theta => parameterDerivative F (r,theta)) :=
    funext (fun r => (average_hasDerivAt hf r).deriv)
  rw [he,(average_hasDerivAt (partial_smooth hf) t).deriv]
  rfl


private theorem horizontal_family (q : XiZeroCopy) (branch : Bool) (d k : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => source q branch d p.2 p.1 k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hp : 0 < logCircle d p.2 p.1 k 1 := by
    dsimp [logCircle,circle,height]
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hs : ContDiffAt ℝ ∞ (fullAngularField q branch) (logCircle d p.2 p.1 k) :=
    contDiffAt_infty.mpr (fun n => field_smooth q branch _ hp n)
  apply hs.comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

private theorem height_family (q : XiZeroCopy) (branch : Bool) (d x : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => source q branch d p.2 x p.1) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hp : 0 < logCircle d p.2 x p.1 1 := by
    dsimp [logCircle,circle,height]
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hs : ContDiffAt ℝ ∞ (fullAngularField q branch) (logCircle d p.2 x p.1) :=
    contDiffAt_infty.mpr (fun n => field_smooth q branch _ hp n)
  apply hs.comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

private theorem average_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    D4BMNativeCircle.average (fun theta => f theta+g theta)=D4BMNativeCircle.average f+D4BMNativeCircle.average g := by
  dsimp [D4BMNativeCircle.average]
  rw [integral_add (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
  ring
private theorem average_sub {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    D4BMNativeCircle.average (fun theta => f theta-g theta)=D4BMNativeCircle.average f-D4BMNativeCircle.average g := by
  dsimp [D4BMNativeCircle.average]
  rw [integral_sub (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
  ring
private theorem average_const_mul (c : ℂ) (f : ℝ → ℂ) :
    D4BMNativeCircle.average (fun theta => c*f theta)=c*D4BMNativeCircle.average f := by
  dsimp [D4BMNativeCircle.average]
  rw [integral_const_mul]
  ring

private theorem first_slice_continuous {F : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ F) (t : ℝ) :
    Continuous (fun theta => deriv (fun r => F (r,theta)) t) :=
  (partial_smooth hf).continuous.comp (continuous_const.prodMk continuous_id)
private theorem second_slice_continuous {F : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ F) (t : ℝ) :
    Continuous (fun theta => deriv (deriv (fun r => F (r,theta))) t) :=
  (partial_smooth (partial_smooth hf)).continuous.comp (continuous_const.prodMk continuous_id)


private theorem source_periodic (q : XiZeroCopy) (branch : Bool) (d x k theta : ℝ) :
    source q branch d (theta+2*Real.pi) x k=source q branch d theta x k := by
  simp [source,logCircle,circle,offset,height,denominator,Real.sin_add_two_pi,Real.cos_add_two_pi]

private theorem smooth_derivative {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (deriv f) :=
  (contDiff_infty_iff_deriv.mp hf).2


private theorem average_periodic_derivative {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : ∀ theta, f (theta+2*Real.pi)=f theta) : D4BMNativeCircle.average (deriv f)=0 := by
  have hT : 0 ≤ 2*Real.pi := by positivity
  have h := intervalIntegral.integral_deriv_of_contDiffOn_Icc
    ((hf.of_le (by simp : (1:WithTop ℕ∞) ≤ ∞)).contDiffOn) hT
  rw [intervalIntegral.integral_of_le hT] at h
  dsimp [D4BMNativeCircle.average]
  rw [h,show f (2*Real.pi)=f 0 by simpa using hp 0,sub_self,mul_zero]

private theorem horizontal_theta_smooth (q : XiZeroCopy) (branch : Bool) (d x k : ℝ) :
    ContDiff ℝ ∞ (fun theta => deriv (fun r => source q branch d theta r k) x) := by
  have he : (fun theta => deriv (fun r => source q branch d theta r k) x)=
      fun theta => coordDeriv 0 (fullAngularField q branch) (logCircle d theta x k) :=
    funext (fun theta => source_horizontal_derivative q branch d theta x k)
  rw [he]
  apply contDiff_iff_contDiffAt.mpr
  intro theta
  have hp : 0 < logCircle d theta x k 1 := by
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hs : ContDiffAt ℝ ∞ (fullAngularField q branch) (logCircle d theta x k) :=
    contDiffAt_infty.mpr (fun n => field_smooth q branch _ hp n)
  apply (coordDeriv_contDiffAt (m := ∞) (by simpa using hs) 0).comp theta
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

private theorem horizontal_theta_periodic (q : XiZeroCopy) (branch : Bool) (d x k theta : ℝ) :
    deriv (fun r => source q branch d (theta+2*Real.pi) r k) x=
      deriv (fun r => source q branch d theta r k) x :=
  congrArg (fun f : ℝ → ℂ => deriv f x) (funext (fun r => source_periodic q branch d r k theta))

/-- The actual base-point Laplacian commutes with averaging the full angular field. -/
private theorem mean_laplacian_commutes (q : XiZeroCopy) (branch : Bool) (d x k : ℝ) :
    (Real.exp k:ℂ)^2*deriv (deriv (fun r => mean q branch d r k)) x+
      deriv (deriv (fun r => mean q branch d x r)) k-deriv (fun r => mean q branch d x r) k=
      D4BMNativeCircle.average (fun theta => scalarLaplacian (fullAngularField q branch) (logCircle d theta x k)) := by
  have hx := horizontal_family q branch d k
  have hk := height_family q branch d x
  have hxx := second_slice_continuous hx x
  have hkk := second_slice_continuous hk k
  have hk1 := first_slice_continuous hk k
  have hg := horizontal_theta_smooth q branch d x k
  have hgp := (smooth_derivative hg).continuous
  have hz := average_periodic_derivative hg (horizontal_theta_periodic q branch d x k)
  have hQ : (fun theta => coordDeriv 0 (fullAngularField q branch) (logCircle d theta x k))=
      fun theta => deriv (fun r => source q branch d theta r k) x :=
    funext (fun theta => (source_horizontal_derivative q branch d theta x k).symm)
  have he (theta : ℝ) : scalarLaplacian (fullAngularField q branch) (logCircle d theta x k)=
      (Real.exp k:ℂ)^2*deriv (deriv (fun r => source q branch d theta r k)) x+
      deriv (deriv (fun r => source q branch d theta x r)) k-deriv (fun r => source q branch d theta x r) k+
      2*(Real.exp k:ℂ)*deriv (fun t => deriv (fun r => source q branch d t r k) x) theta := by
    have h := source_base_laplacian_integrand q branch d theta x k
    rw [hQ] at h
    linear_combination -h
  have h := congrArg D4BMNativeCircle.average (funext he)
  erw [average_add (((hxx.const_mul ((Real.exp k:ℂ)^2)).add hkk).sub hk1)
      (hgp.const_mul (2*(Real.exp k:ℂ))),
    average_sub ((hxx.const_mul ((Real.exp k:ℂ)^2)).add hkk) hk1,
    average_add (hxx.const_mul ((Real.exp k:ℂ)^2)) hkk,
    average_const_mul,average_const_mul,hz,mul_zero,add_zero] at h
  rw [← average_second hx x,← average_second hk k,← average_derivative hk k] at h
  exact h.symm

/-- The original base Laplacian commutes with the full angular circular mean. -/
theorem angularMean_laplacian_commutes (q : XiZeroCopy) (branch : Bool) (d x k : ℝ) :
    (Real.exp k:ℂ)^2*deriv (deriv (fun r => D4BMFullAngularCircle.angularMean q branch d r k)) x+
      deriv (deriv (fun r => D4BMFullAngularCircle.angularMean q branch d x r)) k-
      deriv (fun r => D4BMFullAngularCircle.angularMean q branch d x r) k=
      D4BMNativeCircle.average (fun theta => scalarLaplacian (fullAngularField q branch) (logCircle d theta x k)) :=
  by simpa only [mean_eq] using mean_laplacian_commutes q branch d x k

private theorem theta_smooth (q : XiZeroCopy) (branch : Bool) (d x k : ℝ) :
    ContDiff ℝ ∞ (fun theta => source q branch d theta x k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro theta
  have hp : 0 < logCircle d theta x k 1 := logCircle_pos d theta x k
  have hs : ContDiffAt ℝ ∞ (fullAngularField q branch) (logCircle d theta x k) :=
    fullAngularField_smooth q branch _ hp
  apply hs.comp theta
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

/-- The base action of the actual full angular mean retains the complete theta forcing. -/
theorem angularMean_laplacian_equation (q : XiZeroCopy) (branch : Bool) (d x k : ℝ) :
    (Real.exp k:ℂ)^2*deriv (deriv (fun r => D4BMFullAngularCircle.angularMean q branch d r k)) x+
      deriv (deriv (fun r => D4BMFullAngularCircle.angularMean q branch d x r)) k-
      deriv (fun r => D4BMFullAngularCircle.angularMean q branch d x r) k=
      parameter q branch*(D4BMFullAngularCircle.angularMean q branch d x k+D4BMNativeCircle.mean q d x k) := by
  calc
    _ = D4BMNativeCircle.average (fun theta => scalarLaplacian (fullAngularField q branch) (logCircle d theta x k)) :=
      angularMean_laplacian_commutes q branch d x k
    _ = _ := by
      have hh : Continuous (fun theta => source q branch d theta x k) :=
        (theta_smooth q branch d x k).continuous
      have hq : Continuous (fun theta => D4BMNativeCircle.source q d theta x k) := by
        change Continuous ((fun p : Fin 4 → ℝ => D4BMNativeCircle.source q (p 0) (p 1) (p 2) (p 3)) ∘
          (fun theta : ℝ => ![d,theta,x,k]))
        exact (D4BMNativeCircle.source_smooth q).continuous.comp (by fun_prop)
      have he : (fun theta => scalarLaplacian (fullAngularField q branch) (logCircle d theta x k))=
          fun theta => parameter q branch*(source q branch d theta x k+D4BMNativeCircle.source q d theta x k) := by
        funext theta
        rw [fullAngularField_equation q branch _ (logCircle_pos _ _ _ _)]
        dsimp [source,D4BMNativeCircle.source,fullSquarePotential]
        ring
      rw [he,average_const_mul,average_add hh hq]
      rfl

/-- The constructed full angular field has the actual radial/base Darboux action. -/
theorem angularMean_darboux (q : XiZeroCopy) (branch : Bool) (d x k : ℝ) :
    (Real.sinh d:ℂ)^2*deriv (deriv (fun r => D4BMFullAngularCircle.angularMean q branch r x k)) d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*deriv (fun r => D4BMFullAngularCircle.angularMean q branch r x k) d=
      (Real.sinh d:ℂ)^2*((Real.exp k:ℂ)^2*deriv (deriv (fun r => D4BMFullAngularCircle.angularMean q branch d r k)) x+
        deriv (deriv (fun r => D4BMFullAngularCircle.angularMean q branch d x r)) k-
        deriv (fun r => D4BMFullAngularCircle.angularMean q branch d x r) k) := by
  rw [D4BMFullAngularCircle.angularMean_forced,angularMean_laplacian_equation]
  ring

private theorem mean_radial_smooth (q : XiZeroCopy) (branch : Bool) (x k : ℝ) :
    ContDiff ℝ ∞ (fun d => mean q branch d x k) :=
  D4BMFullAngularCircle.angularMean_smooth q branch x k

private theorem mean_zero (q : XiZeroCopy) (branch : Bool) (x k : ℝ) :
    mean q branch 0 x k=fullAngularField q branch ![x,Real.exp k] :=
  D4BMFullAngularCircle.angularMean_zero q branch x k


private def angularKernel (q : XiZeroCopy) (branch : Bool) (z X k : ℝ) : ℂ := mean q branch (Real.arcosh z) X k
private def argumentFirst (q : XiZeroCopy) (branch : Bool) (z X k : ℝ) : ℂ :=
  deriv (fun r => mean q branch r X k) (Real.arcosh z)/(Real.sinh (Real.arcosh z):ℂ)
private def argumentSecond (q : XiZeroCopy) (branch : Bool) (z X k : ℝ) : ℂ :=
  deriv (deriv (fun r => mean q branch r X k)) (Real.arcosh z)/(Real.sinh (Real.arcosh z):ℂ)^2-
    (Real.cosh (Real.arcosh z):ℂ)*deriv (fun r => mean q branch r X k) (Real.arcosh z)/
      (Real.sinh (Real.arcosh z):ℂ)^3
private def angularAction (q : XiZeroCopy) (branch : Bool) (z X k : ℝ) : ℂ :=
  (Real.exp k:ℂ)^2*deriv (deriv (fun r => angularKernel q branch z r k)) X+
    deriv (deriv (fun r => angularKernel q branch z X r)) k-deriv (fun r => angularKernel q branch z X r) k

private theorem radius_derivative {z : ℝ} (hz : 1 < z) :
    HasDerivAt Real.arcosh (1/Real.sinh (Real.arcosh z)) z := by
  simpa only [one_div,Real.sinh_arcosh hz.le] using Real.hasDerivAt_arcosh hz

private theorem angular_derivatives (q : XiZeroCopy) (branch : Bool) (X k : ℝ) {z : ℝ} (hz : 1 < z) :
    HasDerivAt (fun y => angularKernel q branch y X k) (argumentFirst q branch z X k) z ∧
    HasDerivAt (fun y => argumentFirst q branch y X k) (argumentSecond q branch z X k) z := by
  have hs := mean_radial_smooth q branch X k
  have hs1 := (contDiff_infty_iff_deriv.mp hs).2
  have hm := ((hs.contDiffAt (x := Real.arcosh z)).differentiableAt (by simp)).hasDerivAt
  have hm1 := ((hs1.contDiffAt (x := Real.arcosh z)).differentiableAt (by simp)).hasDerivAt
  have hd := radius_derivative hz
  have hn : Real.sinh (Real.arcosh z) ≠ 0 := (Real.sinh_pos_iff.mpr (Real.arcosh_pos hz)).ne'
  have hnC : (Real.sinh (Real.arcosh z):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have hr := ((Real.hasDerivAt_sinh (Real.arcosh z)).comp z hd).ofReal_comp
  constructor
  · apply (hm.scomp z hd).congr_deriv
    simp only [argumentFirst,Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one]
    ring
  · apply ((hm1.scomp z hd).div hr hnC).congr_deriv
    dsimp [argumentSecond]
    simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one]
    field_simp [hnC]

private theorem angular_equation (q : XiZeroCopy) (branch : Bool) (X k : ℝ) {z : ℝ} (hz : 1 < z) :
    ((z:ℂ)^2-1)*argumentSecond q branch z X k+2*(z:ℂ)*argumentFirst q branch z X k=angularAction q branch z X k := by
  have hn : (Real.sinh (Real.arcosh z):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr (Real.arcosh_pos hz)).ne'
  have he : (z:ℂ)^2-1=(Real.sinh (Real.arcosh z):ℂ)^2 := by
    have h := Real.cosh_sq_sub_sinh_sq (Real.arcosh z)
    rw [Real.cosh_arcosh hz.le] at h
    exact_mod_cast (by linarith : z^2-1=Real.sinh (Real.arcosh z)^2)
  have h := angularMean_darboux q branch (Real.arcosh z) X k
  change _ = (Real.sinh (Real.arcosh z):ℂ)^2*angularAction q branch z X k at h
  rw [Real.cosh_arcosh hz.le] at h
  rw [he]
  dsimp [argumentSecond,argumentFirst]
  simp only [mean_eq]
  rw [Real.cosh_arcosh hz.le]
  linear_combination (norm := (field_simp [hn]; ring)) h/(Real.sinh (Real.arcosh z):ℂ)^2

def fullAngularRiemannKernel (q : XiZeroCopy) (branch : Bool) (h x y X k : ℝ) : ℂ :=
  angularKernel q branch (invariant h x y) X k
private def nativeTimeFirst (q : XiZeroCopy) (branch : Bool) (h x y X k : ℝ) : ℂ :=
  argumentFirst q branch (invariant h x y) X k*(invariantTimeFirst h x y:ℂ)
private def nativeTimeSecond (q : XiZeroCopy) (branch : Bool) (h x y X k : ℝ) : ℂ :=
  argumentSecond q branch (invariant h x y) X k*(invariantTimeFirst h x y:ℂ)^2+
    argumentFirst q branch (invariant h x y) X k*(invariantTimeSecond h x y:ℂ)
private def nativeSpaceFirst (q : XiZeroCopy) (branch : Bool) (h x y X k : ℝ) : ℂ :=
  argumentFirst q branch (invariant h x y) X k*(invariantSpaceFirst h x y:ℂ)
private def nativeSpaceSecond (q : XiZeroCopy) (branch : Bool) (h x y X k : ℝ) : ℂ :=
  argumentSecond q branch (invariant h x y) X k*(invariantSpaceFirst h x y:ℂ)^2+
    argumentFirst q branch (invariant h x y) X k*(invariantSpaceSecond h x y:ℂ)

private theorem time_derivatives (q : XiZeroCopy) (branch : Bool) (h x y X k : ℝ) (hz : 1 < invariant h x y) :
    HasDerivAt (fun t => fullAngularRiemannKernel q branch t x y X k) (nativeTimeFirst q branch h x y X k) h ∧
    HasDerivAt (fun t => nativeTimeFirst q branch t x y X k) (nativeTimeSecond q branch h x y X k) h := by
  obtain ⟨hA,hB⟩ := angular_derivatives q branch X k hz
  obtain ⟨hz1,hz2⟩ := invariant_time_derivatives h x y
  constructor
  · apply (hA.scomp h hz1).congr_deriv
    simp only [nativeTimeFirst,Complex.real_smul]
    ring
  · apply ((hB.scomp h hz1).mul hz2.ofReal_comp).congr_deriv
    simp only [nativeTimeSecond,Complex.real_smul,Function.comp_def]
    ring

private theorem space_derivatives (q : XiZeroCopy) (branch : Bool) (h x y X k : ℝ) (hz : 1 < invariant h x y) :
    HasDerivAt (fun t => fullAngularRiemannKernel q branch h t y X k) (nativeSpaceFirst q branch h x y X k) x ∧
    HasDerivAt (fun t => nativeSpaceFirst q branch h t y X k) (nativeSpaceSecond q branch h x y X k) x := by
  obtain ⟨hA,hB⟩ := angular_derivatives q branch X k hz
  obtain ⟨hz1,hz2⟩ := invariant_space_derivatives h x y
  constructor
  · apply (hA.scomp x hz1).congr_deriv
    simp only [nativeSpaceFirst,Complex.real_smul]
    ring
  · apply ((hB.scomp x hz1).mul hz2.ofReal_comp).congr_deriv
    simp only [nativeSpaceSecond,Complex.real_smul,Function.comp_def]
    ring

/-- The complete full-angular Riemann kernel satisfies the original time/tortoise wave equation
with the actual hyperbolic Laplacian in horizontal and logarithmic-height coordinates. -/
theorem fullAngularRiemannKernel_wave (q : XiZeroCopy) (branch : Bool) (p : InteriorPoint) (X k : ℝ) :
    deriv (deriv (fun h => fullAngularRiemannKernel q branch h p.val.target p.val.source X k)) p.val.time-
      deriv (deriv (fun x => fullAngularRiemannKernel q branch p.val.time x p.val.source X k)) p.val.target-
      ((Real.exp k:ℂ)^2*deriv (deriv (fun a => fullAngularRiemannKernel q branch p.val.time p.val.target p.val.source a k)) X+
        deriv (deriv (fun a => fullAngularRiemannKernel q branch p.val.time p.val.target p.val.source X a)) k-
        deriv (fun a => fullAngularRiemannKernel q branch p.val.time p.val.target p.val.source X a) k)/
          (Real.cosh p.val.target:ℂ)^2=0 := by
  obtain ⟨ht,htt⟩ := time_derivatives q branch p.val.time p.val.target p.val.source X k p.property
  obtain ⟨hx,hxx⟩ := space_derivatives q branch p.val.time p.val.target p.val.source X k p.property
  have et : deriv (fun h => fullAngularRiemannKernel q branch h p.val.target p.val.source X k) =ᶠ[𝓝 p.val.time]
      fun h => nativeTimeFirst q branch h p.val.target p.val.source X k := by
    filter_upwards [(invariant_time_derivatives p.val.time p.val.target p.val.source).1.continuousAt.eventually_const_lt p.property] with h hh
    exact (time_derivatives q branch h p.val.target p.val.source X k hh).1.deriv
  have ex : deriv (fun x => fullAngularRiemannKernel q branch p.val.time x p.val.source X k) =ᶠ[𝓝 p.val.target]
      fun x => nativeSpaceFirst q branch p.val.time x p.val.source X k := by
    filter_upwards [(invariant_space_derivatives p.val.time p.val.target p.val.source).1.continuousAt.eventually_const_lt p.property] with x hh
    exact (space_derivatives q branch p.val.time x p.val.source X k hh).1.deriv
  rw [et.deriv_eq,ex.deriv_eq,htt.deriv,hxx.deriv]
  have h1 : (invariantTimeFirst p.val.time p.val.target p.val.source:ℂ)^2-
      (invariantSpaceFirst p.val.time p.val.target p.val.source:ℂ)^2=
      ((invariant p.val.time p.val.target p.val.source:ℂ)^2-1)/(Real.cosh p.val.target:ℂ)^2 := by
    exact_mod_cast (invariant_wave_geometry p.val.time p.val.target p.val.source).1
  have h2 : (invariantTimeSecond p.val.time p.val.target p.val.source:ℂ)-
      (invariantSpaceSecond p.val.time p.val.target p.val.source:ℂ)=
      2*(invariant p.val.time p.val.target p.val.source:ℂ)/(Real.cosh p.val.target:ℂ)^2 := by
    exact_mod_cast (invariant_wave_geometry p.val.time p.val.target p.val.source).2
  have h := angular_equation q branch X k p.property
  change _-_ - angularAction q branch (invariant p.val.time p.val.target p.val.source) X k/(Real.cosh p.val.target:ℂ)^2=0
  dsimp [nativeTimeSecond,nativeSpaceSecond]
  linear_combination
    argumentSecond q branch (invariant p.val.time p.val.target p.val.source) X k*h1+
    argumentFirst q branch (invariant p.val.time p.val.target p.val.source) X k*h2+
    h/(Real.cosh p.val.target:ℂ)^2

/-- The characteristic value is the original constructed full angular field. -/
theorem fullAngularRiemannKernel_characteristic (q : XiZeroCopy) (branch : Bool) (x y X k : ℝ) :
    fullAngularRiemannKernel q branch (x-y) x y X k=fullAngularField q branch ![X,Real.exp k] := by
  rw [fullAngularRiemannKernel,invariant_characteristic,angularKernel,Real.arcosh_zero,mean_zero]

/-- The full-angular kernel and its image agree at the original AdS endpoint. -/
theorem fullAngularRiemannKernel_AdS (q : XiZeroCopy) (branch : Bool) (h y X k : ℝ) :
    fullAngularRiemannKernel q branch h 0 y X k-fullAngularRiemannKernel q branch h 0 (-y) X k=0 := by
  rw [fullAngularRiemannKernel,fullAngularRiemannKernel,invariant_AdS,sub_self]

end
end RHTower.D4BMFullAngularCircleAction
