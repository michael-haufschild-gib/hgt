import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeCircleMean
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularCovector
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCausalRiemannKernel
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullSourceOnsetReduction

/-! A source-faithful circular Green identity for the full angular response. -/
namespace RHTower.D4BMFullAngularCircle
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

def angularSource (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) : ℂ :=
  fullAngularField q branch (logCircle d theta x k)

/-- The actual circular average of the constructed full angular response. -/
def angularMean (q : XiZeroCopy) (branch : Bool) (d x k : ℝ) : ℂ :=
  D4BMNativeCircle.average (fun theta => angularSource q branch d theta x k)

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
      (v 0:ℂ)^(2 : ℕ)*coordDeriv 0 (coordDeriv 0 (fullAngularField q branch)) p+
      (v 0:ℂ)*(v 1:ℂ)*(coordDeriv 0 (coordDeriv 1 (fullAngularField q branch)) p+
        coordDeriv 1 (coordDeriv 0 (fullAngularField q branch)) p)+
      (v 1:ℂ)^(2 : ℕ)*coordDeriv 1 (coordDeriv 1 (fullAngularField q branch)) p+
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


private theorem logCircle_radial (d theta x k : ℝ) :
    HasDerivAt (fun r => logCircle r theta x k) (radialVelocity d theta k) d ∧
    HasDerivAt (fun r => radialVelocity r theta k) (radialAcceleration d theta k) d := by
  obtain ⟨hA,hAA⟩ := offset_radial_derivatives d theta
  obtain ⟨hB,hBB⟩ := height_radial_derivatives d theta
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


private def radialFirst (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) : ℂ :=
  fieldFirst q branch (logCircle d theta x k) (radialVelocity d theta k)
private def radialSecond (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) : ℂ :=
  fieldSecond q branch (logCircle d theta x k) (radialVelocity d theta k) (radialAcceleration d theta k)
private def angularFirst (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) : ℂ :=
  fieldFirst q branch (logCircle d theta x k) (angularVelocity d theta k)
private def angularSecond (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) : ℂ :=
  fieldSecond q branch (logCircle d theta x k) (angularVelocity d theta k) (angularAcceleration d theta k)

private theorem radial_first (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) :
    HasDerivAt (fun r => angularSource q branch r theta x k) (radialFirst q branch d theta x k) d :=
  field_path_first q branch (logCircle_radial d theta x k).1 (logCircle_pos d theta x k)
private theorem radial_second (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) :
    HasDerivAt (fun r => radialFirst q branch r theta x k) (radialSecond q branch d theta x k) d :=
  field_path_second q branch (logCircle_radial d theta x k).1
    (logCircle_radial d theta x k).2 (logCircle_pos d theta x k)
private theorem angular_first (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) :
    HasDerivAt (fun t => angularSource q branch d t x k) (angularFirst q branch d theta x k) theta :=
  field_path_first q branch (logCircle_angular d theta x k).1 (logCircle_pos d theta x k)
private theorem angular_second (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) :
    HasDerivAt (fun t => angularFirst q branch d t x k) (angularSecond q branch d theta x k) theta :=
  field_path_second q branch (logCircle_angular d theta x k).1
    (logCircle_angular d theta x k).2 (logCircle_pos d theta x k)

private theorem polar_source (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) :
    (Real.sinh d:ℂ)^(2 : ℕ)*radialSecond q branch d theta x k+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*radialFirst q branch d theta x k+
      angularSecond q branch d theta x k=
      (Real.sinh d:ℂ)^(2 : ℕ)*scalarLaplacian (fullAngularField q branch) (logCircle d theta x k) := by
  have hp := logCircle_pos d theta x k
  obtain ⟨hxx,hxy,hyy⟩ := polar_principal d theta
  obtain ⟨hx,hy⟩ := polar_connection d theta
  have hxxC : (Real.sinh d:ℂ)^(2 : ℕ)*(offsetRadial d theta:ℂ)^(2 : ℕ)+(offsetAngular d theta:ℂ)^(2 : ℕ)=
      (Real.sinh d:ℂ)^(2 : ℕ)*(height d theta:ℂ)^(2 : ℕ) := by exact_mod_cast hxx
  have hxyC : (Real.sinh d:ℂ)^(2 : ℕ)*(offsetRadial d theta:ℂ)*(heightRadial d theta:ℂ)+
      (offsetAngular d theta:ℂ)*(heightAngular d theta:ℂ)=0 := by exact_mod_cast hxy
  have hyyC : (Real.sinh d:ℂ)^(2 : ℕ)*(heightRadial d theta:ℂ)^(2 : ℕ)+(heightAngular d theta:ℂ)^(2 : ℕ)=
      (Real.sinh d:ℂ)^(2 : ℕ)*(height d theta:ℂ)^(2 : ℕ) := by exact_mod_cast hyy
  have hxC : (Real.sinh d:ℂ)^(2 : ℕ)*(offsetRadialSecond d theta:ℂ)+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*(offsetRadial d theta:ℂ)+(offsetAngularSecond d theta:ℂ)=0 := by
    exact_mod_cast hx
  have hyC : (Real.sinh d:ℂ)^(2 : ℕ)*(heightRadialSecond d theta:ℂ)+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*(heightRadial d theta:ℂ)+(heightAngularSecond d theta:ℂ)=0 := by
    exact_mod_cast hy
  dsimp [radialSecond,radialFirst,angularSecond]
  rw [second_coordinates q branch _ _ _ hp,first_coordinates,second_coordinates q branch _ _ _ hp,
    scalarLaplacian_eq _ _ hp]
  dsimp [radialVelocity,radialAcceleration,angularVelocity,angularAcceleration,
    D4BMAngularSeries.hyperbolicLaplacian]
  simp only [Complex.ofReal_mul]
  have he : (logCircle d theta x k 1:ℂ)=(Real.exp k:ℂ)*(height d theta:ℂ) := by
    simp [logCircle,circle]
  rw [he]
  linear_combination
    (Real.exp k:ℂ)^(2 : ℕ)*coordDeriv 0 (coordDeriv 0 (fullAngularField q branch)) (logCircle d theta x k)*hxxC+
    (Real.exp k:ℂ)^(2 : ℕ)*(coordDeriv 0 (coordDeriv 1 (fullAngularField q branch)) (logCircle d theta x k)+
      coordDeriv 1 (coordDeriv 0 (fullAngularField q branch)) (logCircle d theta x k))*hxyC+
    (Real.exp k:ℂ)^(2 : ℕ)*coordDeriv 1 (coordDeriv 1 (fullAngularField q branch)) (logCircle d theta x k)*hyyC+
    (Real.exp k:ℂ)*coordDeriv 0 (fullAngularField q branch) (logCircle d theta x k)*hxC+
    (Real.exp k:ℂ)*coordDeriv 1 (fullAngularField q branch) (logCircle d theta x k)*hyC

/-- The full angular response satisfies the polar Darboux identity with its complete angular Laplacian. -/
private theorem source_darboux_integrand (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) :
    (Real.sinh d:ℂ)^(2 : ℕ)*deriv (deriv (fun r => angularSource q branch r theta x k)) d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*deriv (fun r => angularSource q branch r theta x k) d+
      deriv (deriv (fun t => angularSource q branch d t x k)) theta=
      (Real.sinh d:ℂ)^(2 : ℕ)*scalarLaplacian (fullAngularField q branch) (logCircle d theta x k) := by
  have hr : deriv (fun r => angularSource q branch r theta x k)=fun r => radialFirst q branch r theta x k :=
    funext (fun r => (radial_first q branch r theta x k).deriv)
  have ha : deriv (fun t => angularSource q branch d t x k)=fun t => angularFirst q branch d t x k :=
    funext (fun t => (angular_first q branch d t x k).deriv)
  rw [hr,ha,(radial_second q branch d theta x k).deriv,(angular_second q branch d theta x k).deriv]
  exact polar_source q branch d theta x k


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

private theorem radial_family (q : XiZeroCopy) (branch : Bool) (x k : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => angularSource q branch p.1 p.2 x k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hp : 0 < logCircle p.1 p.2 x k 1 := by
    dsimp [logCircle,circle,height]
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hs : ContDiffAt ℝ ∞ (fullAngularField q branch) (logCircle p.1 p.2 x k) :=
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

private theorem theta_smooth (q : XiZeroCopy) (branch : Bool) (d x k : ℝ) :
    ContDiff ℝ ∞ (fun theta => angularSource q branch d theta x k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro theta
  have hp : 0 < logCircle d theta x k 1 := by
    exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hs : ContDiffAt ℝ ∞ (fullAngularField q branch) (logCircle d theta x k) :=
    contDiffAt_infty.mpr (fun n => field_smooth q branch _ hp n)
  apply hs.comp theta
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := exact (denominator_pos _ _).ne')

private theorem source_periodic (q : XiZeroCopy) (branch : Bool) (d x k theta : ℝ) :
    angularSource q branch d (theta+2*Real.pi) x k=angularSource q branch d theta x k := by
  simp [angularSource,logCircle,circle,offset,height,denominator,Real.sin_add_two_pi,Real.cos_add_two_pi]

/-- Negating the literal native radius is the same circle after the forced half-turn. -/
theorem logCircle_neg_radius_eq_halfTurn (d theta x k : ℝ) :
    logCircle (-d) theta x k = logCircle d (theta + Real.pi) x k := by
  funext i
  fin_cases i <;> simp [logCircle,circle,offset,height,denominator]

/-- The full constructed response is transported by the same literal half-turn. -/
theorem angularSource_neg_radius_eq_halfTurn (q : XiZeroCopy) (branch : Bool) (d theta x k : ℝ) :
    angularSource q branch (-d) theta x k = angularSource q branch d (theta + Real.pi) x k := by
  unfold angularSource
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
    (hp : ∀ theta, f (theta+2*Real.pi)=f theta) : D4BMNativeCircle.average (deriv f)=0 := by
  have hT : 0 ≤ 2*Real.pi := by positivity
  have h := intervalIntegral.integral_deriv_of_contDiffOn_Icc
    ((hf.of_le (by simp : (1:WithTop ℕ∞) ≤ ∞)).contDiffOn) hT
  rw [intervalIntegral.integral_of_le hT] at h
  dsimp [D4BMNativeCircle.average]
  rw [h,show f (2*Real.pi)=f 0 by simpa using hp 0,sub_self,mul_zero]

/-- The original circle average has the full radial Darboux action on the original theta angularSource. -/
private theorem mean_radial_action (q : XiZeroCopy) (branch : Bool) (d x k : ℝ) :
    (Real.sinh d:ℂ)^(2 : ℕ)*deriv (deriv (fun r => angularMean q branch r x k)) d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*deriv (fun r => angularMean q branch r x k) d=
      (Real.sinh d:ℂ)^(2 : ℕ)*D4BMNativeCircle.average (fun theta =>
        scalarLaplacian (fullAngularField q branch) (logCircle d theta x k)) := by
  have hf := radial_family q branch x k
  have hr := first_slice_continuous hf d
  have hrr := second_slice_continuous hf d
  have ht := theta_smooth q branch d x k
  have htt := (smooth_derivative (smooth_derivative ht)).continuous
  have hz : D4BMNativeCircle.average (deriv (deriv (fun theta => angularSource q branch d theta x k)))=0 :=
    average_periodic_derivative (smooth_derivative ht) (periodic_derivative ht (source_periodic q branch d x k))
  have h := congrArg D4BMNativeCircle.average (funext (fun theta => source_darboux_integrand q branch d theta x k))
  erw [average_add ((hrr.const_mul ((Real.sinh d:ℂ)^(2 : ℕ))).add
      (hr.const_mul ((Real.sinh d:ℂ)*(Real.cosh d:ℂ)))) htt,
    average_add (hrr.const_mul ((Real.sinh d:ℂ)^(2 : ℕ)))
      (hr.const_mul ((Real.sinh d:ℂ)*(Real.cosh d:ℂ))),average_const_mul,average_const_mul,
    average_const_mul,hz,add_zero] at h
  rw [← average_second hf d,← average_derivative hf d] at h
  exact h


private theorem average_constant (c : ℂ) : D4BMNativeCircle.average (fun _ => c)=c := by
  have hT : 0 ≤ 2*Real.pi := by positivity
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  dsimp [D4BMNativeCircle.average]
  rw [← intervalIntegral.integral_of_le hT]
  simp only [intervalIntegral.integral_const,sub_zero,Complex.real_smul,Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  field_simp [hpi]

/-- Radius zero retains the constructed full angular response. -/
theorem angularMean_zero (q : XiZeroCopy) (branch : Bool) (x k : ℝ) :
    angularMean q branch 0 x k=fullAngularField q branch ![x,Real.exp k] := by
  have he : (fun theta => angularSource q branch 0 theta x k)=fun _ => fullAngularField q branch ![x,Real.exp k] := by
    funext theta
    simp [angularSource,logCircle,circle,offset,height,denominator]
  rw [angularMean,he,average_constant]

/-- The complete full angular mean is even in the signed literal radius.  This is
the exact parity required before regularizing the seed-cap corner; it is not a
source-only replacement. -/
theorem angularMean_neg_radius (q : XiZeroCopy) (branch : Bool) (d x k : ℝ) :
    angularMean q branch (-d) x k = angularMean q branch d x k := by
  have hsource : (fun theta => angularSource q branch (-d) theta x k) =
      fun theta => angularSource q branch d (theta + Real.pi) x k := by
    funext theta
    exact angularSource_neg_radius_eq_halfTurn q branch d theta x k
  rw [angularMean,hsource]
  unfold D4BMNativeCircle.average
  congr 1
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hperiod : Function.Periodic (fun theta => angularSource q branch d theta x k) (2 * Real.pi) :=
    fun theta => source_periodic q branch d x k theta
  change (∫ theta in Ioc (0 : ℝ) (2 * Real.pi),
      angularSource q branch d (theta + Real.pi) x k) =
    ∫ theta in Ioc (0 : ℝ) (2 * Real.pi), angularSource q branch d theta x k
  calc
    (∫ theta in Ioc (0 : ℝ) (2 * Real.pi),
        angularSource q branch d (theta + Real.pi) x k) =
        ∫ theta in (0 : ℝ)..2 * Real.pi, angularSource q branch d (theta + Real.pi) x k :=
      (intervalIntegral.integral_of_le hpi).symm
    _ = ∫ theta in Real.pi..2 * Real.pi + Real.pi, angularSource q branch d theta x k := by
      simpa only [zero_add] using
        intervalIntegral.integral_comp_add_right
          (a := (0 : ℝ)) (b := 2 * Real.pi)
          (fun theta => angularSource q branch d theta x k) Real.pi
    _ = ∫ theta in (0 : ℝ)..2 * Real.pi, angularSource q branch d theta x k := by
      simpa only [zero_add, add_comm] using (hperiod.intervalIntegral_add_eq 0 Real.pi).symm
    _ = ∫ theta in Ioc (0 : ℝ) (2 * Real.pi), angularSource q branch d theta x k :=
      intervalIntegral.integral_of_le hpi

private theorem average_finite_smooth (n : ℕ) {F : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ F) :
    ContDiff ℝ n (fun r => D4BMNativeCircle.average (fun theta => F (r,theta))) := by
  have hd : Differentiable ℝ (fun r => D4BMNativeCircle.average (fun theta => F (r,theta))) :=
    fun r => (average_hasDerivAt hf r).differentiableAt
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr hd.continuous
  | succ n ih =>
    change ContDiff ℝ ((n:WithTop ℕ∞)+1) _
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨hd,by simp,?_⟩
    have he : deriv (fun r => D4BMNativeCircle.average (fun theta => F (r,theta)))=
        fun r => D4BMNativeCircle.average (fun theta => parameterDerivative F (r,theta)) :=
      funext (fun r => (average_hasDerivAt hf r).deriv)
    rw [he]
    exact ih (partial_smooth hf) (fun r => (average_hasDerivAt (partial_smooth hf) r).differentiableAt)

/-- Every radial derivative of the actual finite circle average exists, including at radius zero. -/
theorem angularMean_smooth (q : XiZeroCopy) (branch : Bool) (x k : ℝ) : ContDiff ℝ ∞ (fun d => angularMean q branch d x k) :=
  contDiff_infty.mpr (fun n => average_finite_smooth n (radial_family q branch x k))

private theorem deriv_neg_of_even {f : ℝ → ℂ} (heven : Function.Even f)
    (hf : Differentiable ℝ f) (x : ℝ) : deriv f (-x) = -deriv f x := by
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id x).neg
  have hcomp := ((hf (-x)).hasDerivAt.scomp x hneg).deriv
  have hreflect : f ∘ Neg.neg = (fun y : ℝ => f (-y)) := by rfl
  rw [hreflect] at hcomp
  have heq : (fun y : ℝ => f (-y)) = f := funext heven
  have hderiv := congrArg (fun g : ℝ → ℂ => deriv g x) heq
  change deriv (fun y : ℝ => f (-y)) x = deriv f x at hderiv
  rw [hcomp] at hderiv
  have hderiv' : -deriv f (-x) = deriv f x := by simpa using hderiv
  calc
    deriv f (-x) = -(-deriv f (-x)) := by ring
    _ = -deriv f x := by rw [hderiv']

private theorem deriv2_even_of_even {f : ℝ → ℂ} (heven : Function.Even f)
    (hf : ContDiff ℝ ∞ f) (u : ℝ) :
    deriv (deriv f) (-u) = deriv (deriv f) u := by
  have hf1 := smooth_derivative hf
  have hodd : Function.Odd (deriv f) := by
    intro x
    exact deriv_neg_of_even heven (hf.differentiable (by simp)) x
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) u := (hasDerivAt_id u).neg
  have hleft := ((hf1.differentiable (by simp) (-u)).hasDerivAt.scomp u hneg).deriv
  have hreflect : deriv f ∘ Neg.neg = (fun y : ℝ => deriv f (-y)) := by rfl
  rw [hreflect] at hleft
  have hright : deriv (fun y : ℝ => -deriv f y) u = -deriv (deriv f) u :=
    ((hf1.differentiable (by simp) u).hasDerivAt).neg.deriv
  have heq : (fun y : ℝ => deriv f (-y)) = fun y : ℝ => -deriv f y := funext hodd
  have huniq := congrArg (fun g : ℝ → ℂ => deriv g u) heq
  change deriv (fun y : ℝ => deriv f (-y)) u = deriv (fun y : ℝ => -deriv f y) u at huniq
  rw [hleft, hright] at huniq
  have huniq' : -deriv (deriv f) (-u) = -deriv (deriv f) u := by simpa using huniq
  calc
    deriv (deriv f) (-u) = -(-deriv (deriv f) (-u)) := by ring
    _ = -(-deriv (deriv f) u) := by rw [huniq']
    _ = deriv (deriv f) u := by ring

/-- The actual full circle germ has no odd radial jets through order three.
These are the exact local compatibility conditions required by the literal
`arcosh (max 1 ·)` cap corner before any two-jet construction. -/
theorem angularMean_radial_oddJets_zero (q : XiZeroCopy) (branch : Bool) (x k : ℝ) :
    deriv (fun d => angularMean q branch d x k) 0 = 0 ∧
      deriv (deriv (deriv (fun d => angularMean q branch d x k))) 0 = 0 := by
  let f : ℝ → ℂ := fun d => angularMean q branch d x k
  have heven : Function.Even f := by
    intro d
    exact angularMean_neg_radius q branch d x k
  have hf : ContDiff ℝ ∞ f := angularMean_smooth q branch x k
  have hf1 := smooth_derivative hf
  have hf2 := smooth_derivative hf1
  constructor
  · have h := deriv_neg_of_even heven (hf.differentiable (by simp)) 0
    simp only [neg_zero] at h
    linear_combination h / 2
  · have heven2 : Function.Even (deriv (deriv f)) := by
      intro d
      exact deriv2_even_of_even heven hf d
    have h := deriv_neg_of_even heven2 (hf2.differentiable (by simp)) 0
    simp only [neg_zero] at h
    linear_combination h / 2

/-- The forced circular equation retains the literal half-square source on both physical branches. -/
theorem angularMean_forced (q : XiZeroCopy) (branch : Bool) (d x k : ℝ) :
    (Real.sinh d:ℂ)^(2 : ℕ)*deriv (deriv (fun r => angularMean q branch r x k)) d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*deriv (fun r => angularMean q branch r x k) d=
      (Real.sinh d:ℂ)^(2 : ℕ)*parameter q branch*
        (angularMean q branch d x k+D4BMNativeCircle.mean q d x k) := by
  have h := mean_radial_action q branch d x k
  have hq : Continuous (fun theta => D4BMNativeCircle.source q d theta x k) := by
    have hs := (D4BMNativeCircle.source_smooth q).comp
      (show ContDiff ℝ ∞ (fun theta : ℝ => ![d,theta,x,k]) by
        apply contDiff_pi.mpr
        intro i
        fin_cases i
        · change ContDiff ℝ ∞ (fun _ : ℝ => d)
          exact contDiff_const
        · change ContDiff ℝ ∞ (fun theta : ℝ => theta)
          exact contDiff_id
        · change ContDiff ℝ ∞ (fun _ : ℝ => x)
          exact contDiff_const
        · change ContDiff ℝ ∞ (fun _ : ℝ => k)
          exact contDiff_const)
    exact hs.continuous
  have he : (fun theta => scalarLaplacian (fullAngularField q branch) (logCircle d theta x k))=
      fun theta => parameter q branch*
        (angularSource q branch d theta x k+D4BMNativeCircle.source q d theta x k) := by
    funext theta
    rw [fullAngularField_equation q branch _ (logCircle_pos _ _ _ _)]
    dsimp [angularSource,D4BMNativeCircle.source,fullSquarePotential]
    ring
  rw [he,average_const_mul,average_add (theta_smooth q branch d x k).continuous hq] at h
  simpa only [angularMean,D4BMNativeCircle.mean,mul_assoc] using h

/-- The original Legendre kernel at the actual angular parameter, in circle radius. -/
def radialLegendre (q : XiZeroCopy) (branch : Bool) (d : ℝ) : ℂ :=
  legendreKernel (2*physicalRate q branch+1) (Real.cosh d)
private def radialLegendreFirst (q : XiZeroCopy) (branch : Bool) (d : ℝ) : ℂ :=
  (Real.sinh d:ℂ)*legendreKernelFirst (2*physicalRate q branch+1) (Real.cosh d)
private def radialLegendreSecond (q : XiZeroCopy) (branch : Bool) (d : ℝ) : ℂ :=
  (Real.cosh d:ℂ)*legendreKernelFirst (2*physicalRate q branch+1) (Real.cosh d)+
    (Real.sinh d:ℂ)^(2 : ℕ)*legendreKernelSecond (2*physicalRate q branch+1) (Real.cosh d)

private theorem radialLegendre_derivatives (q : XiZeroCopy) (branch : Bool) (d : ℝ) :
    HasDerivAt (radialLegendre q branch) (radialLegendreFirst q branch d) d ∧
    HasDerivAt (radialLegendreFirst q branch) (radialLegendreSecond q branch d) d := by
  obtain ⟨h,h1⟩ := legendreKernel_derivatives (2*physicalRate q branch+1) (Real.cosh_pos d)
  have hp : HasDerivAt (radialLegendre q branch) (radialLegendreFirst q branch d) d := by
    simpa only [radialLegendre,radialLegendreFirst,Function.comp_def,Complex.real_smul] using!
      h.scomp d (Real.hasDerivAt_cosh d)
  refine ⟨hp,?_⟩
  have hg : HasDerivAt (fun r => legendreKernelFirst (2*physicalRate q branch+1) (Real.cosh r))
      ((Real.sinh d:ℂ)*legendreKernelSecond (2*physicalRate q branch+1) (Real.cosh d)) d := by
    simpa only [Function.comp_def,Complex.real_smul] using h1.scomp d (Real.hasDerivAt_cosh d)
  apply (((Real.hasDerivAt_sinh d).ofReal_comp).mul hg).congr_deriv
  dsimp [radialLegendreSecond]
  ring

private theorem radialLegendre_equation (q : XiZeroCopy) (branch : Bool) (d : ℝ) :
    (Real.sinh d:ℂ)*radialLegendreSecond q branch d+
      (Real.cosh d:ℂ)*radialLegendreFirst q branch d=
      parameter q branch*(Real.sinh d:ℂ)*radialLegendre q branch d := by
  have he := legendreKernel_equation (2*physicalRate q branch+1) (Real.cosh_pos d)
  have hc : (Real.cosh d:ℂ)^(2 : ℕ)-(Real.sinh d:ℂ)^(2 : ℕ)=1 := by
    exact_mod_cast Real.cosh_sq_sub_sinh_sq d
  rw [parameter_physicalRate]
  dsimp [radialLegendre,radialLegendreFirst,radialLegendreSecond,D4BMQuadraticMixedSource.resolventParameter]
  linear_combination (Real.sinh d:ℂ)*he-
    (Real.sinh d:ℂ)*legendreKernelSecond (2*physicalRate q branch+1) (Real.cosh d)*hc

/-- The actual circular Green current, with both derivatives taken from the constructed functions. -/
def greenCurrent (q : XiZeroCopy) (branch : Bool) (d x k : ℝ) : ℂ :=
  (Real.sinh d:ℂ)*(radialLegendre q branch d*deriv (fun r => angularMean q branch r x k) d-
    deriv (radialLegendre q branch) d*angularMean q branch d x k)

private theorem legendre_first_eq (q : XiZeroCopy) (branch : Bool) :
    deriv (radialLegendre q branch)=radialLegendreFirst q branch :=
  funext (fun d => (radialLegendre_derivatives q branch d).1.deriv)

private theorem greenCurrent_continuous (q : XiZeroCopy) (branch : Bool) (x k : ℝ) :
    Continuous (fun d => greenCurrent q branch d x k) := by
  have hp : Continuous (radialLegendre q branch) :=
    continuous_iff_continuousAt.mpr (fun d => (radialLegendre_derivatives q branch d).1.continuousAt)
  have hp1 : Continuous (radialLegendreFirst q branch) :=
    continuous_iff_continuousAt.mpr (fun d => (radialLegendre_derivatives q branch d).2.continuousAt)
  have hm := angularMean_smooth q branch x k
  have hm1 := smooth_derivative hm
  simp only [greenCurrent,legendre_first_eq]
  exact (Complex.continuous_ofReal.comp Real.continuous_sinh).mul ((hp.mul hm1.continuous).sub (hp1.mul hm.continuous))

/-- The complete response current differentiates to a literal-source integral density. -/
theorem greenCurrent_hasDerivAt (q : XiZeroCopy) (branch : Bool) (x k d : ℝ) (hd : d ≠ 0) :
    HasDerivAt (fun r => greenCurrent q branch r x k)
      (parameter q branch*(Real.sinh d:ℂ)*radialLegendre q branch d*D4BMNativeCircle.mean q d x k) d := by
  have hm := angularMean_smooth q branch x k
  have hm1 := smooth_derivative hm
  have hmD := (hm.differentiable (by simp) d).hasDerivAt
  have hm1D := (hm1.differentiable (by simp) d).hasDerivAt
  obtain ⟨hp,hp1⟩ := radialLegendre_derivatives q branch d
  have h := ((Real.hasDerivAt_sinh d).ofReal_comp).mul
    ((hp.mul hm1D).sub (hp1.mul hmD))
  have hmE := angularMean_forced q branch d x k
  have hpE := radialLegendre_equation q branch d
  have hs : (Real.sinh d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sinh_ne_zero.mpr hd)
  have hmean : (Real.sinh d:ℂ)*deriv (deriv (fun r => angularMean q branch r x k)) d+
      (Real.cosh d:ℂ)*deriv (fun r => angularMean q branch r x k) d=
      parameter q branch*(Real.sinh d:ℂ)*
        (angularMean q branch d x k+D4BMNativeCircle.mean q d x k) := by
    apply mul_left_cancel₀ hs
    linear_combination hmE
  simp only [greenCurrent,legendre_first_eq]
  apply h.congr_deriv
  simp only [Pi.sub_apply,Pi.mul_apply]
  linear_combination radialLegendre q branch d*hmean-angularMean q branch d x k*hpE

/-- Finite-radius transfer evaluates the full response current in the unchanged theta source.
No nonvanishing assumption on the Legendre kernel or zero angular boundary datum is required. -/
theorem greenCurrent_finite_integral (q : XiZeroCopy) (branch : Bool) (x k D : ℝ) (hD : 0 ≤ D) :
    greenCurrent q branch D x k=parameter q branch*
      ∫ d in (0:ℝ)..D, (Real.sinh d:ℂ)*radialLegendre q branch d*D4BMNativeCircle.mean q d x k := by
  have hp : Continuous (radialLegendre q branch) :=
    continuous_iff_continuousAt.mpr (fun d => (radialLegendre_derivatives q branch d).1.continuousAt)
  have hc : Continuous (fun d => (Real.sinh d:ℂ)*radialLegendre q branch d*D4BMNativeCircle.mean q d x k) :=
    ((Complex.continuous_ofReal.comp Real.continuous_sinh).mul hp).mul (D4BMNativeCircle.mean_radial_smooth q x k).continuous
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hD
    (greenCurrent_continuous q branch x k).continuousOn
    (fun d hd => greenCurrent_hasDerivAt q branch x k d (ne_of_gt hd.1))
    (show IntervalIntegrable (fun d => parameter q branch*(Real.sinh d:ℂ)*
        radialLegendre q branch d*D4BMNativeCircle.mean q d x k) volume 0 D from by
      simpa only [mul_assoc] using
        (hc.const_mul (parameter q branch)).intervalIntegrable (μ := volume) 0 D)
  have hzero : greenCurrent q branch 0 x k=0 := by simp [greenCurrent]
  rw [hzero,sub_zero] at hi
  rw [← hi,← intervalIntegral.integral_const_mul]
  congr 1
  funext d
  ring

open D4BMJointSource

/-- The full-response coefficient in the original onset pulse, with the original clock. -/
def onsetResponseCoefficient (q : XiZeroCopy) (branch : Bool) (a : ℂ) (τ t : ℝ) : ℂ :=
  -2*sourceSeedFieldFirst (physicalRate q branch) 0 a 1 (parameter q branch) t*
    ((deriv Real.smoothTransition (τ+t):ℝ):ℂ)*Complex.exp (2*physicalRate q branch*(τ+t:ℝ))

/-- The literal half-square coefficient in the original onset pulse. -/
def onsetSourceCoefficient (q : XiZeroCopy) (branch : Bool) (a : ℂ) (τ t : ℝ) : ℂ :=
  2*parameter q branch*radialLiftFirst (physicalRate q branch) 0 a 1 t*
    ((deriv Real.smoothTransition (τ+t):ℝ):ℂ)*Complex.exp (2*physicalRate q branch*(τ+t:ℝ))

/-- Circular propagation data of the original, unprojected onset pulse. -/
def onsetAngularMean (q : XiZeroCopy) (branch : Bool) (a : ℂ) (τ t d x k : ℝ) : ℂ :=
  D4BMNativeCircle.average (fun theta => fullSourceOnsetPulse q branch a τ t (logCircle d theta x k))

/-- The unchanged onset pulse has exactly the two retained circular channels. -/
theorem onsetAngularMean_eq (q : XiZeroCopy) (branch : Bool) (a : ℂ) (τ t d x k : ℝ) :
    onsetAngularMean q branch a τ t d x k=
      onsetResponseCoefficient q branch a τ t*angularMean q branch d x k+
      onsetSourceCoefficient q branch a τ t*D4BMNativeCircle.mean q d x k := by
  have hq : Continuous (fun theta => D4BMNativeCircle.source q d theta x k) := by
    have hs := (D4BMNativeCircle.source_smooth q).comp
      (show ContDiff ℝ ∞ (fun theta : ℝ => ![d,theta,x,k]) by
        apply contDiff_pi.mpr
        intro i
        fin_cases i
        · change ContDiff ℝ ∞ (fun _ : ℝ => d)
          exact contDiff_const
        · change ContDiff ℝ ∞ (fun theta : ℝ => theta)
          exact contDiff_id
        · change ContDiff ℝ ∞ (fun _ : ℝ => x)
          exact contDiff_const
        · change ContDiff ℝ ∞ (fun _ : ℝ => k)
          exact contDiff_const)
    exact hs.continuous
  have he : (fun theta => fullSourceOnsetPulse q branch a τ t (logCircle d theta x k))=
      fun theta => onsetResponseCoefficient q branch a τ t*angularSource q branch d theta x k+
        onsetSourceCoefficient q branch a τ t*D4BMNativeCircle.source q d theta x k := by
    funext theta
    rw [fullSourceOnsetPulse_transition]
    dsimp [onsetResponseCoefficient,onsetSourceCoefficient,angularSource,D4BMNativeCircle.source]
    ring
  rw [onsetAngularMean,he,average_add
    ((theta_smooth q branch d x k).continuous.const_mul _) (hq.const_mul _),
    average_const_mul,average_const_mul]
  rfl

private theorem onsetAngularMean_derivative (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ t d x k : ℝ) :
    deriv (fun r => onsetAngularMean q branch a τ t r x k) d=
      onsetResponseCoefficient q branch a τ t*deriv (fun r => angularMean q branch r x k) d+
      onsetSourceCoefficient q branch a τ t*deriv (fun r => D4BMNativeCircle.mean q r x k) d := by
  have hh := ((angularMean_smooth q branch x k).differentiable (by simp) d).hasDerivAt
  have hq := ((D4BMNativeCircle.mean_radial_smooth q x k).differentiable (by simp) d).hasDerivAt
  have he : (fun r => onsetAngularMean q branch a τ t r x k)=
      fun r => onsetResponseCoefficient q branch a τ t*angularMean q branch r x k+
        onsetSourceCoefficient q branch a τ t*D4BMNativeCircle.mean q r x k :=
    funext (fun r => onsetAngularMean_eq q branch a τ t r x k)
  rw [he]
  exact ((hh.const_mul _).add (hq.const_mul _)).deriv

/-- The actual circular Green current of the original onset pulse. -/
def onsetGreenCurrent (q : XiZeroCopy) (branch : Bool) (a : ℂ) (τ t d x k : ℝ) : ℂ :=
  (Real.sinh d:ℂ)*(radialLegendre q branch d*deriv (fun r => onsetAngularMean q branch a τ t r x k) d-
    deriv (radialLegendre q branch) d*onsetAngularMean q branch a τ t d x k)

/-- The pulse's full-response channel transfers to the literal-source integral; the original
half-square current and fixed onset coefficient remain explicit. -/
theorem onsetGreenCurrent_transfer (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ t x k D : ℝ) (hD : 0 ≤ D) :
    onsetGreenCurrent q branch a τ t D x k=
      onsetResponseCoefficient q branch a τ t*parameter q branch*
        (∫ d in (0:ℝ)..D, (Real.sinh d:ℂ)*radialLegendre q branch d*D4BMNativeCircle.mean q d x k)+
      onsetSourceCoefficient q branch a τ t*(Real.sinh D:ℂ)*
        (radialLegendre q branch D*deriv (fun d => D4BMNativeCircle.mean q d x k) D-
          deriv (radialLegendre q branch) D*D4BMNativeCircle.mean q D x k) := by
  have he : onsetGreenCurrent q branch a τ t D x k=
      onsetResponseCoefficient q branch a τ t*greenCurrent q branch D x k+
      onsetSourceCoefficient q branch a τ t*(Real.sinh D:ℂ)*
        (radialLegendre q branch D*deriv (fun d => D4BMNativeCircle.mean q d x k) D-
          deriv (radialLegendre q branch) D*D4BMNativeCircle.mean q D x k) := by
    rw [onsetGreenCurrent,onsetAngularMean_derivative,onsetAngularMean_eq]
    dsimp [greenCurrent]
    ring
  rw [he,greenCurrent_finite_integral q branch x k D hD]
  ring

end
end RHTower.D4BMFullAngularCircle
