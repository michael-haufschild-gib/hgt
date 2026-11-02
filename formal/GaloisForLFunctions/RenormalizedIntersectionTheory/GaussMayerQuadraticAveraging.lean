import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringNormalization
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! A reciprocal Cauchy change of variable converts a quadratic lattice
weight into a linear one. Its two reciprocal branches combine to the
ordinary Cauchy measure. -/

open Complex Set MeasureTheory
open scoped FourierTransform
open GaloisForLFunctions.RenormalizedIntersectionTheory
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerQuadraticAveraging

/-- The increasing coordinate joining the two reciprocal quadratic branches. -/
private def cauchyChart (a b t : ℝ) : ℝ := (a*t-b/t)/(a+b)

private def chartJac (a b t : ℝ) : ℝ := (a+b/t^2)/(a+b)

private theorem chart_hasDeriv {a b t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (cauchyChart a b) (chartJac a b t) t := by
  have h := (((hasDerivAt_id t).const_mul a).sub
    ((hasDerivAt_inv ht).const_mul b)).div_const (a+b)
  unfold cauchyChart chartJac
  simpa only [id_eq,Pi.sub_apply,mul_one,mul_neg,sub_neg_eq_add,div_eq_mul_inv] using! h

private theorem chartJac_pos {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < chartJac a b t := by
  unfold chartJac
  exact div_pos (add_pos_of_pos_of_nonneg ha (div_nonneg hb.le (sq_nonneg t))) (add_pos ha hb)

private theorem chart_injective {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    InjOn (cauchyChart a b) (Ioi 0) := by
  apply StrictMonoOn.injOn
  intro x hx y hy hxy
  have hi : b/y < b/x := div_lt_div_of_pos_left hb hx hxy
  have hl : a*x < a*y := mul_lt_mul_of_pos_left hxy ha
  exact (div_lt_div_iff_of_pos_right (add_pos ha hb)).mpr (sub_lt_sub hl hi)

private theorem chart_image {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    cauchyChart a b '' Ioi 0=univ := by
  apply Set.eq_univ_of_forall
  intro v
  let c := (a+b)*v
  let d := Real.sqrt (c^2+4*a*b)
  have hab : 0 < a*b := mul_pos ha hb
  have hd2 : d^2=c^2+4*a*b := Real.sq_sqrt (by nlinarith only [sq_nonneg c,hab])
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hdc : |c| < d := by
    nlinarith only [sq_abs c,abs_nonneg c,hd2,hd0,hab]
  have hnum : 0 < c+d := by
    have hc := neg_le_abs c
    linarith only [hc,hdc]
  let t := (c+d)/(2*a)
  have ht : 0 < t := div_pos hnum (mul_pos (by norm_num) ha)
  have htEq : 2*a*t=c+d := by dsimp [t]; field_simp
  have hquad : a*t^2-c*t-b=0 := by
    have h := hd2
    rw [show d=2*a*t-c by linarith only [htEq]] at h
    have hfact : 4*a*(a*t^2-c*t-b)=0 := by nlinarith only [h]
    exact (mul_eq_zero.mp hfact).resolve_left (mul_ne_zero (by norm_num) ha.ne')
  refine ⟨t,ht,?_⟩
  unfold cauchyChart
  apply (div_eq_iff (add_pos ha hb).ne').mpr
  field_simp [ht.ne']
  dsimp [c] at hquad
  linear_combination hquad

/-- The quadratic product is a square times the Cauchy denominator. -/
private theorem quadratic_factorization (a b t : ℝ) (ht : t ≠ 0) :
    (1+t^2)*(b^2+a^2*t^2)=t^2*((a*t-b/t)^2+(a+b)^2) := by
  field_simp
  ring

/-- Reciprocal reflection becomes ordinary reflection in the Cauchy coordinate. -/
private theorem chart_reciprocal {a b t : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) :
    cauchyChart a b (b/(a*t))= -cauchyChart a b t := by
  unfold cauchyChart
  field_simp
  ring

/-- The sum of the two reciprocal weights is the pulled-back Cauchy measure. -/
private theorem cauchy_weight_sum {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    (1+t^2)⁻¹+a*b/(a^2*t^2+b^2)=
      chartJac a b t/(1+(cauchyChart a b t)^2) := by
  have hab : a+b ≠ 0 := (add_pos ha hb).ne'
  have hd : a^2*t^2+b^2 ≠ 0 := ne_of_gt (by positivity)
  have hc : 1+(cauchyChart a b t)^2 ≠ 0 := ne_of_gt (by positivity)
  have ht1 : 1+t^2 ≠ 0 := ne_of_gt (by positivity)
  unfold chartJac cauchyChart at *
  field_simp
  ring


private def leftWeight (t : ℝ) : ℝ := (1+t^2)⁻¹
private def rightWeight (a b t : ℝ) : ℝ := a*b/(a^2*t^2+b^2)

private theorem reciprocal_hasDeriv {a b t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun y : ℝ => b/(a*y)) (-(b/a)/t^2) t := by
  have h := (hasDerivAt_inv ht).const_mul (b/a)
  have he : (fun y : ℝ => b/(a*y))=fun y => (b/a)*y⁻¹ := by
    funext y
    simp only [div_eq_mul_inv,mul_inv]
    ring
  rw [he]
  have hj : -(b/a)/t^2=(b/a)*(-(t^2)⁻¹) := by ring
  rw [hj]
  exact h

private theorem reciprocal_image {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (fun t : ℝ => b/(a*t)) '' Ioi 0=Ioi 0 := by
  ext y
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact div_pos hb (mul_pos ha ht)
  · intro hy
    refine ⟨b/(a*y),div_pos hb (mul_pos ha hy),?_⟩
    field_simp

private theorem reciprocal_injective {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    InjOn (fun t : ℝ => b/(a*t)) (Ioi 0) := by
  intro x hx y hy he
  have h := congrArg (fun t : ℝ => b/(a*t)) he
  have hcancel (t : ℝ) (ht : 0 < t) : b/(a*(b/(a*t)))=t := by field_simp
  rwa [hcancel x hx,hcancel y hy] at h

private theorem reciprocal_weight {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    |-(b/a)/t^2| * leftWeight (b/(a*t))=rightWeight a b t := by
  have hj : 0 < (b/a)/t^2 := div_pos (div_pos hb ha) (sq_pos_of_pos ht)
  rw [neg_div,abs_neg,abs_of_pos hj]
  unfold leftWeight rightWeight
  field_simp

private theorem reciprocal_average {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (g : ℝ → ℂ) (he : ∀ v, g (-v)=g v) :
    (∫ t in Ioi (0 : ℝ), leftWeight t • g (cauchyChart a b t))=
      ∫ t in Ioi (0 : ℝ), rightWeight a b t • g (cauchyChart a b t) := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (f := fun t : ℝ => b/(a*t)) (f' := fun t => -(b/a)/t^2)
    measurableSet_Ioi (fun t ht => (reciprocal_hasDeriv (ne_of_gt ht)).hasDerivWithinAt)
    (reciprocal_injective ha hb) (fun t => leftWeight t • g (cauchyChart a b t))
  rw [reciprocal_image ha hb] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [chart_reciprocal ha.ne' hb.ne' (ne_of_gt ht),he,smul_smul,reciprocal_weight ha hb ht]

private theorem reciprocal_average_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (g : ℝ → ℂ) (he : ∀ v, g (-v)=g v)
    (hi : IntegrableOn (fun t => leftWeight t • g (cauchyChart a b t)) (Ioi 0)) :
    IntegrableOn (fun t => rightWeight a b t • g (cauchyChart a b t)) (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (f := fun t : ℝ => b/(a*t)) (f' := fun t => -(b/a)/t^2)
    measurableSet_Ioi (fun t ht => (reciprocal_hasDeriv (ne_of_gt ht)).hasDerivWithinAt)
    (reciprocal_injective ha hb) (fun t => leftWeight t • g (cauchyChart a b t))
  rw [reciprocal_image ha hb] at h
  refine (h.mp hi).congr_fun ?_ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [chart_reciprocal ha.ne' hb.ne' (ne_of_gt ht),he,smul_smul,reciprocal_weight ha hb ht]

/-- Reciprocal symmetrization turns an even Cauchy mean into a half-line mean. -/
private theorem cauchy_average {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (g : ℝ → ℂ) (hg : Measurable g) (he : ∀ v, g (-v)=g v)
    (hi : Integrable (fun v => leftWeight v • g v)) :
    IntegrableOn (fun t => leftWeight t • g (cauchyChart a b t)) (Ioi 0) ∧
      2*(∫ t in Ioi (0 : ℝ), leftWeight t • g (cauchyChart a b t))=
        ∫ v : ℝ, leftWeight v • g v := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (f := cauchyChart a b) (f' := chartJac a b)
    measurableSet_Ioi (fun t ht => (chart_hasDeriv (ne_of_gt ht)).hasDerivWithinAt)
    (chart_injective ha hb) (fun v => leftWeight v • g v)
  have hint := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (f := cauchyChart a b) (f' := chartJac a b)
    measurableSet_Ioi (fun t ht => (chart_hasDeriv (ne_of_gt ht)).hasDerivWithinAt)
    (chart_injective ha hb) (fun v => leftWeight v • g v)
  rw [chart_image ha hb,setIntegral_univ] at hchange
  rw [chart_image ha hb,integrableOn_univ] at hint
  have hpoint (t : ℝ) (ht : 0 < t) :
      |chartJac a b t| • (leftWeight (cauchyChart a b t) • g (cauchyChart a b t))=
        (leftWeight t+rightWeight a b t) • g (cauchyChart a b t) := by
    rw [abs_of_pos (chartJac_pos ha hb),smul_smul]
    congr 1
    exact (cauchy_weight_sum ha hb ht).symm
  have hJ : IntegrableOn (fun t => (leftWeight t+rightWeight a b t) •
      g (cauchyChart a b t)) (Ioi 0) :=
    (hint.mp hi).congr_fun hpoint measurableSet_Ioi
  have hleft : IntegrableOn (fun t => leftWeight t • g (cauchyChart a b t)) (Ioi 0) := by
    refine hJ.norm.mono' (by unfold leftWeight cauchyChart; fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hl : 0 ≤ leftWeight t := by unfold leftWeight; positivity
    have hr : 0 ≤ rightWeight a b t := by unfold rightWeight; positivity
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hl,abs_of_nonneg (add_nonneg hl hr)]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hr) (norm_nonneg _)
  have hright := reciprocal_average_integrable ha hb g he hleft
  refine ⟨hleft,?_⟩
  have hsum : (∫ t in Ioi (0 : ℝ), (leftWeight t+rightWeight a b t) •
      g (cauchyChart a b t))=
        (∫ t in Ioi (0 : ℝ), leftWeight t • g (cauchyChart a b t))+
          ∫ t in Ioi (0 : ℝ), rightWeight a b t • g (cauchyChart a b t) := by
    simp_rw [add_smul]
    exact integral_add hleft hright
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint,hsum,
    ← reciprocal_average ha hb g he] at hchange
  linear_combination -hchange



private def cauchyWave (w : ℂ) (v : ℝ) : ℂ :=
  ((1+v^2 : ℝ) : ℂ)^(-w/2)

private def cauchyPower (w : ℂ) (v : ℝ) : ℂ :=
  ((1+v^2 : ℝ) : ℂ)^(-((w+2)/2))

private theorem cauchyPower_eq (w : ℂ) (v : ℝ) :
    leftWeight v • cauchyWave w v=cauchyPower w v := by
  have hn : ((1+v^2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  rw [leftWeight,cauchyWave,cauchyPower,Complex.real_smul,Complex.ofReal_inv,
    ← Complex.cpow_neg_one,← Complex.cpow_add _ _ hn]
  congr 1
  ring

private def cauchyParameter (w : ℂ) (hw : 2 < w.re) :
    _root_.RHTower.D4BMEisensteinAbsoluteConvergenceParameter where
  s := (w+2)/2
  re_gt_one := by norm_num [Complex.add_re,Complex.div_re]; linarith only [hw]

private theorem cauchyPower_kernel {w : ℂ} (hw : 2 < w.re) :
    cauchyPower w=_root_.RHTower.d4BMCauchyPowerKernel
      MayerScatteringNormalization.basePoint (cauchyParameter w hw).s := by
  funext v
  simp only [cauchyPower,_root_.RHTower.d4BMCauchyPowerKernel,
    MayerScatteringNormalization.basePoint,cauchyParameter,one_pow]

private theorem cauchyPower_integrable {w : ℂ} (hw : 2 < w.re) :
    Integrable (cauchyPower w) := by
  rw [cauchyPower_kernel hw]
  exact _root_.RHTower.integrable_d4BMCauchyPowerKernel
    MayerScatteringNormalization.basePoint (cauchyParameter w hw)

private theorem cauchyPower_integral {w : ℂ} (hw : 2 < w.re) :
    (∫ v : ℝ, cauchyPower w v)=MayerScatteringNormalization.archimedeanFactor ((w+2)/2) := by
  have h := MayerScatteringNormalization.kernel_normalization (cauchyParameter w hw)
  rw [← cauchyPower_kernel hw] at h
  simpa [Real.fourier_eq,cauchyParameter] using! h

/-- Exact half-line Cauchy mean of the quadratic wave after the reciprocal change of variable. -/
private theorem cauchyWave_average {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {w : ℂ} (hw : 2 < w.re) :
    IntegrableOn (fun t => leftWeight t • cauchyWave w (cauchyChart a b t)) (Ioi 0) ∧
      2*(∫ t in Ioi (0 : ℝ), leftWeight t • cauchyWave w (cauchyChart a b t))=
        MayerScatteringNormalization.archimedeanFactor ((w+2)/2) := by
  have hg : Measurable (cauchyWave w) := by unfold cauchyWave; fun_prop
  have he (v : ℝ) : cauchyWave w (-v)=cauchyWave w v := by simp only [cauchyWave,neg_sq]
  have hq : (fun v => leftWeight v • cauchyWave w v)=cauchyPower w :=
    funext (cauchyPower_eq w)
  have hi : Integrable (fun v => leftWeight v • cauchyWave w v) := by
    rw [hq]
    exact cauchyPower_integrable hw
  have h := cauchy_average ha hb (cauchyWave w) hg he hi
  rw [hq,cauchyPower_integral hw] at h
  exact h


/-- The single lattice term in the quadratic averaging integral. -/
def quadraticIntegrand (w : ℂ) (a b t : ℝ) : ℂ :=
  (t : ℂ)^w/(((1+t^2 : ℝ) : ℂ)^((w+2)/2)*((b^2+a^2*t^2 : ℝ) : ℂ)^(w/2))

private theorem square_cpow {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    ((x^2 : ℝ) : ℂ)^s=(x : ℂ)^(2*s) := by
  have h := Complex.cpow_mul_ofReal_nonneg hx (2 : ℝ) s
  rw [show x^(2 : ℝ)=x^2 from Real.rpow_natCast x 2] at h
  exact h.symm

/-- Pointwise conversion to the Cauchy mean; every power has a positive real base. -/
private theorem quadraticIntegrand_eq {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (w : ℂ) :
    quadraticIntegrand w a b t=((a+b : ℝ) : ℂ)^(-w)*
      (leftWeight t • cauchyWave w (cauchyChart a b t)) := by
  have hU : 0 < 1+t^2 := by positivity
  have hV : 0 < b^2+a^2*t^2 := by positivity
  have hC : 0 < 1+(cauchyChart a b t)^2 := by positivity
  have hS : 0 < a+b := add_pos ha hb
  have hUn : ((1+t^2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU.ne'
  have he : (1+t^2)*(b^2+a^2*t^2)=t^2*(a+b)^2*(1+(cauchyChart a b t)^2) := by
    rw [quadratic_factorization a b t ht.ne']
    unfold cauchyChart
    field_simp [hS.ne']
    ring
  have hprod : ((1+t^2 : ℝ) : ℂ)^(w/2)*((b^2+a^2*t^2 : ℝ) : ℂ)^(w/2)=
      (t : ℂ)^w*((a+b : ℝ) : ℂ)^w*((1+(cauchyChart a b t)^2 : ℝ) : ℂ)^(w/2) := by
    calc
      _ = (((1+t^2)*(b^2+a^2*t^2) : ℝ) : ℂ)^(w/2) := by
        rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hU.le hV.le]
      _ = ((t^2*(a+b)^2*(1+(cauchyChart a b t)^2) : ℝ) : ℂ)^(w/2) := by rw [he]
      _ = _ := by
        rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg
          (mul_nonneg (sq_nonneg t) (sq_nonneg (a+b))) hC.le,
          Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (sq_nonneg t) (sq_nonneg (a+b)),
          square_cpow ht.le,square_cpow hS.le,show (2 : ℂ)*(w/2)=w by ring]
  have hshift : ((1+t^2 : ℝ) : ℂ)^((w+2)/2)=
      ((1+t^2 : ℝ) : ℂ)*((1+t^2 : ℝ) : ℂ)^(w/2) := by
    rw [show (w+2)/2=1+w/2 by ring,Complex.cpow_add _ _ hUn,Complex.cpow_one]
  have htP : (t : ℂ)^w ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr ht.ne'))
  have hsP : ((a+b : ℝ) : ℂ)^w ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hS.ne'))
  have hcP : ((1+(cauchyChart a b t)^2 : ℝ) : ℂ)^(w/2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hC.ne'))
  rw [quadraticIntegrand,hshift,mul_assoc,hprod]
  simp only [leftWeight,cauchyWave,Complex.real_smul,Complex.ofReal_inv,
    show -w/2= -(w/2) by ring,Complex.cpow_neg]
  field_simp [hUn,htP,hsP,hcP]

/-- Absolute convergence of the actual single-term quadratic average. -/
theorem quadraticIntegrand_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {w : ℂ} (hw : 2 < w.re) : IntegrableOn (quadraticIntegrand w a b) (Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ => ((a+b : ℝ) : ℂ)^(-w) •
      (leftWeight t • cauchyWave w (cauchyChart a b t))) (Ioi 0) :=
    (cauchyWave_average ha hb hw).1.smul (((a+b : ℝ) : ℂ)^(-w))
  refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Ioi
  intro t ht
  exact (quadraticIntegrand_eq ha hb ht w).symm

/-- Exact quadratic-to-linear averaging of one positive lattice term. -/
theorem quadratic_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {w : ℂ} (hw : 2 < w.re) :
    (∫ t in Ioi (0 : ℝ), quadraticIntegrand w a b t)=
      (MayerScatteringNormalization.archimedeanFactor ((w+2)/2)/2)*((a+b : ℝ) : ℂ)^(-w) := by
  have h := (cauchyWave_average ha hb hw).2
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => quadraticIntegrand_eq ha hb ht w),
    integral_const_mul]
  linear_combination (((a+b : ℝ) : ℂ)^(-w)/2)*h


#print axioms quadratic_factorization
#print axioms chart_reciprocal
#print axioms cauchy_weight_sum
#print axioms cauchy_average
#print axioms cauchyWave_average
#print axioms quadraticIntegrand_integrable
#print axioms quadratic_integral
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerQuadraticAveraging
