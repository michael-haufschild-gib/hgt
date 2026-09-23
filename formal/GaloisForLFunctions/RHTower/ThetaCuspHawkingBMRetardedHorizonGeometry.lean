import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRetardedTriangleGeometry
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeField
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceHorizonFactor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Exact compact coordinates of the original retarded source at the future horizon. -/
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
namespace RHTower.D4BMRetardedHorizonGeometry
open D4BMCausalKernel D4BMJointSource D4BMLaplaceRadial D4BMRetardedTriangleGeometry
open HTGeometry.ConstraintMotiveRelativity

/-- Positive removable exponential quotient, including its characteristic value. -/
def expc (t : ℝ) : ℝ := Real.exp (t/2)*sinhc (t/2)

@[fun_prop] theorem expc_smooth : ContDiff ℝ ∞ expc := by
  unfold expc
  have h : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (t/2)) := by fun_prop
  exact h.mul (sinhc_smooth.comp (by fun_prop))

theorem expc_pos (t : ℝ) : 0 < expc t := mul_pos (Real.exp_pos _) (sinhc_pos _)

theorem expc_mul (t : ℝ) : t*expc t=Real.exp t-1 := by
  have h := sinhc_mul (t/2)
  unfold expc
  rw [show t*(Real.exp (t/2)*sinhc (t/2))=2*Real.exp (t/2)*(sinhc (t/2)*(t/2)) by ring]
  rw [h,Real.sinh_eq,Real.exp_neg]
  have he : Real.exp t=Real.exp (t/2)^(2 : ℕ) := by
    calc
      Real.exp t=Real.exp (t/2+t/2) := congrArg Real.exp (by ring)
      _=Real.exp (t/2)^(2 : ℕ) := by rw [Real.exp_add,pow_two]
  rw [he]
  field_simp

/-- Source radial coordinate, regular on the whole half-line `-1 < z`. -/
def compactUnit (z : ℝ) : ℝ := (1-z)/(1+z)

theorem radialUnit_compact (y : ℝ) : radialUnit y=compactUnit (Real.exp (2*y)) := by
  apply (eq_div_iff (ne_of_gt (by positivity : 0<1+Real.exp (2*y)))).mpr
  have h := radialUnit_one_sub y
  nlinarith

def compactInvariant (image : Bool) (E rho z : ℝ) : ℝ :=
  1+2*(if image then (E-rho)*(z-1/E) else (E-1)*(z-rho/E))/((1+rho)*(1+z))

/-- Both actual invariant kernels in the same physical compact source coordinate. -/
theorem invariant_compact (image : Bool) (v x y : ℝ) :
    invariant (v-x+y) x (if image then -y else y)=
      compactInvariant image (Real.exp v) (Real.exp (2*x)) (Real.exp (2*y)) := by
  have hx : Real.exp (2*x)=Real.exp x^(2 : ℕ) := by rw [two_mul,Real.exp_add,pow_two]
  have hy : Real.exp (2*y)=Real.exp y^(2 : ℕ) := by rw [two_mul,Real.exp_add,pow_two]
  have hxp := Real.exp_pos x
  have hyp := Real.exp_pos y
  have hvp := Real.exp_pos v
  have hx2 : 1+Real.exp x^(2 : ℕ) ≠ 0 := ne_of_gt (by positivity)
  have hy2 : 1+Real.exp y^(2 : ℕ) ≠ 0 := ne_of_gt (by positivity)
  cases image
  · simp only [compactInvariant,Bool.false_eq_true,↓reduceIte,hx,hy,invariant,
      Real.cosh_eq,Real.sinh_eq,Real.exp_add,Real.exp_sub,Real.exp_neg]
    field_simp
    ring
  · simp only [compactInvariant,↓reduceIte,hx,hy,invariant]
    rw [Real.cosh_neg,Real.sinh_neg]
    simp only [Real.cosh_eq,Real.sinh_eq,Real.exp_add,Real.exp_sub,Real.exp_neg]
    field_simp
    ring

/-- Complete source density after cancelling the logarithmic Jacobian. -/
def compactForcing (s amp : ℂ) (a z : ℝ) (J K : ℂ) : ℂ :=
  -8*(compactUnit z:ℂ)/(1+(z:ℂ))^(2 : ℕ)*power (2*s) (2/(1+z))*amp^(2 : ℕ)*
    (((5*s^(2 : ℕ)+15*s+4)/4)*J+s*(s-1)*(compactUnit z:ℂ)^(2 : ℕ)/4*((s+2)^(2 : ℕ)*J-K))*
    timeOnset (2*s) a

theorem originalForcing_compact (s amp J K : ℂ) (tau y : ℝ) :
    originalForcing s 0 amp 1 J K y*timeOnset (2*s) (tau+y)=
      (Real.exp (2*y):ℂ)*compactForcing s amp (tau+y) (Real.exp (2*y)) J K := by
  have hz : (1+(Real.exp (2*y):ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : 0<1+Real.exp (2*y)))
  have hp : 1+radialUnit y=2/(1+Real.exp (2*y)) := by
    rw [radialUnit_compact,compactUnit]
    field_simp
    ring
  have hc : 1-(radialUnit y:ℂ)^(2 : ℕ)=4*(Real.exp (2*y):ℂ)/(1+(Real.exp (2*y):ℂ))^(2 : ℕ) := by
    rw [radialUnit_compact]
    simp only [compactUnit,Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_add,
      Complex.ofReal_one]
    field_simp [hz]
    ring
  rw [originalForcing,sourceAmplitude,hp,hc]
  simp only [zero_mul,Complex.exp_zero,one_mul,mul_one,radialUnit_compact]
  unfold compactForcing
  ring

/-- The original forcing, with its full gradient field and fixed onset retained. -/
theorem timeOriginalForcing_compact (q : RHTower.XiZeroCopy) (branch : Bool) (amp : ℂ)
    (a b : ℝ) (point : D4BMHorizon.Point) :
    timeOriginalForcing q branch amp ((a+b)/2) ((a-b)/2) point=
      (Real.exp (a-b):ℂ)*compactForcing (D4BMModularCore.physicalRate q branch) amp a
        (Real.exp (a-b)) (D4BMModularCore.fullSquarePotential q point)
        (D4BMModularCore.fullGradientEnergy q point/2) := by
  unfold timeOriginalForcing
  rw [originalForcing_compact,show 2*((a-b)/2)=a-b by ring,
    show (a+b)/2+(a-b)/2=a by ring]

/-- Compact source lower endpoint for each of the two original causal triangles. -/
def sourceLower (image : Bool) (p rho alpha : ℝ) : ℝ :=
  (if image then 1 else rho)*Real.exp (-(p*(1-alpha)))

def sourceZ (image : Bool) (p rho alpha beta : ℝ) : ℝ :=
  sourceLower image p rho alpha+(1-sourceLower image p rho alpha)*beta

/-- The positive factor left after extracting the characteristic square root. -/
def horizonFactor (image : Bool) (p rho alpha beta : ℝ) : ℝ :=
  p*expc (p*(1-alpha))*(1-rho*Real.exp (-(p*(1-alpha))))/
    ((1+rho)*(1+sourceZ image p rho alpha beta))

theorem sourceZ_add_one_pos (image : Bool) {p rho alpha beta : ℝ}
    (hp : 0 ≤ p) (hr : -(1/2:ℝ)<rho) (ha : alpha ≤ 1)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) :
    0 < 1+sourceZ image p rho alpha beta := by
  have he : Real.exp (-(p*(1-alpha))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hp (sub_nonneg.mpr ha)))
  have he0 := Real.exp_pos (-(p*(1-alpha)))
  have hL : -(1/2:ℝ)<sourceLower image p rho alpha := by
    unfold sourceLower
    cases image <;> simp only [Bool.false_eq_true,↓reduceIte,one_mul]
    · by_cases hr0 : 0 ≤ rho
      · exact lt_of_lt_of_le (by norm_num) (mul_nonneg hr0 he0.le)
      · have := mul_le_mul_of_nonpos_left he (le_of_not_ge hr0)
        nlinarith
    · linarith
  have hf : 0 ≤ (1-beta)*(sourceLower image p rho alpha+1/2) :=
    mul_nonneg (sub_nonneg.mpr hb1) (by linarith)
  unfold sourceZ
  nlinarith

theorem horizonFactor_pos (image : Bool) {p rho alpha beta : ℝ}
    (hp : 0 < p) (hr0 : -(1/2:ℝ)<rho) (hr1 : rho < 1/2)
    (ha : alpha ≤ 1) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) :
    0 < horizonFactor image p rho alpha beta := by
  have he : Real.exp (-(p*(1-alpha))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hp.le (sub_nonneg.mpr ha)))
  have he0 := Real.exp_pos (-(p*(1-alpha)))
  have hn : 0 < 1-rho*Real.exp (-(p*(1-alpha))) := by
    by_cases hr : 0 ≤ rho
    · have := mul_le_mul_of_nonneg_left he hr
      nlinarith
    · have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hr) he0.le
      linarith
  exact div_pos (mul_pos (mul_pos hp (expc_pos _)) hn)
    (mul_pos (by linarith) (sourceZ_add_one_pos image hp.le hr0 ha hb0 hb1))

theorem compactInvariant_factor (image : Bool) (p rho alpha beta : ℝ) :
    compactInvariant image (Real.exp (p*(1-alpha))) rho (sourceZ image p rho alpha beta)-1=
      2*(1-alpha)*beta*horizonFactor image p rho alpha beta := by
  unfold compactInvariant horizonFactor
  rw [add_sub_cancel_left]
  rw [show 2*(1-alpha)*beta*(p*expc (p*(1-alpha))*(1-rho*Real.exp (-(p*(1-alpha))))/
      ((1+rho)*(1+sourceZ image p rho alpha beta)))=
      2*((p*(1-alpha))*expc (p*(1-alpha)))*beta*(1-rho*Real.exp (-(p*(1-alpha))))/
      ((1+rho)*(1+sourceZ image p rho alpha beta)) by ring,expc_mul]
  apply congrArg (fun n => n/((1+rho)*(1+sourceZ image p rho alpha beta)))
  unfold sourceZ sourceLower
  rw [Real.exp_neg]
  cases image <;> simp only [Bool.false_eq_true,↓reduceIte,one_mul]
  all_goals field_simp
  all_goals ring

/-- An open smooth chart crossing the physical future horizon at parameter zero. -/
def horizonChart (v : ℝ) : ℝ := (1-Real.exp v)/(2*(1+Real.exp v))

theorem horizonChart_bounds (v : ℝ) : -(1/2:ℝ)<horizonChart v ∧ horizonChart v<1/2 := by
  have hp := Real.exp_pos v
  unfold horizonChart
  constructor
  · apply (lt_div_iff₀ (by positivity)).mpr
    linarith
  · apply (div_lt_iff₀ (by positivity)).mpr
    linarith

@[fun_prop] theorem horizonChart_smooth : ContDiff ℝ ∞ horizonChart := by
  unfold horizonChart
  fun_prop (disch := intro x; positivity)

@[simp] theorem horizonChart_zero : horizonChart 0=0 := by simp [horizonChart]

def horizonRadius (image : Bool) (z : Fin 4 → ℝ) : ℝ :=
  2*Real.arsinh (Real.cos (z 2)*Real.sin (z 3)*
    Real.sqrt (horizonFactor image (Real.exp (z 0)) (horizonChart (z 1))
      (Real.sin (z 2)^(2 : ℕ)) (Real.sin (z 3)^(2 : ℕ))))

@[fun_prop] theorem sourceZ_chart_smooth (image : Bool) :
    ContDiff ℝ ∞ (fun z : Fin 4 → ℝ => sourceZ image (Real.exp (z 0))
      (horizonChart (z 1)) (Real.sin (z 2)^(2 : ℕ)) (Real.sin (z 3)^(2 : ℕ))) := by
  cases image <;> dsimp [sourceZ,sourceLower] <;> fun_prop

theorem sourceZ_chart_add_one_pos (image : Bool) (z : Fin 4 → ℝ) :
    0 < 1+sourceZ image (Real.exp (z 0)) (horizonChart (z 1))
      (Real.sin (z 2)^(2 : ℕ)) (Real.sin (z 3)^(2 : ℕ)) :=
  sourceZ_add_one_pos image (Real.exp_pos _).le (horizonChart_bounds _).1
    (Real.sin_sq_le_one _) (sq_nonneg _) (Real.sin_sq_le_one _)

@[fun_prop] theorem horizonFactor_chart_smooth (image : Bool) :
    ContDiff ℝ ∞ (fun z : Fin 4 → ℝ => horizonFactor image (Real.exp (z 0))
      (horizonChart (z 1)) (Real.sin (z 2)^(2 : ℕ)) (Real.sin (z 3)^(2 : ℕ))) := by
  have hn (z : Fin 4 → ℝ) :
      (1+horizonChart (z 1))*(1+sourceZ image (Real.exp (z 0)) (horizonChart (z 1))
        (Real.sin (z 2)^(2 : ℕ)) (Real.sin (z 3)^(2 : ℕ))) ≠ 0 :=
    mul_ne_zero (ne_of_gt (by linarith [(horizonChart_bounds (z 1)).1]))
      (sourceZ_chart_add_one_pos image z).ne'
  unfold horizonFactor
  fun_prop (disch := exact hn _)

@[fun_prop] theorem horizonRadius_smooth (image : Bool) : ContDiff ℝ ∞ (horizonRadius image) := by
  have hH (z : Fin 4 → ℝ) : 0 < horizonFactor image (Real.exp (z 0)) (horizonChart (z 1))
      (Real.sin (z 2)^(2 : ℕ)) (Real.sin (z 3)^(2 : ℕ)) :=
    horizonFactor_pos image (Real.exp_pos _) (horizonChart_bounds _).1 (horizonChart_bounds _).2
      (Real.sin_sq_le_one _) (sq_nonneg _) (Real.sin_sq_le_one _)
  have hs : ContDiff ℝ ∞ (fun z : Fin 4 → ℝ => Real.cos (z 2)*Real.sin (z 3)) := by fun_prop
  unfold horizonRadius
  exact contDiff_const.mul (Real.contDiff_arsinh.comp
    (hs.mul ((horizonFactor_chart_smooth image).sqrt (fun z => (hH z).ne'))))

/-- Actual circle radius on the closed square, including both characteristic edges. -/
theorem compact_radius (image : Bool) {p rho alpha beta : ℝ}
    (hp : 0<p) (hr0 : -(1/2:ℝ)<rho) (hr1 : rho<1/2)
    (ha : alpha ≤ 1) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) :
    Real.arcosh (max 1 (compactInvariant image (Real.exp (p*(1-alpha))) rho
      (sourceZ image p rho alpha beta)))=
      2*Real.arsinh (Real.sqrt ((1-alpha)*beta)*Real.sqrt (horizonFactor image p rho alpha beta)) := by
  have hw : 0 ≤ (1-alpha)*beta := mul_nonneg (sub_nonneg.mpr ha) hb0
  have hH := horizonFactor_pos image hp hr0 hr1 ha hb0 hb1
  have hc : Real.cosh (2*Real.arsinh
      (Real.sqrt ((1-alpha)*beta)*Real.sqrt (horizonFactor image p rho alpha beta)))=
      compactInvariant image (Real.exp (p*(1-alpha))) rho (sourceZ image p rho alpha beta) := by
    rw [Real.cosh_two_mul,Real.cosh_arsinh,Real.sinh_arsinh,
      Real.sq_sqrt (by positivity : 0 ≤ 1+(Real.sqrt ((1-alpha)*beta)*
        Real.sqrt (horizonFactor image p rho alpha beta))^(2 : ℕ)),
      mul_pow,Real.sq_sqrt hw,Real.sq_sqrt hH.le]
    linear_combination -(compactInvariant_factor image p rho alpha beta)
  rw [← hc,max_eq_right (Real.one_le_cosh _),Real.arcosh_cosh]
  exact mul_nonneg (by norm_num) (Real.arsinh_nonneg_iff.mpr (by positivity))

/-- The signed smooth chart equals the original nonnegative radius at its compact parameters. -/
theorem horizonRadius_eq (image : Bool) (u v : ℝ) {alpha beta : ℝ}
    (ha : alpha ∈ Icc (0:ℝ) 1) (hb : beta ∈ Icc (0:ℝ) 1) :
    horizonRadius image ![u,v,angleMap alpha,angleMap beta]=
      Real.arcosh (max 1 (compactInvariant image (Real.exp (Real.exp u*(1-alpha)))
        (horizonChart v) (sourceZ image (Real.exp u) (horizonChart v) alpha beta))) := by
  rw [compact_radius image (Real.exp_pos _) (horizonChart_bounds _).1
    (horizonChart_bounds _).2 ha.2 hb.1 hb.2]
  change 2*Real.arsinh (Real.cos (angleMap alpha)*Real.sin (angleMap beta)*
    Real.sqrt (horizonFactor image (Real.exp u) (horizonChart v)
      (Real.sin (angleMap alpha)^(2 : ℕ)) (Real.sin (angleMap beta)^(2 : ℕ))))=
    2*Real.arsinh (Real.sqrt ((1-alpha)*beta)*Real.sqrt (horizonFactor image
      (Real.exp u) (horizonChart v) alpha beta))
  rw [angleMap_sine_square ha,angleMap_sine_square hb,angleMap_cosine ha]
  have hs : Real.sin (angleMap beta)=Real.sqrt beta := by
    unfold angleMap
    exact Real.sin_arcsin (le_trans (by norm_num : (-1:ℝ)≤0) (Real.sqrt_nonneg beta)) ((Real.sqrt_le_one).mpr hb.2)
  rw [hs,Real.sqrt_mul (sub_nonneg.mpr ha.2)]

/-- Exact source-Jacobian cancellation under the original exponential coordinate change. -/
theorem integral_source_coordinate (F : ℝ → ℂ) (a B : ℝ) :
    (∫ b in a..B, (Real.exp (a-b):ℂ)*F (Real.exp (a-b)))=
      ∫ z in (Real.exp (a-B))..1, F z := by
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
    (f := fun b : ℝ => Real.exp (a-b)) (f' := fun b : ℝ => -Real.exp (a-b)) (g := F)
    (by fun_prop : ContinuousOn (fun b : ℝ => Real.exp (a-b)) (uIcc a B))
    (fun b _ => by simpa using ((hasDerivAt_const b a).sub (hasDerivAt_id b)).exp)
    (fun b _ => (neg_nonpos.mpr (Real.exp_pos _).le))
  simp only [Function.comp_apply,sub_self,Real.exp_zero,Complex.real_smul,
    Complex.ofReal_neg,neg_mul,intervalIntegral.integral_neg] at h
  rw [intervalIntegral.integral_symm (a := Real.exp (a-B)) (b := (1:ℝ))] at h
  exact neg_injective h

end RHTower.D4BMRetardedHorizonGeometry
