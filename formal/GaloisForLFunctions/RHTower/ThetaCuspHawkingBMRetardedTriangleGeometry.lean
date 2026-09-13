import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalRiemannKernel
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PrimeGammaReesEventGerm
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Exact smooth radius coordinates for both original causal source triangles. -/

open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RHTower.D4BMRetardedTriangleGeometry
open HTGeometry.ConstraintMotiveRelativity D4BMCausalKernel


@[fun_prop] theorem sinhc_smooth : ContDiff ℝ ∞ sinhc := by
  have hd : Differentiable ℂ (dslope Complex.sinh 0) := by
    apply differentiableOn_univ.mp
    rw [Complex.differentiableOn_dslope Filter.univ_mem]
    exact Complex.differentiable_sinh.differentiableOn
  have hc := (hd.contDiff : ContDiff ℂ ∞ (dslope Complex.sinh 0)).real_of_complex
  convert! hc using 1
  funext x
  by_cases hx : x = 0
  · subst x
    simp [dslope_same, Complex.deriv_sinh]
  · have hz : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    simp [sinhc,hx,dslope_of_ne _ hz,slope_def_field,← Complex.ofReal_sinh,
      ← Complex.ofReal_div]

def sourceB (image : Bool) (p r alpha beta : ℝ) : ℝ :=
  p*alpha+(if image then p-p*alpha else r-p*alpha)*beta

def triangleInvariant (image : Bool) (p r alpha beta : ℝ) : ℝ :=
  invariant ((p+r-p*alpha-sourceB image p r alpha beta)/2) ((p-r)/2)
    (if image then -(p*alpha-sourceB image p r alpha beta)/2
      else (p*alpha-sourceB image p r alpha beta)/2)

def positiveFactor (image : Bool) (p r alpha beta : ℝ) : ℝ :=
  p*(r-p*alpha)*
    (if image then sinhc ((p-p*alpha)*(1-beta)/2)*sinhc ((r-p*alpha)/2)
      else sinhc ((p-p*alpha)/2)*sinhc ((r-p*alpha)*(1-beta)/2))/
    (4*Real.cosh ((p-r)/2)*Real.cosh ((p*alpha-sourceB image p r alpha beta)/2))

def edgeWeight (alpha beta : ℝ) : ℝ := Real.sqrt ((1-alpha)*(1-beta))

def smoothRadius (image : Bool) (p r alpha beta c : ℝ) : ℝ :=
  2*Real.arsinh (c*Real.sqrt (positiveFactor image p r alpha beta))

private theorem cosh_difference (u v : ℝ) :
    Real.cosh u-Real.cosh v=
      2*Real.sinh ((u+v)/2)*Real.sinh ((u-v)/2) := by
  have h1 := Real.cosh_add ((u+v)/2) ((u-v)/2)
  have h2 := Real.cosh_sub ((u+v)/2) ((u-v)/2)
  rw [show (u+v)/2+(u-v)/2=u by ring] at h1
  rw [show (u+v)/2-(u-v)/2=v by ring] at h2
  linear_combination h1-h2

private theorem invariant_minus_one (h x y : ℝ) :
    invariant h x y-1=
      2*Real.sinh ((h+(x-y))/2)*Real.sinh ((h-(x-y))/2)/
        (Real.cosh x*Real.cosh y) := by
  rw [← cosh_difference]
  unfold invariant
  rw [Real.cosh_sub]
  field_simp
  ring

theorem triangleInvariant_factor (image : Bool) (p r alpha beta : ℝ) :
    triangleInvariant image p r alpha beta-1=
      2*((1-alpha)*(1-beta))*positiveFactor image p r alpha beta := by
  unfold triangleInvariant
  rw [invariant_minus_one]
  cases image
  · simp only [Bool.false_eq_true,↓reduceIte]
    rw [show ((p+r-p*alpha-sourceB false p r alpha beta)/2+
      ((p-r)/2-(p*alpha-sourceB false p r alpha beta)/2))/2=(p-p*alpha)/2 by ring,
      show ((p+r-p*alpha-sourceB false p r alpha beta)/2-
      ((p-r)/2-(p*alpha-sourceB false p r alpha beta)/2))/2=
      (r-p*alpha)*(1-beta)/2 by unfold sourceB; simp only [Bool.false_eq_true,↓reduceIte]; ring]
    rw [← sinhc_mul ((p-p*alpha)/2),← sinhc_mul ((r-p*alpha)*(1-beta)/2)]
    unfold positiveFactor
    simp only [Bool.false_eq_true,↓reduceIte]
    ring
  · simp only [↓reduceIte]
    rw [show ((p+r-p*alpha-sourceB true p r alpha beta)/2+
      ((p-r)/2- -(p*alpha-sourceB true p r alpha beta)/2))/2=
      (p-p*alpha)*(1-beta)/2 by unfold sourceB; simp only [↓reduceIte]; ring,
      show ((p+r-p*alpha-sourceB true p r alpha beta)/2-
      ((p-r)/2- -(p*alpha-sourceB true p r alpha beta)/2))/2=(r-p*alpha)/2 by ring]
    rw [← sinhc_mul ((p-p*alpha)*(1-beta)/2),← sinhc_mul ((r-p*alpha)/2)]
    unfold positiveFactor
    simp only [↓reduceIte]
    rw [neg_div,Real.cosh_neg]
    ring

theorem positiveFactor_pos (image : Bool) {p r alpha : ℝ}
    (hp : 0 < p) (hpr : p < r) (ha : alpha ≤ 1) (beta : ℝ) :
    0 < positiveFactor image p r alpha beta := by
  have hD : 0 < r-p*alpha := by
    have := mul_le_mul_of_nonneg_left ha hp.le
    nlinarith
  unfold positiveFactor
  apply div_pos
  · apply mul_pos (mul_pos hp hD)
    cases image <;> simp only [Bool.false_eq_true,↓reduceIte]
    all_goals exact mul_pos (sinhc_pos _) (sinhc_pos _)
  · exact mul_pos (mul_pos (by norm_num) (Real.cosh_pos _)) (Real.cosh_pos _)

theorem triangle_radius (image : Bool) {p r alpha beta : ℝ}
    (hp : 0 < p) (hpr : p < r) (ha : alpha ≤ 1) (hb : beta ≤ 1) :
    Real.arcosh (max 1 (triangleInvariant image p r alpha beta))=
      smoothRadius image p r alpha beta (edgeWeight alpha beta) := by
  have hprod : 0 ≤ (1-alpha)*(1-beta) := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  have hH := positiveFactor_pos image hp hpr ha beta
  have he : (edgeWeight alpha beta)^2=(1-alpha)*(1-beta) := Real.sq_sqrt hprod
  have hv : 0 ≤ edgeWeight alpha beta*Real.sqrt (positiveFactor image p r alpha beta) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hc : Real.cosh (smoothRadius image p r alpha beta (edgeWeight alpha beta))=
      triangleInvariant image p r alpha beta := by
    unfold smoothRadius
    rw [Real.cosh_two_mul,Real.cosh_arsinh,Real.sinh_arsinh,
      Real.sq_sqrt (by positivity : 0 ≤ 1+(edgeWeight alpha beta*Real.sqrt (positiveFactor image p r alpha beta))^2),
      mul_pow,he,Real.sq_sqrt hH.le]
    linear_combination -(triangleInvariant_factor image p r alpha beta)
  have hge : 1 ≤ triangleInvariant image p r alpha beta := by
    rw [← hc]
    exact Real.one_le_cosh _
  rw [max_eq_right hge,← hc,Real.arcosh_cosh]
  exact mul_nonneg (by norm_num) (Real.arsinh_nonneg_iff.mpr hv)

@[fun_prop] theorem sourceB_smooth (image : Bool) :
    ContDiff ℝ ∞ (fun z : Fin 4 → ℝ => sourceB image (z 0) (z 1) (z 2) (z 3)) := by
  cases image <;> dsimp [sourceB] <;> fun_prop

@[fun_prop] theorem positiveFactor_smooth (image : Bool) :
    ContDiff ℝ ∞ (fun z : Fin 4 → ℝ => positiveFactor image (z 0) (z 1) (z 2) (z 3)) := by
  cases image <;> dsimp [positiveFactor,sourceB]
  all_goals
    apply ContDiff.div
    · fun_prop
    · fun_prop
    · intro z
      exact mul_ne_zero (mul_ne_zero (by norm_num) (Real.cosh_pos _).ne') (Real.cosh_pos _).ne'

def logarithmicRadius (image : Bool) (z : Fin 4 → ℝ) : ℝ :=
  smoothRadius image (Real.exp (z 0)) (Real.exp (z 0)+Real.exp (z 1))
    (Real.sin (z 2)^2) (Real.sin (z 3)^2) (Real.cos (z 2)*Real.cos (z 3))

theorem logarithmicRadius_smooth (image : Bool) : ContDiff ℝ ∞ (logarithmicRadius image) := by
  have hH : ContDiff ℝ ∞ (fun z : Fin 4 → ℝ =>
      positiveFactor image (Real.exp (z 0)) (Real.exp (z 0)+Real.exp (z 1))
        (Real.sin (z 2)^2) (Real.sin (z 3)^2)) := by
    exact (positiveFactor_smooth image).comp
      (show ContDiff ℝ ∞ (fun z : Fin 4 → ℝ =>
        ![Real.exp (z 0),Real.exp (z 0)+Real.exp (z 1),Real.sin (z 2)^2,Real.sin (z 3)^2]) by
        apply contDiff_pi.mpr
        intro i
        fin_cases i <;> dsimp <;> fun_prop)
  have hn (z : Fin 4 → ℝ) :
      positiveFactor image (Real.exp (z 0)) (Real.exp (z 0)+Real.exp (z 1))
        (Real.sin (z 2)^2) (Real.sin (z 3)^2) ≠ 0 :=
    (positiveFactor_pos image (Real.exp_pos _) (by linarith [Real.exp_pos (z 1)])
      (Real.sin_sq_le_one _) _).ne'
  have hr := hH.sqrt hn
  have hc : ContDiff ℝ ∞ (fun z : Fin 4 → ℝ => Real.cos (z 2)*Real.cos (z 3)) := by fun_prop
  unfold logarithmicRadius smoothRadius
  exact contDiff_const.mul (Real.contDiff_arsinh.comp (hc.mul hr))

def angleMap (t : ℝ) : ℝ := Real.arcsin (Real.sqrt t)

theorem angleMap_continuous : Continuous angleMap :=
  Real.continuous_arcsin.comp Real.continuous_sqrt

theorem angleMap_sine_square {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    Real.sin (angleMap t)^2=t := by
  unfold angleMap
  rw [Real.sin_arcsin (le_trans (by norm_num) (Real.sqrt_nonneg t))
    (Real.sqrt_le_one.mpr ht.2),Real.sq_sqrt ht.1]

theorem angleMap_cosine {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    Real.cos (angleMap t)=Real.sqrt (1-t) := by
  unfold angleMap
  rw [Real.cos_arcsin,Real.sq_sqrt ht.1]

theorem logarithmicRadius_eq (image : Bool) {p r alpha beta : ℝ}
    (hp : 0 < p) (hpr : p < r) (ha : alpha ∈ Icc (0:ℝ) 1) (hb : beta ∈ Icc (0:ℝ) 1) :
    logarithmicRadius image ![Real.log p,Real.log (r-p),angleMap alpha,angleMap beta]=
      Real.arcosh (max 1 (triangleInvariant image p r alpha beta)) := by
  rw [triangle_radius image hp hpr ha.2 hb.2]
  change smoothRadius image (Real.exp (Real.log p)) (Real.exp (Real.log p)+Real.exp (Real.log (r-p)))
    (Real.sin (angleMap alpha)^2) (Real.sin (angleMap beta)^2)
    (Real.cos (angleMap alpha)*Real.cos (angleMap beta))=_
  rw [Real.exp_log hp,Real.exp_log (sub_pos.mpr hpr),
    show p+(r-p)=r by ring,angleMap_sine_square ha,angleMap_sine_square hb,
    angleMap_cosine ha,angleMap_cosine hb]
  congr 1
  exact (Real.sqrt_mul (sub_nonneg.mpr ha.2) (1-beta)).symm

end RHTower.D4BMRetardedTriangleGeometry
