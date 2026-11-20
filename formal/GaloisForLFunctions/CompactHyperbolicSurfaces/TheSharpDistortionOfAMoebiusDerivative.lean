import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact derivative distortion for real Möbius maps

The conformal distortion estimate of Koskela–Li–Zhou–Zhu, Lemma 2.3,
specializes on the half-plane to an attained envelope for each Möbius
map. The Euclidean derivative norm is the quotient of the target and
source heights. Their logarithms each cost at most one hyperbolic
distance. For a nonaffine map both costs are attained on the vertical
line through its real pole.
-/

noncomputable section
open UpperHalfPlane Matrix
open scoped MatrixGroups
namespace GaloisForLFunctions.CompactHyperbolicSurfaces

/-- Euclidean length multiplier of a hyperbolic isometry. -/
def heightMultiplier (g : GL (Fin 2) ℝ) (z : ℍ) : ℝ := (g • z).im/z.im

private theorem multiplier_pos (g : GL (Fin 2) ℝ) (z : ℍ) : 0<heightMultiplier g z :=
  div_pos (g • z).im_pos z.im_pos

private theorem multiplier_formula (g : GL (Fin 2) ℝ) (z : ℍ) :
    heightMultiplier g z=|g.det.val|/Complex.normSq (denom g z) := by
  rw [heightMultiplier,im_smul_eq_div_normSq]
  field_simp [z.im_ne_zero,(normSq_denom_pos g z.im_ne_zero).ne']

/-- The actual complex derivative of an orientation-preserving
isometry has norm equal to the intrinsic height multiplier. -/
theorem moebius_derivative_height {g : GL (Fin 2) ℝ} (hg : 0<g.val.det) (z : ℍ) :
    ‖deriv (fun u : ℂ => (↑(g • ofComplex u):ℂ)) (z:ℂ)‖=heightMultiplier g z := by
  simp only [deriv_smul hg,multiplier_formula,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    Complex.normSq_eq_norm_sq,Matrix.GeneralLinearGroup.val_det_apply]

private theorem affine_constant {g : GL (Fin 2) ℝ} (hc : g 1 0=0) (z w : ℍ) :
    heightMultiplier g z=heightMultiplier g w := by
  simp only [multiplier_formula,denom,hc,Complex.ofReal_zero,zero_mul,zero_add]

-- Matching bottom rows makes the heights proportional for all points.
private theorem determinant_one_height (g : GL (Fin 2) ℝ) (hc : g 1 0≠0) :
    ∃ h : SL(2,ℝ), ∀ u : ℍ, (g • u).im=|g.det.val| *(h • u).im := by
  let h : SL(2,ℝ) := ⟨!![0, -(g 1 0)⁻¹; g 1 0, g 1 1],by simp [Matrix.det_fin_two,hc]⟩
  refine ⟨h,fun u => ?_⟩
  change (g • u).im=|g.det.val| *((SpecialLinearGroup.mapGL ℝ h) • u).im
  rw [im_smul_eq_div_normSq,im_smul_eq_div_normSq]
  have eq : denom (SpecialLinearGroup.mapGL ℝ h) u=denom g u := by
    simp [denom,h]
  rw [eq]
  simp [mul_div_assoc]

/-- The logarithmic multiplier changes by at most twice the total
hyperbolic displacement, for either orientation of the isometry. -/
theorem log_height_multiplier_transport (g : GL (Fin 2) ℝ) (z w : ℍ) :
    |Real.log (heightMultiplier g z)-Real.log (heightMultiplier g w)|≤2*dist z w := by
  by_cases hc : g 1 0=0
  · rw [affine_constant hc z w,sub_self,abs_zero]
    exact mul_nonneg (by norm_num) dist_nonneg
  obtain ⟨h,height⟩ := determinant_one_height g hc
  have hs := abs_le.mp (show |Real.log z.im-Real.log w.im|≤dist z w from dist_log_im_le z w)
  have gt := dist_log_im_le (h • z) (h • w)
  rw [Real.dist_eq,dist_smul] at gt
  have ht := abs_le.mp gt
  have price (u : ℍ) : Real.log (heightMultiplier g u)=
      Real.log |g.det.val| + Real.log (h • u).im-Real.log u.im := by
    rw [heightMultiplier,Real.log_div (g • u).im_ne_zero u.im_ne_zero,height,
      Real.log_mul (abs_ne_zero.mpr g.det.ne_zero) (h • u).im_ne_zero]
  rw [price,price]
  apply abs_le.mpr
  constructor <;> linarith only [hs.1,hs.2,ht.1,ht.2]

private def verticalHeight (x t : ℝ) : ℍ := ⟨⟨x,Real.exp t⟩,Real.exp_pos t⟩

private theorem pole_norm (g : GL (Fin 2) ℝ) (hc : g 1 0≠0) (t : ℝ) :
    Complex.normSq (denom g (verticalHeight (-(g 1 1)/(g 1 0)) t))=(g 1 0*Real.exp t)^2 := by
  have cancel : g 1 0*(-(g 1 1)/(g 1 0))+g 1 1=0 := by
    field_simp [hc]
    ring
  have eq (z : ℍ) : Complex.normSq (denom g z)=(g 1 0*z.im)^2+(g 1 0*z.re+g 1 1)^2 := by
    simp [denom,Complex.normSq]
    ring
  rw [eq]
  change (g 1 0*Real.exp t)^2+(g 1 0*(-(g 1 1)/(g 1 0))+g 1 1)^2=_
  simp only [cancel,zero_pow (by decide : 2≠0),add_zero]

/-- At each prescribed distance the sharp multiplicative distortion
is attained. For a nonaffine matrix the two points above its pole
have heights one and exp D, respectively. -/
theorem height_multiplier_distortion_attained (g : GL (Fin 2) ℝ) {D : ℝ} (hD : 0≤D) :
    ∃ z w : ℍ, dist z w=D ∧
      heightMultiplier g z=(if g 1 0=0 then 1 else Real.exp (2*D))*heightMultiplier g w := by
  let x := -(g 1 1)/(g 1 0)
  let z := verticalHeight x 0
  let w := verticalHeight x D
  have travel : dist z w=D := by
    have h := (isometry_vertical_line x).dist_eq 0 D
    simpa only [z,w,verticalHeight,Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg hD] using h
  refine ⟨z,w,travel,?_⟩
  by_cases hc : g 1 0=0
  · rw [if_pos hc,one_mul,affine_constant hc z w]
  · rw [if_neg hc,multiplier_formula,multiplier_formula,pole_norm g hc,pole_norm g hc,
      Real.exp_zero,mul_one,mul_pow,show 2*D=D+D by ring,Real.exp_add]
    field_simp [hc,Real.exp_ne_zero D]

/-- Exact distortion constant for the complex derivative at fixed
displacement D. The affine branch costs one and every other matrix
costs exp(2D), even when that single matrix is fixed in advance. -/
theorem sharp_moebius_derivative_distortion {g : GL (Fin 2) ℝ} (hg : 0<g.val.det)
    {D : ℝ} (hD : 0≤D) (K : ℝ) :
    (∀ z w : ℍ, dist z w≤D →
      ‖deriv (fun u : ℂ => (↑(g • ofComplex u):ℂ)) (z:ℂ)‖≤
        K*‖deriv (fun u : ℂ => (↑(g • ofComplex u):ℂ)) (w:ℂ)‖) ↔
      (if g 1 0=0 then 1 else Real.exp (2*D))≤K := by
  simp only [moebius_derivative_height hg]
  constructor
  · intro bound
    obtain ⟨z,w,d,eq⟩ := height_multiplier_distortion_attained g hD
    have h := bound z w d.le
    rw [eq] at h
    exact le_of_mul_le_mul_right h (multiplier_pos g w)
  · intro cap z w distcap
    by_cases hc : g 1 0=0
    · rw [if_pos hc] at cap
      rw [affine_constant hc z w]
      exact le_mul_of_one_le_left (multiplier_pos g w).le cap
    · rw [if_neg hc] at cap
      have logbound := (le_abs_self _).trans (log_height_multiplier_transport g z w)
      have price : Real.log (heightMultiplier g z)≤2*D+Real.log (heightMultiplier g w) := by
        linarith only [logbound,distcap]
      have scaled := Real.exp_le_exp.mpr price
      rw [Real.exp_log (multiplier_pos g z),Real.exp_add,Real.exp_log (multiplier_pos g w)] at scaled
      exact scaled.trans (mul_le_mul_of_nonneg_right cap (multiplier_pos g w).le)

#print axioms moebius_derivative_height
#print axioms log_height_multiplier_transport
#print axioms height_multiplier_distortion_attained
#print axioms sharp_moebius_derivative_distortion
end GaloisForLFunctions.CompactHyperbolicSurfaces
