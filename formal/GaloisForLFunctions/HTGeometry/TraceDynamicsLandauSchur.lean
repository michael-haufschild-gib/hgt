import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity

/-!
# Sharp Landau stability and critical Schur modes

Positive self-couplings admit an exact copositivity threshold and a nonzero flat boundary
direction. Actual derivatives distinguish secondary mass shifts from mixed Gaussian
curvature. A heavy positive channel yields a classified Schur-complement zero mode.

Source: Singh, arXiv:2609.10571, section 5.3 and equation (82).
-/

set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry.TraceDynamics
noncomputable section

/-- Two invariant amplitudes with intrinsically positive self-couplings. -/
def landauQuartic (u v κ x y : ℝ) : ℝ :=
  (Real.exp u)^2*x^4 + (Real.exp v)^2*y^4 + κ*x^2*y^2

theorem landauQuartic_square_decomposition (u v κ x y : ℝ) :
    landauQuartic u v κ x y = (Real.exp u*x^2 - Real.exp v*y^2)^2 +
      (κ + 2*Real.exp u*Real.exp v)*x^2*y^2 := by
  unfold landauQuartic
  ring

/-- Sharp copositivity threshold, including its flat boundary. -/
theorem landauQuartic_nonnegative_iff (u v κ : ℝ) :
    (∀ x y, 0 ≤ landauQuartic u v κ x y) ↔ -2*Real.exp (u+v) ≤ κ := by
  rw [Real.exp_add]
  constructor
  · intro h
    have hx := Real.sq_sqrt (Real.exp_pos v).le
    have hy := Real.sq_sqrt (Real.exp_pos u).le
    have hn := h (Real.sqrt (Real.exp v)) (Real.sqrt (Real.exp u))
    rw [landauQuartic_square_decomposition, hx, hy] at hn
    have hprod : 0 < Real.exp v * Real.exp u := mul_pos (Real.exp_pos _) (Real.exp_pos _)
    have hval : 0 ≤ (κ + 2*Real.exp u*Real.exp v)*(Real.exp v*Real.exp u) := by
      nlinarith [hn]
    have := (mul_nonneg_iff_of_pos_right hprod).mp hval
    linarith
  · intro h x y
    rw [landauQuartic_square_decomposition]
    apply add_nonneg (sq_nonneg _)
    exact mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (sq_nonneg _)

/-- The obstruction to stability provides an explicit nonzero flat direction at equality. -/
theorem landauQuartic_boundary_flat (u v : ℝ) :
    landauQuartic u v (-2*Real.exp (u+v))
      (Real.sqrt (Real.exp v)) (Real.sqrt (Real.exp u)) = 0 := by
  rw [landauQuartic_square_decomposition, Real.exp_add,
    Real.sq_sqrt (Real.exp_pos v).le, Real.sq_sqrt (Real.exp_pos u).le]
  ring

theorem landauQuartic_unstable_iff (u v κ : ℝ) :
    (∃ x y, landauQuartic u v κ x y < 0) ↔ κ < -2*Real.exp (u+v) := by
  have h := not_congr (landauQuartic_nonnegative_iff u v κ)
  push Not at h
  exact h

def landauPotential (r s u v κ x y : ℝ) : ℝ :=
  r*x^2+s*y^2+landauQuartic u v κ x y

theorem hasDerivAt_landauPotential_left (r s u v κ x y : ℝ) :
    HasDerivAt (fun z => landauPotential r s u v κ z y)
      (2*x*(r+κ*y^2+2*(Real.exp u)^2*x^2)) x := by
  unfold landauPotential landauQuartic
  apply (((((hasDerivAt_id x).pow 2).const_mul r).add
    (hasDerivAt_const x (s*y^2))).add
    (((((hasDerivAt_id x).pow 4).const_mul ((Real.exp u)^2)).add
      (hasDerivAt_const x ((Real.exp v)^2*y^4))).add
      ((((hasDerivAt_id x).pow 2).const_mul κ).mul_const (y^2)))).congr_deriv
  dsimp
  ring

/-- Quartic cross-coupling shifts secondary curvature away from the symmetric origin. -/
theorem landau_secondary_curvature (r s u v κ y : ℝ) :
    deriv (fun x => deriv (fun z => landauPotential r s u v κ z y) x) 0 =
      2*(r+κ*y^2) := by
  simp_rw [(hasDerivAt_landauPotential_left r s u v κ _ y).deriv]
  have h : HasDerivAt (fun x : ℝ => 2*x*(r+κ*y^2+2*(Real.exp u)^2*x^2))
      (2*(r+κ*y^2)) 0 := by
    apply (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul
      ((hasDerivAt_const 0 (r+κ*y^2)).add
        (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (2*(Real.exp u)^2)))).congr_deriv
    dsimp
    ring
  exact h.deriv

/-- All quartic cross-couplings leave the mixed Gaussian entry zero at the origin. -/
theorem landau_mixed_origin (r s u v κ : ℝ) :
    deriv (fun y => deriv (fun x => landauPotential r s u v κ x y) 0) 0 = 0 := by
  simp_rw [(hasDerivAt_landauPotential_left r s u v κ 0 _).deriv]
  simp

/-- A heavy channel with positive stiffness and an arbitrary mixed coupling. -/
def heavyChannelQuadratic (a b c x y : ℝ) : ℝ :=
  Real.exp a*x^2 + 2*b*x*y + c*y^2

/-- Integrating out the heavy coordinate leaves the exact Schur-complement stiffness. -/
theorem heavyChannel_square_decomposition (a b c x y : ℝ) :
    heavyChannelQuadratic a b c x y =
      Real.exp a*(x+b/Real.exp a*y)^2 + (c-b^2/Real.exp a)*y^2 := by
  unfold heavyChannelQuadratic
  field_simp [(Real.exp_pos a).ne']
  ring

theorem heavyChannel_nonnegative_iff (a b c : ℝ) :
    (∀ x y, 0 ≤ heavyChannelQuadratic a b c x y) ↔ b^2/Real.exp a ≤ c := by
  constructor
  · intro h
    have hn := h (-b/Real.exp a) 1
    rw [heavyChannel_square_decomposition] at hn
    have hh : -b/Real.exp a+b/Real.exp a*1 = 0 := by ring
    rw [hh] at hn
    nlinarith
  · intro h x y
    rw [heavyChannel_square_decomposition]
    exact add_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
      (mul_nonneg (sub_nonneg.mpr h) (sq_nonneg _))

/-- At critical Schur stiffness the complete zero set is a single line. -/
theorem heavyChannel_critical_zero_iff (a b x y : ℝ) :
    heavyChannelQuadratic a b (b^2/Real.exp a) x y = 0 ↔ x = -b/Real.exp a*y := by
  rw [heavyChannel_square_decomposition, sub_self, zero_mul, add_zero]
  rw [mul_eq_zero]
  simp only [(Real.exp_pos a).ne', false_or, sq_eq_zero_iff]
  rw [neg_div]
  constructor <;> intro h <;> linarith

/-- The canonical critical mode is mixed precisely when the cross-coupling is nonzero. -/
theorem heavyChannel_critical_mode_mixed_iff (a b : ℝ) :
    (-b/Real.exp a ≠ 0 ∧ (1 : ℝ) ≠ 0) ↔ b ≠ 0 := by
  simp [(Real.exp_pos a).ne']

end
end GaloisForLFunctions.HTGeometry.TraceDynamics
