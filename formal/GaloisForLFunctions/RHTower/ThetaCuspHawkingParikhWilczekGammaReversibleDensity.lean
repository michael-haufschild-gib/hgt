import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusReflectedFrullani
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Reversible density of the actual Gamma-source jump directions

The forward and reciprocal displacement rates have one reversible density up to
scale on the positive ray. The reciprocal rate retains its actual Jacobian.
The explicit density is integrable and inversion-invariant, and its original-source
weight agrees exactly with the existing singular gain in logarithmic coordinates.

These are density-level results. Integral substitution, complete operator domains,
retained cutoff corrections and spectral Ward balance require separate proofs.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology
noncomputable section

def pwGammaForwardJumpRate (x y : ℝ) : ℝ := Real.exp (-(y-x))/(y-x)
def pwGammaBackwardJumpRate (y x : ℝ) : ℝ :=
  (y/x)*Real.exp (-(x⁻¹-y⁻¹))/(y-x)
def pwGammaReversibleDensity (x : ℝ) : ℝ := Real.exp (-x-x⁻¹)/x
def pwGammaReversibleSourceDensity (x : ℝ) : ℝ := Real.exp (x-x⁻¹)/x^(2 : ℕ)

theorem pwGammaReversibleDensity_pos {x : ℝ} (hx : 0<x) :
    0 < pwGammaReversibleDensity x := div_pos (Real.exp_pos _) hx

theorem pwGammaForwardJumpRate_pos {x y : ℝ} (hxy : x<y) :
    0 < pwGammaForwardJumpRate x y := div_pos (Real.exp_pos _) (sub_pos.mpr hxy)

theorem pwGammaReversibleDensity_forward {x y : ℝ} :
    pwGammaReversibleDensity x * pwGammaForwardJumpRate x y =
      Real.exp (-y-x⁻¹)/(x*(y-x)) := by
  rw [pwGammaReversibleDensity, pwGammaForwardJumpRate, div_mul_div_comm, ← Real.exp_add]
  congr 2
  ring

theorem pwGammaReversibleDensity_backward {x y : ℝ} (hy : y≠0) :
    pwGammaReversibleDensity y * pwGammaBackwardJumpRate y x =
      Real.exp (-y-x⁻¹)/(x*(y-x)) := by
  unfold pwGammaReversibleDensity pwGammaBackwardJumpRate
  have he : Real.exp (-y-y⁻¹)*Real.exp (-(x⁻¹-y⁻¹)) = Real.exp (-y-x⁻¹) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-y-y⁻¹)*Real.exp (-(x⁻¹-y⁻¹)))/(x*(y-x)) := by
      field_simp
    _ = _ := by rw [he]

theorem pwGammaReversibleDensity_detailedBalance {x y : ℝ} (hy : y≠0) :
    pwGammaReversibleDensity x * pwGammaForwardJumpRate x y =
      pwGammaReversibleDensity y * pwGammaBackwardJumpRate y x := by
  rw [pwGammaReversibleDensity_forward, pwGammaReversibleDensity_backward hy]

theorem pwGammaReversibleDensity_inv {x : ℝ} (hx : x≠0) :
    pwGammaReversibleDensity x⁻¹ / x^(2 : ℕ) = pwGammaReversibleDensity x := by
  unfold pwGammaReversibleDensity
  rw [inv_inv, show -x⁻¹-x = -x-x⁻¹ by ring]
  field_simp

theorem pwGammaReversibleSourceDensity_source {x : ℝ} (hx : 0<x) :
    pwGammaReversibleSourceDensity x * ‖pwGammaRaySource x‖^(2 : ℕ) =
      pwGammaReversibleDensity x := by
  rw [pwGammaRaySource_eq hx, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    mul_pow, Real.sq_sqrt hx.le, pwGammaReversibleSourceDensity, pwGammaReversibleDensity]
  have he : Real.exp (x-x⁻¹)*Real.exp (-x)^(2 : ℕ) = Real.exp (-x-x⁻¹) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (x-x⁻¹)*Real.exp (-x)^(2 : ℕ))/x := by field_simp
    _ = _ := by rw [he]

theorem pwGammaReversibleSourceDensity_log (t : ℝ) :
    pwGammaReversibleSourceDensity (Real.exp t)*Real.exp t = pwLogSingularGain t := by
  unfold pwGammaReversibleSourceDensity pwLogSingularGain pwLogSingularGaugePotential
  rw [Real.sinh_eq, Real.exp_neg]
  have h : Real.exp (Real.exp t - (Real.exp t)⁻¹) / Real.exp t =
      Real.exp (2*((Real.exp t-(Real.exp t)⁻¹)/2-t/2)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  calc
    _ = Real.exp (Real.exp t-(Real.exp t)⁻¹)/Real.exp t := by field_simp
    _ = _ := h

theorem pwGammaReversibleDensity_le_exp {x : ℝ} (_hx : 0<x) :
    pwGammaReversibleDensity x ≤ Real.exp (-x) := by
  have h := (Real.mul_exp_neg_le_exp_neg_one x⁻¹).trans
    (Real.exp_le_one_iff.mpr (by linarith : (-1:ℝ)≤0))
  unfold pwGammaReversibleDensity
  calc
    _ = Real.exp (-x) * (x⁻¹*Real.exp (-x⁻¹)) := by
      rw [sub_eq_add_neg, Real.exp_add, div_eq_mul_inv]
      ring
    _ ≤ Real.exp (-x) := mul_le_of_le_one_right (Real.exp_pos _).le h

theorem pwGammaReversibleDensity_integrable :
    IntegrableOn pwGammaReversibleDensity (Ioi 0) := by
  have hc : ContinuousOn pwGammaReversibleDensity (Ioi 0) := by
    have hi : ContinuousOn (fun x : ℝ => x) (Ioi (0:ℝ)) := continuousOn_id
    exact (hi.neg.sub (hi.inv₀ (fun x hx => ne_of_gt hx))).rexp.div
      hi (fun x hx => ne_of_gt hx)
  apply (integrableOn_exp_neg_Ioi 0).mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_of_nonneg (pwGammaReversibleDensity_pos hx).le]
  exact pwGammaReversibleDensity_le_exp hx

theorem pwGammaReversibleDensity_ratio_forced {rho : ℝ → ℝ}
    (hbalance : ∀ x y : ℝ, 0<x → x<y →
      rho x*pwGammaForwardJumpRate x y = rho y*pwGammaBackwardJumpRate y x)
    {x y : ℝ} (hx : 0<x) (hxy : x<y) :
    rho x/pwGammaReversibleDensity x = rho y/pwGammaReversibleDensity y := by
  have hy := hx.trans hxy
  apply (div_eq_div_iff (pwGammaReversibleDensity_pos hx).ne'
    (pwGammaReversibleDensity_pos hy).ne').mpr
  apply mul_right_cancel₀ (pwGammaForwardJumpRate_pos hxy).ne'
  calc
    _ = (rho x*pwGammaForwardJumpRate x y)*pwGammaReversibleDensity y := by ring
    _ = (rho y*pwGammaBackwardJumpRate y x)*pwGammaReversibleDensity y := by
      rw [hbalance x y hx hxy]
    _ = rho y*(pwGammaReversibleDensity y*pwGammaBackwardJumpRate y x) := by ring
    _ = rho y*(pwGammaReversibleDensity x*pwGammaForwardJumpRate x y) := by
      rw [← pwGammaReversibleDensity_detailedBalance hy.ne']
    _ = _ := by ring

theorem pwGammaReversibleDensity_unique {rho : ℝ → ℝ}
    (hbalance : ∀ x y : ℝ, 0<x → x<y →
      rho x*pwGammaForwardJumpRate x y = rho y*pwGammaBackwardJumpRate y x) :
    ∃ c : ℝ, ∀ x : ℝ, 0<x → rho x=c*pwGammaReversibleDensity x := by
  refine ⟨rho 1/pwGammaReversibleDensity 1, ?_⟩
  intro x hx
  have he : rho x/pwGammaReversibleDensity x = rho 1/pwGammaReversibleDensity 1 := by
    rcases lt_trichotomy x 1 with h | rfl | h
    · exact pwGammaReversibleDensity_ratio_forced hbalance hx h
    · rfl
    · exact (pwGammaReversibleDensity_ratio_forced hbalance zero_lt_one h).symm
  exact (div_eq_iff (pwGammaReversibleDensity_pos hx).ne').mp he

/-- Actual reciprocal displacement derivative, before applying change of variables. -/
theorem pwGammaBackwardJump_displacement_hasDerivAt {x : ℝ} (hx : x≠0) (y : ℝ) :
    HasDerivAt (fun u : ℝ => u⁻¹-y⁻¹) (-(x^(2 : ℕ))⁻¹) x :=
  (hasDerivAt_inv hx).sub_const _

/-- The backward rate retains the reciprocal displacement's Jacobian. -/
theorem pwGammaBackwardJumpRate_changeOfVariables {x y : ℝ} (hx : 0<x) (hxy : x<y) :
    Real.exp (-(x⁻¹-y⁻¹))/(x⁻¹-y⁻¹)*(x^(2 : ℕ))⁻¹ = pwGammaBackwardJumpRate y x := by
  have hy := hx.trans hxy
  have hd : x⁻¹-y⁻¹≠0 := sub_ne_zero.mpr (inv_injective.ne hxy.ne)
  unfold pwGammaBackwardJumpRate
  field_simp [hx.ne', hy.ne', hd]

end
end RHTower
