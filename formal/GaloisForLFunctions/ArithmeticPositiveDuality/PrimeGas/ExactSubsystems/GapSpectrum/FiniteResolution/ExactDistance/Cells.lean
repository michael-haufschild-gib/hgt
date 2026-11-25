import GaloisForLFunctions.HTGeometry.MidpointConvexIntegral
import GaloisForLFunctions.HTGeometry.ConvexIntegralTrapezoid
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Convex cell estimates for the prime-gas Gibbs weights -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GibbsTail

open Set MeasureTheory

/-- Unnormalized Gibbs weight at real label coordinate x. -/
def density (h : Ioi (0:ℝ)) (x : ℝ) := x^(-(1+h.val))

/-- Integral of the continuous Gibbs weight from x to infinity for positive x. -/
def primitive (h : Ioi (0:ℝ)) (x : ℝ) := x^(-h.val)/h.val

private theorem density_convex (h : Ioi (0:ℝ)) : StrictConvexOn ℝ (Ioi 0) (density h) := by
  have hs : -(1+h.val) < 0 := by linarith only [show 0 < h.val from h.property]
  unfold density
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0)
  · intro x hx
    exact (Real.continuousAt_rpow_const x _ (Or.inl hx.ne')).continuousWithinAt
  · intro x hx
    rw [Real.iter_deriv_rpow_const,descPochhammer_succ_eval 1,descPochhammer_one,Polynomial.eval_X,Nat.cast_one]
    exact mul_pos (mul_pos_of_neg_of_neg hs (by linarith only [hs])) (Real.rpow_pos_of_pos hx _)

private theorem convex_cell (h : Ioi (0:ℝ)) {a b : ℝ} (ha : 0 < a) :
    ConvexOn ℝ (Icc a b) (density h) :=
  (density_convex h).convexOn.subset (fun _ hx => ha.trans_le hx.1) (convex_Icc a b)

private theorem integrable_cell (h : Ioi (0:ℝ)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (density h) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro x hx
  exact (Real.continuousAt_rpow_const x _ (Or.inl (ha.trans_le hx.1).ne')).continuousWithinAt

theorem integral_density (h : Ioi (0:ℝ)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ y in a..b, density h y) = primitive h a-primitive h b := by
  have hz : (0:ℝ) ∉ uIcc a b := by rw [uIcc_of_le hab]; exact fun h0 => ha.not_ge h0.1
  unfold density primitive
  rw [integral_rpow (Or.inr ⟨by linarith only [show 0 < h.val from h.property],hz⟩),
    show -(1+h.val)+1 = -h.val by ring]
  ring

/-- The two half-cell trapezoids give a strict deficit against the full endpoint trapezoid. -/
theorem strict_trapezoid (h : Ioi (0:ℝ)) {a : ℝ} (ha : 0 < a) :
    primitive h a-primitive h (a+1) < (density h a+density h (a+1))/2 := by
  have hm : 0 < a+1/2 := by linarith only [ha]
  have hb : 0 < a+1 := by linarith only [ha]
  have h1 := GaloisForLFunctions.ConvexOn.integral_le_trapezoid (show a < a+1/2 by linarith)
    (convex_cell h ha) (integrable_cell h ha (by linarith))
  have h2 := GaloisForLFunctions.ConvexOn.integral_le_trapezoid (show a+1/2 < a+1 by linarith)
    (convex_cell h hm) (integrable_cell h hm (by linarith))
  have hs := (density_convex h).2 (show a ∈ Ioi (0:ℝ) from ha) (show a+1 ∈ Ioi (0:ℝ) from hb)
    (show a ≠ a+1 by linarith) (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (1/2:ℝ)+1/2 = 1)
  simp only [smul_eq_mul] at hs
  rw [show (1/2:ℝ)*a+1/2*(a+1) = a+1/2 by ring] at hs
  rw [integral_density h ha (by linarith),show a+1/2-a = 1/2 by ring] at h1
  rw [integral_density h hm (by linarith),show a+1-(a+1/2) = 1/2 by ring] at h2
  linarith only [h1,h2,hs]

/-- The weight at the midpoint is bounded by the exact mass of its unit cell. -/
theorem midpoint_cell (h : Ioi (0:ℝ)) {a : ℝ} (ha : 0 < a) :
    density h (a+1/2) ≤ primitive h a-primitive h (a+1) := by
  have hab : a ≤ a+1 := by linarith
  have hc := GaloisForLFunctions.ConvexOn.midpoint_mul_le_integral hab
    (convex_cell h ha) (integrable_cell h ha hab)
  rwa [show (a+(a+1))/2 = a+1/2 by ring,show a+1-a = 1 by ring,mul_one,integral_density h ha hab] at hc

theorem primitive_antitone (h : Ioi (0:ℝ)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    primitive h b ≤ primitive h a := by
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos ha hab (neg_nonpos.mpr h.property.le)) h.property.le

/-- The endpoint correction is at most the interval length times the density at any earlier label. -/
theorem primitive_loss (h : Ioi (0:ℝ)) {n a b : ℝ} (hn : 0 < n) (hna : n ≤ a) (hab : a ≤ b) :
    primitive h a-primitive h b ≤ (b-a)*density h n := by
  rw [← integral_density h (hn.trans_le hna) hab]
  have hc := intervalIntegral.integral_mono_on (μ := volume) hab
    (integrable_cell h (hn.trans_le hna) hab) (intervalIntegrable_const (c := density h n))
    (fun x hx => Real.rpow_le_rpow_of_nonpos hn (hna.trans hx.1) (by linarith only [show 0 < h.val from h.property] : -(1+h.val) ≤ 0))
  simpa only [intervalIntegral.integral_const,smul_eq_mul] using hc

#print axioms integral_density
#print axioms strict_trapezoid
#print axioms midpoint_cell
#print axioms primitive_antitone
#print axioms primitive_loss

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GibbsTail
