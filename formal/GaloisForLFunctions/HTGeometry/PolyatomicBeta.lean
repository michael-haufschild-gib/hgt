import Mathlib.Probability.Distributions.Beta
import Mathlib.Tactic

/-!
# Exact beta-partition moments for polyatomic energy exchange

Appendix B of arXiv:2608.29825 derives the exchange rate from the first
moment of the kinetic beta partition. Positive shape parameters are
represented by exponentials, so every theorem is closed for arbitrary
real parameters. The integral identities are analytic, not quadrature
or numerical evaluations.
-/

open MeasureTheory Set ProbabilityTheory
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The beta normalizer obeys the right-shape first-moment recurrence. -/
theorem collisionBeta_right_recurrence (a b : ℝ) :
    beta (Real.exp a) (Real.exp b + 1) =
      Real.exp b / (Real.exp a + Real.exp b) * beta (Real.exp a) (Real.exp b) := by
  have ha := Real.exp_pos a
  have hb := Real.exp_pos b
  have hab : 0 < Real.exp a + Real.exp b := add_pos ha hb
  unfold beta
  rw [Real.Gamma_add_one (ne_of_gt hb),
    show Real.exp a + (Real.exp b + 1) = (Real.exp a + Real.exp b) + 1 by ring,
    Real.Gamma_add_one (ne_of_gt hab)]
  field_simp

/-- The real beta integral for every positive pair of shape parameters. -/
theorem collisionBeta_integral (a b : ℝ) :
    (∫ x : ℝ in 0..1, x ^ (Real.exp a - 1) * (1 - x) ^ (Real.exp b - 1)) =
      beta (Real.exp a) (Real.exp b) := by
  have he : Complex.ofReal (∫ x : ℝ in 0..1,
      x ^ (Real.exp a - 1) * (1 - x) ^ (Real.exp b - 1)) =
      Complex.betaIntegral (Real.exp a) (Real.exp b) := by
    rw [← intervalIntegral.integral_ofReal, Complex.betaIntegral]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    dsimp only
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
      Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le)]
    push_cast
    rfl
  have hr := congrArg Complex.re he
  simpa only [Complex.ofReal_re, ← beta_eq_betaIntegralReal _ _ (Real.exp_pos a)
    (Real.exp_pos b)] using hr

/-- Multiplication by the internal fraction shifts the right beta shape by one. -/
theorem collisionBeta_internal_moment (a b : ℝ) :
    (∫ x : ℝ in 0..1, (1 - x) *
      (x ^ (Real.exp a - 1) * (1 - x) ^ (Real.exp b - 1))) =
      beta (Real.exp a) (Real.exp b + 1) := by
  have hb : 0 < Real.exp b + 1 := by positivity
  have he := collisionBeta_integral a (Real.log (Real.exp b + 1))
  rw [Real.exp_log hb] at he
  rw [← he]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  have hx1 : 0 < 1 - x := sub_pos.mpr hx.2
  rw [add_sub_cancel_right]
  calc
    _ = x ^ (Real.exp a - 1) *
        ((1 - x) ^ (Real.exp b - 1) * (1 - x) ^ (1 : ℝ)) := by
      rw [Real.rpow_one]
      ring
    _ = _ := by rw [← Real.rpow_add hx1, sub_add_cancel]

/-- The normalized internal-energy fraction is the exact beta mean. -/
theorem collisionBeta_internal_mean (a b : ℝ) :
    (∫ x : ℝ in 0..1, (1 - x) *
      (x ^ (Real.exp a - 1) * (1 - x) ^ (Real.exp b - 1))) /
      (∫ x : ℝ in 0..1, x ^ (Real.exp a - 1) * (1 - x) ^ (Real.exp b - 1)) =
      Real.exp b / (Real.exp a + Real.exp b) := by
  rw [collisionBeta_internal_moment, collisionBeta_integral,
    collisionBeta_right_recurrence]
  exact mul_div_cancel_right₀ _ (ne_of_gt (beta_pos (Real.exp_pos a) (Real.exp_pos b)))

/-- For three translational degrees of freedom, the partition deposits exactly
`2δ/(3+2δ)` into the two internal-energy pools, for every positive real `δ`. -/
theorem polyatomicBeta_internal_fraction (d : ℝ) :
    (∫ x : ℝ in 0..1, (1 - x) *
      (x ^ (1 / 2 : ℝ) * (1 - x) ^ (Real.exp d - 1))) /
      (∫ x : ℝ in 0..1, x ^ (1 / 2 : ℝ) * (1 - x) ^ (Real.exp d - 1)) =
      2 * Real.exp d / (3 + 2 * Real.exp d) := by
  have h := collisionBeta_internal_mean (Real.log (3 / 2)) d
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)] at h
  norm_num only [show (3 / 2 : ℝ) - 1 = 1 / 2 by ring] at h
  rw [h]
  field_simp

/-- Positive Landau--Teller relaxation rate extracted from the beta partition. -/
def polyatomicLandauTellerRate (d : ℝ) : ℝ :=
  (3 + Real.exp d) / (3 + 2 * Real.exp d)

/-- The beta exchange gain minus unit loss gives the negative Landau--Teller rate. -/
theorem polyatomicLandauTeller_gain_loss (d : ℝ) :
    Real.exp d / (3 + 2 * Real.exp d) - 1 = -polyatomicLandauTellerRate d := by
  have h : 3 + 2 * Real.exp d ≠ 0 := by positivity
  unfold polyatomicLandauTellerRate
  field_simp
  ring

/-- Exchange relaxation is faster than the shear rate and slower than unit collision frequency. -/
theorem polyatomicLandauTeller_rate_bounds (d : ℝ) :
    1 / 2 < polyatomicLandauTellerRate d ∧ polyatomicLandauTellerRate d < 1 := by
  have h : 0 < 3 + 2 * Real.exp d := by positivity
  unfold polyatomicLandauTellerRate
  constructor
  · rw [lt_div_iff₀ h]
    linarith
  · rw [div_lt_iff₀ h]
    linarith [Real.exp_pos d]

/-- Increasing the internal dimension strictly slows the exchange rate. -/
theorem polyatomicLandauTeller_rate_strictAnti : StrictAnti polyatomicLandauTellerRate := by
  intro x y hxy
  have hx : 0 < 3 + 2 * Real.exp x := by positivity
  have hy : 0 < 3 + 2 * Real.exp y := by positivity
  unfold polyatomicLandauTellerRate
  rw [div_lt_div_iff₀ hy hx]
  nlinarith [Real.exp_lt_exp.mpr hxy]

end GaloisForLFunctions.HTGeometry
