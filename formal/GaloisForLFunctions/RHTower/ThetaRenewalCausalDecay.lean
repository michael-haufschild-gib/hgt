import GaloisForLFunctions.RHTower.ThetaRenewalExitDensity
import GaloisForLFunctions.RHTower.ThetaRenewalResonanceDivisor

/-!
# Intrinsic decay of the theta renewal transport kernel

The logarithmic loss grows at least like `exp t`. Its integrated form controls
the ratio of two actual theta increments, including arbitrarily late starting
points. This is the source admission estimate for the causal Fredholm operator.
-/

noncomputable section
open Set

namespace RHTower

theorem thetaRenewalIncrementDeriv_add_exp_nonpos {t : ℝ} (ht : 0 ≤ t) :
    thetaRenewalIncrementDeriv t + Real.exp t * thetaRenewalIncrement t ≤ 0 := by
  have hE := Real.one_le_exp ht
  have hpi := Real.pi_gt_three
  have hM := thetaMoment_pos 1 (Real.exp_pos t)
  have h12 := thetaMoment_one_le_two (Real.exp_pos t)
  have hcoef : 5 / 4 - Real.pi * Real.exp t + Real.exp t ≤ 0 := by
    nlinarith [mul_nonneg (show 0 ≤ Real.pi - 3 by linarith)
      (show 0 ≤ Real.exp t - 1 by linarith)]
  have hprod := mul_le_mul_of_nonneg_left h12
    (show 0 ≤ Real.pi * Real.exp t by positivity)
  have hsmall : 5 / 4 * thetaMoment 1 (Real.exp t) -
      Real.pi * Real.exp t * thetaMoment 2 (Real.exp t) +
      Real.exp t * thetaMoment 1 (Real.exp t) ≤ 0 := by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hcoef hM.le]
  have he : Real.exp (9 / 4 * t) = Real.exp (5 / 4 * t) * Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hid : thetaRenewalIncrementDeriv t + Real.exp t * thetaRenewalIncrement t =
      (2 * Real.pi * Real.exp (5 / 4 * t)) *
        (5 / 4 * thetaMoment 1 (Real.exp t) -
          Real.pi * Real.exp t * thetaMoment 2 (Real.exp t) +
          Real.exp t * thetaMoment 1 (Real.exp t)) := by
    rw [thetaRenewalIncrementDeriv, thetaRenewalIncrement, he]
    ring
  rw [hid]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hsmall

theorem antitoneOn_thetaRenewalIncrement_exp_exp :
    AntitoneOn (fun t => thetaRenewalIncrement t * Real.exp (Real.exp t)) (Ici 0) := by
  have hd (t : ℝ) : HasDerivAt
      (fun t => thetaRenewalIncrement t * Real.exp (Real.exp t))
      ((thetaRenewalIncrementDeriv t + Real.exp t * thetaRenewalIncrement t) *
        Real.exp (Real.exp t)) t := by
    exact ((hasDerivAt_thetaRenewalIncrement t).mul (Real.hasDerivAt_exp t).exp)
      |>.congr_deriv (by ring)
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (continuous_thetaRenewalIncrement.mul (Real.continuous_exp.comp Real.continuous_exp)).continuousOn
    (fun t _ => (hd t).hasDerivWithinAt) ?_
  intro t ht
  exact mul_nonpos_of_nonpos_of_nonneg
    (thetaRenewalIncrementDeriv_add_exp_nonpos (interior_subset ht)) (Real.exp_pos _).le

/-- The intrinsic increment ratio is controlled by the exponential clock difference. -/
theorem thetaRenewalIncrement_ratio_le {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) :
    thetaRenewalIncrement t / thetaRenewalIncrement a ≤
      Real.exp (-(Real.exp t - Real.exp a)) := by
  have h := antitoneOn_thetaRenewalIncrement_exp_exp ha (ha.trans hat) hat
  rw [show -(Real.exp t - Real.exp a) = Real.exp a - Real.exp t by ring, Real.exp_sub]
  exact (div_le_div_iff₀ (thetaRenewalIncrement_pos a) (Real.exp_pos _)).mpr
    (by simpa [mul_comm] using h)

/-- The starting-point-dependent decay is integrable over the whole causal triangle. -/
theorem thetaRenewalIncrement_ratio_le_exp {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) :
    thetaRenewalIncrement t / thetaRenewalIncrement a ≤
      Real.exp (-(Real.exp a * (t - a))) := by
  refine (thetaRenewalIncrement_ratio_le ha hat).trans (Real.exp_le_exp.mpr ?_)
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (t - a)) (Real.exp_pos a).le
  have he : Real.exp a * Real.exp (t - a) = Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  linarith

/-- The positive half-density of the actual renewal increment. -/
def thetaRenewalHalfDensity (t : ℝ) : ℝ := Real.sqrt (thetaRenewalIncrement t)

theorem thetaRenewalHalfDensity_pos (t : ℝ) : 0 < thetaRenewalHalfDensity t :=
  Real.sqrt_pos.mpr (thetaRenewalIncrement_pos t)

theorem thetaRenewalHalfDensity_sq (t : ℝ) :
    thetaRenewalHalfDensity t ^ 2 = thetaRenewalIncrement t :=
  Real.sq_sqrt (thetaRenewalIncrement_pos t).le

theorem continuous_thetaRenewalHalfDensity : Continuous thetaRenewalHalfDensity :=
  continuous_thetaRenewalIncrement.sqrt

theorem thetaRenewalHalfDensity_ratio_sq (t a : ℝ) :
    (thetaRenewalHalfDensity t / thetaRenewalHalfDensity a) ^ 2 =
      thetaRenewalIncrement t / thetaRenewalIncrement a := by
  rw [div_pow, thetaRenewalHalfDensity_sq, thetaRenewalHalfDensity_sq]

theorem thetaRenewalHalfDensity_ratio_le {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) :
    thetaRenewalHalfDensity t / thetaRenewalHalfDensity a ≤
      Real.exp (-(Real.exp a * (t - a)) / 2) := by
  have h := thetaRenewalIncrement_ratio_le_exp ha hat
  rw [← thetaRenewalHalfDensity_ratio_sq] at h
  have he : Real.exp (-(Real.exp a * (t - a)) / 2) ^ 2 =
      Real.exp (-(Real.exp a * (t - a))) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hp := Real.exp_pos (-(Real.exp a * (t - a)) / 2)
  nlinarith

theorem thetaRenewalHalfDensity_ratio_le_uniform {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) :
    thetaRenewalHalfDensity t / thetaRenewalHalfDensity a ≤ Real.exp (-(t - a) / 2) := by
  refine (thetaRenewalHalfDensity_ratio_le ha hat).trans (Real.exp_le_exp.mpr ?_)
  have h := mul_le_mul_of_nonneg_right (Real.one_le_exp ha) (sub_nonneg.mpr hat)
  linarith

end RHTower
