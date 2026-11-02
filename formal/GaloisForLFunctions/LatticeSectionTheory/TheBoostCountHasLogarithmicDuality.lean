import GaloisForLFunctions.LatticeSectionTheory.TheRectangularLatticeCount
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Logarithmic duality of the Gaussian boost count

The split plane's nonzero Gaussian count is averaged over boosts. Subtracting the
explicit divergent term from the full lattice count gives a convergent self-dual
integral. The removed axes contribute a logarithm and an absolutely convergent
theta constant. Everything here concerns the pole plane.
-/

noncomputable section
open Real MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace GaloisForLFunctions.LatticeSectionTheory
open ArithmeticOrientationGeometry

/-- The nonzero Gaussian lattice count in logarithmic scale. -/
def logThetaTail (x : ℝ) : ℝ := thetaSum (Real.exp (2 * x)) - 1

theorem continuous_logThetaTail : Continuous logThetaTail := by
  refine (continuousOn_thetaSum.comp_continuous (by fun_prop) (fun x => Real.exp_pos _)).sub
    continuous_const

theorem logThetaTail_nonneg (x : ℝ) : 0 ≤ logThetaTail x :=
  sub_nonneg.mpr (one_le_thetaSum (Real.exp_pos _))

theorem logThetaTail_neg (x : ℝ) :
    logThetaTail (-x) = Real.exp x * logThetaTail x + Real.exp x - 1 := by
  have h := thetaSum_inv (Real.exp_pos (2 * -x))
  have hroot : (Real.exp (2 * -x) ^ (1 / 2 : ℝ))⁻¹ = Real.exp x := by
    rw [← Real.exp_mul, ← Real.exp_neg]
    congr 1
    ring
  have hinv : (Real.exp (2 * -x))⁻¹ = Real.exp (2 * x) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  unfold logThetaTail
  rw [h, hroot, hinv]
  ring

theorem logThetaTail_le {x : ℝ} (hx : 0 ≤ x) :
    logThetaTail x ≤ 4 * Real.exp (-4 * x) := by
  have he := Real.add_one_le_exp (2 * x)
  have hx1 : 1 ≤ Real.exp (2 * x) := Real.one_le_exp_iff.mpr (by linarith)
  have hbound : -Real.pi * Real.exp (2 * x) ≤ -4 * x := by
    have hp := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_pos (2*x)).le
    nlinarith only [he, hp, hx]
  exact (thetaSum_sub_one_le hx1).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hbound) (by positivity))

theorem integrableOn_logThetaTail (a : ℝ) : IntegrableOn logThetaTail (Ioi a) := by
  apply integrable_of_isBigO_exp_neg (b := 4) (by positivity)
    continuous_logThetaTail.continuousOn
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simpa only [Real.norm_of_nonneg (logThetaTail_nonneg x), Real.norm_of_nonneg (Real.exp_pos _).le]
    using logThetaTail_le hx

theorem integrableOn_exp_logThetaTail (a : ℝ) :
    IntegrableOn (fun x => Real.exp x * logThetaTail x) (Ioi a) := by
  apply integrable_of_isBigO_exp_neg (b := 3) (by positivity)
    (Real.continuous_exp.mul continuous_logThetaTail).continuousOn
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  dsimp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (logThetaTail_nonneg _)),
    Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp x * logThetaTail x ≤ Real.exp x * (4 * Real.exp (-4*x)) :=
      mul_le_mul_of_nonneg_left (logThetaTail_le hx) (Real.exp_pos _).le
    _ = 4 * Real.exp (-3*x) := by rw [mul_left_comm, ← Real.exp_add]; congr 1; ring

/-- The Gaussian count on the two nonzero axes, averaged over boosts.
The integrand is even in the boost, so twice the positive half-line is the full average. -/
def gaussianBoostCount (x : ℝ) : ℝ :=
  2 * ∫ u in Ioi (0 : ℝ), logThetaTail (x + u) * logThetaTail (x - u)

/-- The full Gaussian count with its explicit divergent term removed. -/
def regularizedBoostCount (x : ℝ) : ℝ :=
  2 * ∫ u in Ioi (0 : ℝ),
    thetaSum (Real.exp (2 * (x + u))) * thetaSum (Real.exp (2 * (x - u))) -
      Real.exp (u - x)

/-- The constant term in the logarithmic reflection defect. -/
def boostLogConstant : ℝ :=
  2 * ((∫ u in Ioi (0 : ℝ), logThetaTail u) +
    ∫ u in Ioi (0 : ℝ), Real.exp u * logThetaTail u) - 2

theorem gaussianBoostCount_nonneg (x : ℝ) : 0 ≤ gaussianBoostCount x := by
  exact mul_nonneg (by positivity) (integral_nonneg fun u =>
    mul_nonneg (logThetaTail_nonneg _) (logThetaTail_nonneg _))

private theorem regularizedBoost_integrand (x u : ℝ) :
    thetaSum (Real.exp (2 * (x + u))) * thetaSum (Real.exp (2 * (x - u))) -
        Real.exp (u - x) =
      logThetaTail (x + u) * logThetaTail (x - u) + logThetaTail (x + u) +
        Real.exp (u - x) * logThetaTail (u - x) := by
  have h := logThetaTail_neg (u - x)
  rw [neg_sub] at h
  dsimp only [logThetaTail] at h ⊢
  nlinarith only [h]

/-- Removing the divergent Gaussian term leaves a nonnegative integrand. -/
theorem regularizedBoostCount_nonneg (x : ℝ) : 0 ≤ regularizedBoostCount x := by
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro u
  rw [regularizedBoost_integrand]
  exact add_nonneg (add_nonneg
    (mul_nonneg (logThetaTail_nonneg _) (logThetaTail_nonneg _))
    (logThetaTail_nonneg _))
    (mul_nonneg (Real.exp_pos _).le (logThetaTail_nonneg _))

private theorem theta_exp_neg (x : ℝ) :
    thetaSum (Real.exp (2 * -x)) = Real.exp x * thetaSum (Real.exp (2*x)) := by
  have h := logThetaTail_neg x
  dsimp only [logThetaTail] at h
  linarith only [h]

/-- Poisson duality before evaluating the regularized axis contributions. -/
theorem regularizedBoostCount_neg (x : ℝ) :
    regularizedBoostCount (-x) = Real.exp (2*x) * regularizedBoostCount x := by
  have he (u : ℝ) :
      thetaSum (Real.exp (2 * (-x + u))) * thetaSum (Real.exp (2 * (-x - u))) -
          Real.exp (u - -x) =
        Real.exp (2*x) * (thetaSum (Real.exp (2 * (x + u))) *
          thetaSum (Real.exp (2 * (x - u))) - Real.exp (u - x)) := by
    rw [show -x+u = -(x-u) by ring, show -x-u = -(x+u) by ring,
      theta_exp_neg, theta_exp_neg]
    have h1 : Real.exp (x-u) * Real.exp (x+u) = Real.exp (2*x) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (2*x) * Real.exp (u-x) = Real.exp (u - -x) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ = (Real.exp (x-u) * Real.exp (x+u)) *
          (thetaSum (Real.exp (2*(x+u))) * thetaSum (Real.exp (2*(x-u)))) -
            Real.exp (u - -x) := by ring
      _ = _ := by rw [h1, ← h2]; ring
  simp only [regularizedBoostCount, he, integral_const_mul]
  ring

private theorem translate_indicator (f : ℝ → ℝ) (x : ℝ) :
    (Ioi (0 : ℝ)).indicator (fun u => f (x+u)) =
      fun u => (Ioi x).indicator f (x+u) := by
  funext u
  simp only [indicator_apply, mem_Ioi, lt_add_iff_pos_right]

private theorem integrableOn_translate {f : ℝ → ℝ} {x : ℝ}
    (hf : IntegrableOn f (Ioi x)) : IntegrableOn (fun u => f (x+u)) (Ioi 0) := by
  apply (integrable_indicator_iff measurableSet_Ioi).mp
  rw [translate_indicator]
  exact (hf.integrable_indicator measurableSet_Ioi).comp_add_left x

private theorem integral_translate (f : ℝ → ℝ) (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), f (x+u)) = ∫ u in Ioi x, f u := by
  rw [← integral_indicator measurableSet_Ioi, translate_indicator,
    integral_add_left_eq_self, integral_indicator measurableSet_Ioi]

/-- Absolute convergence of the nonzero split count's boost average. -/
theorem integrableOn_gaussianBoost (x : ℝ) :
    IntegrableOn (fun u => logThetaTail (x+u) * logThetaTail (x-u)) (Ioi 0) := by
  have hc : Continuous (fun u => logThetaTail (x+u) * logThetaTail (x-u)) :=
    (continuous_logThetaTail.comp (by fun_prop)).mul
      (continuous_logThetaTail.comp (by fun_prop))
  apply integrable_of_isBigO_exp_neg (b := 3) (by positivity) hc.continuousOn
  refine Asymptotics.IsBigO.of_bound (20 * Real.exp (-5*x)) ?_
  filter_upwards [eventually_ge_atTop |x|] with u hu
  have hplus : 0 ≤ x+u := by linarith only [neg_abs_le x, hu]
  have hminus : 0 ≤ u-x := by linarith only [le_abs_self x, hu]
  have hsmall : logThetaTail (u-x) ≤ 4 := by
    exact (logThetaTail_le hminus).trans (by
      have h := Real.exp_le_one_iff.mpr (show -4*(u-x) ≤ 0 by linarith)
      linarith only [h])
  have hlarge : logThetaTail (x-u) ≤ 5 * Real.exp (u-x) := by
    have h := logThetaTail_neg (u-x)
    rw [neg_sub] at h
    have hb := mul_le_mul_of_nonneg_left hsmall (Real.exp_pos (u-x)).le
    linarith only [h, hb]
  rw [Real.norm_of_nonneg (mul_nonneg (logThetaTail_nonneg _) (logThetaTail_nonneg _)),
    Real.norm_of_nonneg (Real.exp_pos _).le]
  calc logThetaTail (x+u) * logThetaTail (x-u)
      ≤ (4 * Real.exp (-4*(x+u))) * (5 * Real.exp (u-x)) :=
        mul_le_mul (logThetaTail_le hplus) hlarge (logThetaTail_nonneg _) (by positivity)
    _ = (20 * Real.exp (-5*x)) * Real.exp (-3*u) := by
      have he : Real.exp (-4*(x+u)) * Real.exp (u-x) =
          Real.exp (-5*x) * Real.exp (-3*u) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      nlinarith only [he]

/-- Absolute convergence also holds after subtracting the divergent full-lattice term. -/
theorem integrableOn_regularizedBoost (x : ℝ) :
    IntegrableOn (fun u =>
      thetaSum (Real.exp (2*(x+u))) * thetaSum (Real.exp (2*(x-u))) - Real.exp (u-x))
      (Ioi 0) := by
  have h₁ := integrableOn_translate (integrableOn_logThetaTail x)
  have h₂ := integrableOn_translate (integrableOn_exp_logThetaTail (-x))
  have h := ((integrableOn_gaussianBoost x).add h₁).add h₂
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  rw [regularizedBoost_integrand]
  simp only [Pi.add_apply, sub_eq_add_neg, add_comm (-x)]

private theorem boost_axis_integrals (x : ℝ) :
    (∫ v in Ioi x, logThetaTail v) + (∫ v in Ioi (-x), Real.exp v * logThetaTail v) =
      (∫ v in Ioi (0 : ℝ), logThetaTail v) +
        (∫ v in Ioi (0 : ℝ), Real.exp v * logThetaTail v) + x + Real.exp (-x) - 1 := by
  have hI := intervalIntegral.integral_interval_add_Ioi
    (integrableOn_logThetaTail 0) (integrableOn_logThetaTail x)
  have hJ := intervalIntegral.integral_interval_add_Ioi
    (integrableOn_exp_logThetaTail (-x)) (integrableOn_exp_logThetaTail 0)
  have hpoint (v : ℝ) : Real.exp (-v) * logThetaTail (-v) =
      logThetaTail v + (1 - Real.exp (-v)) := by
    have he : Real.exp (-v) * Real.exp v = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [logThetaTail_neg, mul_sub, mul_add, ← mul_assoc, he, one_mul]
    ring
  have hchange : (∫ v in -x..0, Real.exp v * logThetaTail v) =
      ∫ v in (0 : ℝ)..x, logThetaTail v + (1-Real.exp (-v)) := by
    have hc := intervalIntegral.integral_comp_neg (a := 0) (b := x)
      (fun v => Real.exp v * logThetaTail v)
    simpa only [neg_zero, hpoint] using hc.symm
  have hcont : Continuous (fun v : ℝ => 1-Real.exp (-v)) := by fun_prop
  have helem : (∫ v in (0 : ℝ)..x, 1-Real.exp (-v)) = x + Real.exp (-x) - 1 := by
    have hd (v : ℝ) : HasDerivAt (fun v : ℝ => v + Real.exp (-v))
        (1-Real.exp (-v)) v := by
      simpa only [id_eq, mul_neg, mul_one, add_neg_eq_sub] using
        (hasDerivAt_id v).add ((hasDerivAt_id v).neg.exp)
    simpa only [neg_zero, Real.exp_zero, zero_add] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
        (hcont.intervalIntegrable 0 x)
  rw [intervalIntegral.integral_add (continuous_logThetaTail.intervalIntegrable 0 x)
    (hcont.intervalIntegrable 0 x), helem] at hchange
  linarith only [hI, hJ, hchange]

/-- The two regularized axes contribute exactly a logarithm, a square-root term and one constant. -/
theorem regularizedBoostCount_eq (x : ℝ) :
    regularizedBoostCount x = gaussianBoostCount x + 2*x + 2*Real.exp (-x) +
      boostLogConstant := by
  have h₁ := integrableOn_translate (integrableOn_logThetaTail x)
  have h₂ := integrableOn_translate (integrableOn_exp_logThetaTail (-x))
  have he (u : ℝ) : Real.exp (u-x) * logThetaTail (u-x) =
      Real.exp (-x+u) * logThetaTail (-x+u) := by
    rw [sub_eq_neg_add]
  simp only [regularizedBoostCount, regularizedBoost_integrand]
  simp_rw [he]
  rw [integral_add ((integrableOn_gaussianBoost x).add h₁) h₂,
    integral_add (integrableOn_gaussianBoost x) h₁, integral_translate, integral_translate]
  have h := boost_axis_integrals x
  dsimp only [gaussianBoostCount, boostLogConstant]
  linarith only [h]

/-- The Gaussian boost average has an explicit logarithmic reflection defect. -/
theorem gaussianBoostCount_neg (x : ℝ) :
    gaussianBoostCount (-x) = Real.exp (2*x) * gaussianBoostCount x +
      2*x*(1+Real.exp (2*x)) + boostLogConstant*(Real.exp (2*x)-1) := by
  have h := regularizedBoostCount_neg x
  rw [regularizedBoostCount_eq, regularizedBoostCount_eq, neg_neg] at h
  have he : Real.exp (2*x) * Real.exp (-x) = Real.exp x := by
    rw [← Real.exp_add]; congr 1; ring
  nlinarith only [h, he]

/-- The half-line definition is the full, even Gaussian boost integral. -/
theorem gaussianBoostCount_eq_integral (x : ℝ) :
    gaussianBoostCount x = ∫ u, logThetaTail (x+u) * logThetaTail (x-u) := by
  rw [gaussianBoostCount, ← integral_comp_abs]
  apply integral_congr_ae
  filter_upwards with u
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_nonpos hu]
    simp only [sub_neg_eq_add, ← sub_eq_add_neg, mul_comm]

/-- In the positive scale, the reflection defect has coefficient `1+t` in front of `log t`. -/
theorem gaussianBoostCount_log_inv {t : ℝ} (ht : 0 < t) :
    gaussianBoostCount (Real.log (1/t)/2) =
      t * gaussianBoostCount (Real.log t/2) + (1+t)*Real.log t + boostLogConstant*(t-1) := by
  have h := gaussianBoostCount_neg (Real.log t/2)
  rw [show 2*(Real.log t/2) = Real.log t by ring, Real.exp_log ht] at h
  rw [one_div, Real.log_inv, neg_div]
  linarith only [h]

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.integrableOn_gaussianBoost
#print axioms GaloisForLFunctions.LatticeSectionTheory.integrableOn_regularizedBoost
#print axioms GaloisForLFunctions.LatticeSectionTheory.regularizedBoostCount_nonneg
#print axioms GaloisForLFunctions.LatticeSectionTheory.regularizedBoostCount_eq
#print axioms GaloisForLFunctions.LatticeSectionTheory.gaussianBoostCount_log_inv
