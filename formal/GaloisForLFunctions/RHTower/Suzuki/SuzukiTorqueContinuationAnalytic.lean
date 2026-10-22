import GaloisForLFunctions.RHTower.RiemannXiRealAxisNonvanishing
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTorqueEulerTransform

/-!
# The torque continuation is analytic at every nonzero real point

`(16)`'s right-hand side is a quotient: two curvatures of the completed logarithmic derivative over
`2s²`.  The curvatures are analytic wherever `ξ` does not vanish, and `ξ` has no real zeros; the
denominator is the only real obstruction, at `s = 0`.
-/

open Complex

noncomputable section

namespace RHTower

theorem analyticAt_xi (z : ℂ) : AnalyticAt ℂ xi z :=
  xi_differentiable.differentiableOn.analyticAt (Filter.univ_mem' fun _ => trivial)

theorem analyticAt_logDeriv_xi_suzukiTorqueContinuationAnalytic {z : ℂ} (hz : xi z ≠ 0) : AnalyticAt ℂ (logDeriv xi) z := by
  have hnum : AnalyticAt ℂ (deriv xi) z := (analyticAt_xi z).deriv
  have h : AnalyticAt ℂ (fun w : ℂ => deriv xi w / xi w) z := hnum.div (analyticAt_xi z) hz
  exact h

theorem analyticAt_deriv_logDeriv_xi {z : ℂ} (hz : xi z ≠ 0) :
    AnalyticAt ℂ (deriv (logDeriv xi)) z := (analyticAt_logDeriv_xi_suzukiTorqueContinuationAnalytic hz).deriv

/-- **The continuation is analytic wherever the two Xi arguments and the denominator allow.** -/
theorem analyticAt_suzukiPositionTorqueLaplaceContinuation {s : ℂ} (hs : s ≠ 0)
    (h1 : xi (s - 1 / 2) ≠ 0) (h2 : xi (s + 3 / 2) ≠ 0) :
    AnalyticAt ℂ suzukiPositionTorqueLaplaceContinuation s := by
  have ha1 : AnalyticAt ℂ (fun w : ℂ => deriv (logDeriv xi) (w - 1 / 2)) s := by
    have hin : AnalyticAt ℂ (fun w : ℂ => w - 1 / 2) s := analyticAt_id.sub analyticAt_const
    exact AnalyticAt.comp (x := s) (g := deriv (logDeriv xi)) (f := fun w : ℂ => w - 1 / 2)
      (analyticAt_deriv_logDeriv_xi h1) hin
  have ha2 : AnalyticAt ℂ (fun w : ℂ => deriv (logDeriv xi) (w + 3 / 2)) s := by
    have hin : AnalyticAt ℂ (fun w : ℂ => w + 3 / 2) s := analyticAt_id.add analyticAt_const
    exact AnalyticAt.comp (x := s) (g := deriv (logDeriv xi)) (f := fun w : ℂ => w + 3 / 2)
      (analyticAt_deriv_logDeriv_xi h2) hin
  have hden : AnalyticAt ℂ (fun w : ℂ => 2 * w ^ (2 : ℕ)) s :=
    analyticAt_const.mul (analyticAt_id.pow 2)
  have hdne : (2 : ℂ) * s ^ (2 : ℕ) ≠ 0 := by
    refine mul_ne_zero (by norm_num) (pow_ne_zero 2 hs)
  have h : AnalyticAt ℂ
      (fun w : ℂ => (deriv (logDeriv xi) (w - 1 / 2) - deriv (logDeriv xi) (w + 3 / 2))
        / (2 * w ^ (2 : ℕ))) s := (ha1.sub ha2).div hden hdne
  exact h

/-- **The continuation is analytic at every nonzero real point.** -/
theorem analyticAt_suzukiPositionTorqueLaplaceContinuation_ofReal {σ : ℝ} (hσ : σ ≠ 0) :
    AnalyticAt ℂ suzukiPositionTorqueLaplaceContinuation ((σ : ℂ)) := by
  refine analyticAt_suzukiPositionTorqueLaplaceContinuation ?_ ?_ ?_
  · simpa using hσ
  · have h := xi_ne_zero_of_ofReal (σ - 1 / 2)
    have hcast : ((((σ - 1 / 2 : ℝ)) : ℂ)) = ((σ : ℂ)) - 1 / 2 := by push_cast; ring
    rwa [hcast] at h
  · have h := xi_ne_zero_of_ofReal (σ + 3 / 2)
    have hcast : ((((σ + 3 / 2 : ℝ)) : ℂ)) = ((σ : ℂ)) + 3 / 2 := by push_cast; ring
    rwa [hcast] at h

end RHTower
