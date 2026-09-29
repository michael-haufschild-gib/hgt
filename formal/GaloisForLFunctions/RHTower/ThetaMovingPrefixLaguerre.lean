import GaloisForLFunctions.RHTower.ThetaMovingPrefixJet
import GaloisForLFunctions.RHTower.ThetaMovingShellLaguerreProfile

/-!
# Sharp moving-cutoff first-Laguerre transition for literal theta prefixes

The actual prefix cosine transform has both signs along quadratic height rays.
The boundary is `lambda = 2*pi`; no RH assumption enters either sign.
-/

open Real Complex Set Filter Topology

namespace RHTower
noncomputable section

def thetaShellPrefixFirstLaguerre (N : ℕ) (b : ℝ) : ℝ :=
  (iteratedDeriv 1 (thetaShellPrefixCosine N) b)^2 -
    thetaShellPrefixCosine N b * iteratedDeriv 2 (thetaShellPrefixCosine N) b

theorem tendsto_normalized_thetaShellPrefixFirstLaguerre {lambda : ℝ} (hlambda : 4 < lambda) :
    Tendsto (fun N => Real.exp (2*Real.pi*thetaMovingShellScale N) *
      thetaShellPrefixFirstLaguerre N (lambda*thetaMovingShellScale N)) atTop
      (𝓝 (128*Real.pi^6*(4*Real.pi^2-lambda^2)/(4*Real.pi^2+lambda^2)^4)) := by
  have h0 := tendsto_normalized_thetaShellPrefixRealJet 0 hlambda
  have h1 := tendsto_normalized_thetaShellPrefixRealJet 1 hlambda
  have h2 := tendsto_normalized_thetaShellPrefixRealJet 2 hlambda
  have hlim := (h1.pow 2).sub (h0.mul h2)
  convert hlim using 1
  · funext N
    have ha := (thetaMovingShellScale_pos N).ne'
    have he : Real.exp (Real.pi*thetaMovingShellScale N) *
        Real.exp (Real.pi*thetaMovingShellScale N) =
          Real.exp (2*Real.pi*thetaMovingShellScale N) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [thetaShellPrefixFirstLaguerre, iteratedDeriv_thetaShellPrefixCosine,
      thetaShellPrefixCosine, pow_zero, pow_one, mul_one]
    rw [← he]
    field_simp [ha]
    <;> ring
  · simp only [thetaMovingShellJetLimit] at *
    rw [← thetaMovingShellJetLimit_firstLaguerre]
    simp only [thetaMovingShellJetLimit, neg_sq, neg_mul_neg]

/-- Concrete positive ray, with no analytic or arithmetic premise. -/
theorem eventually_thetaShellPrefixFirstLaguerre_five_pos :
    ∀ᶠ N : ℕ in atTop,
      0 < thetaShellPrefixFirstLaguerre N (5*thetaMovingShellScale N) := by
  have hl := tendsto_normalized_thetaShellPrefixFirstLaguerre (lambda := 5) (by norm_num)
  have hs : 0 < 128*Real.pi^6*(4*Real.pi^2-(5:ℝ)^2)/(4*Real.pi^2+(5:ℝ)^2)^4 := by
    have hp := Real.pi_gt_three
    have hnum : 0 < 4*Real.pi^2-(5:ℝ)^2 := by nlinarith
    positivity
  filter_upwards [hl.eventually_const_lt hs] with N hN
  exact pos_of_mul_pos_left hN (Real.exp_pos _).le

/-- Concrete negative ray, with no analytic or arithmetic premise. -/
theorem eventually_thetaShellPrefixFirstLaguerre_eight_neg :
    ∀ᶠ N : ℕ in atTop,
      thetaShellPrefixFirstLaguerre N (8*thetaMovingShellScale N) < 0 := by
  have hl := tendsto_normalized_thetaShellPrefixFirstLaguerre (lambda := 8) (by norm_num)
  have hs : 128*Real.pi^6*(4*Real.pi^2-(8:ℝ)^2)/(4*Real.pi^2+(8:ℝ)^2)^4 < 0 := by
    have hp := Real.pi_pos
    have hu := Real.pi_lt_four
    have hnum : 4*Real.pi^2-(8:ℝ)^2 < 0 := by nlinarith
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hnum) (by positivity)
  filter_upwards [hl.eventually_lt_const hs] with N hN
  have hmul : Real.exp (2*Real.pi*thetaMovingShellScale N) *
      thetaShellPrefixFirstLaguerre N (8*thetaMovingShellScale N) <
        Real.exp (2*Real.pi*thetaMovingShellScale N) * 0 := by simpa using hN
  exact (mul_lt_mul_left (Real.exp_pos _)).mp hmul

end
end RHTower
