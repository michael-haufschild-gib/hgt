import GaloisForLFunctions.RHTower.ChebyshevThetaPowerLog

/-!
# The prime discrepancy in logarithmic height

In the logarithmic height `h = log x` the power-log prime number theorem for `θ` reads

`|Θ(h) − e^h| ≤ C e^h e^{-c h^{1/10}}`,  `Θ(h) = θ(e^h)`,

for all large `h`.  This is the exact source-remainder input for the subcaustic penetration
estimates: the exponent `1/10` is the geometric image of the zero-free margin `(log T)^{-9}`.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-- The prime discrepancy in logarithmic height, `E(h) = Θ(h) − e^h`. -/
def xiMassThetaLogDiscrepancy (h : ℝ) : ℝ :=
  Chebyshev.theta (Real.exp h) - Real.exp h

/-- **The power-log prime number theorem in logarithmic height.** -/
theorem exists_norm_xiMassThetaLogDiscrepancy_le :
    ∃ c C h₀ : ℝ, 0 < c ∧ 0 ≤ C ∧ 1 ≤ h₀ ∧ ∀ h : ℝ, h₀ ≤ h →
      |xiMassThetaLogDiscrepancy h|
        ≤ C * Real.exp h * Real.exp (-(c * h ^ ((1 : ℝ) / 10))) := by
  obtain ⟨c, C, x₀, hc, hC, hx₀, hbound⟩ := exists_chebyshev_theta_power_log
  refine ⟨c, C, max (Real.log x₀) 1, hc, hC, le_max_right _ _, fun h hh => ?_⟩
  have hlogx : Real.log x₀ ≤ h := le_trans (le_max_left _ _) hh
  have hx0 : (0 : ℝ) < x₀ := by linarith
  have hxe : x₀ ≤ Real.exp h := by
    have hstep := Real.exp_le_exp.2 hlogx
    rwa [Real.exp_log hx0] at hstep
  have hres := hbound (Real.exp h) hxe
  rw [Real.log_exp] at hres
  exact hres

end

end RHTower
