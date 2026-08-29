import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualBorelTerminalUnconditionalClassification

/-!
# Positive-Borel terminal height controls Xi zero width

Decay of the exact ordered Wold terminal at one height `c` is already quantitative zero
information.  Ordered residual decay transfers to natural cutoffs through the prime-log shell
interpolation, inverse Abel gives the Chebyshev source spectrum of width `1/2-c`, and the corpus
square-window endpoint gives the matching Xi half-plane bound.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Terminal decay at height `c` forces Chebyshev source width `1/2-c`. -/
theorem chebyshevErrorPowerSpectrum_of_woldResidualBorelTerminalWeight
    {c : ℝ} (hc0 : 0 < c) (hcHalf : c < 1 / 2)
    (hterminal : Tendsto (fun k : ℕ ↦
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy k| *
        Real.exp (c * xiMassNthPrimeLogHeight k)) atTop (𝓝 0)) :
    ChebyshevErrorPowerSpectrum (1 / 2 - c) := by
  intro epsilon hepsilon
  let eta : ℝ := min (epsilon / 2) (c / 2)
  let a : ℝ := c - eta
  let epsW : ℝ := 1 / 2 - a
  have heta0 : 0 < eta := by
    dsimp only [eta]
    exact lt_min (by linarith) (by linarith)
  have hetaEpsilon : eta ≤ epsilon := by
    have : eta ≤ epsilon / 2 := by
      dsimp only [eta]
      exact min_le_left _ _
    linarith
  have hetaC : eta ≤ c / 2 := by
    dsimp only [eta]
    exact min_le_right _ _
  have ha0 : 0 < a := by dsimp only [a]; linarith
  have hac : a < c := by dsimp only [a]; linarith
  have hepsW0 : 0 < epsW := by dsimp only [epsW, a]; linarith
  have hepsWHalf : epsW < 1 / 2 := by dsimp only [epsW]; linarith
  obtain ⟨B, hB, hWold⟩ :=
    exists_woldNatResidual_power_rate_of_ordered_terminal
      ha0 hac hcHalf hterminal
  have hWold' : ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ≤
        B * (N : ℝ) ^ (-(1 / 2 - epsW)) := by
    refine ⟨B, hB, ?_⟩
    simpa only [epsW, show (1 : ℝ) / 2 - (1 / 2 - a) = a by ring] using hWold
  obtain ⟨CthetaNat, hCthetaNat, hthetaNat⟩ :=
    exists_chebyshevTheta_nat_power_bound_of_woldNatResidual
      hepsW0 hepsWHalf hWold'
  obtain ⟨Ctheta, hCtheta, htheta⟩ :=
    exists_chebyshevTheta_real_power_bound_of_nat
      (q := 1 / 2 + epsW) (by linarith) hCthetaNat hthetaNat
  obtain ⟨Cpsi, hCpsi, hpsi⟩ :=
    exists_chebyshevPsiReal_power_bound_of_theta hepsW0 hCtheta htheta
  refine ⟨Cpsi, hCpsi.le, ?_⟩
  intro x hx
  rw [criticalMellinError_vonMangoldt_eq_chebyshevPsiReal_sub]
  have hb := hpsi x hx
  have hpow : x ^ (1 / 2 + epsW) ≤
      x ^ (1 / 2 + (1 / 2 - c) + epsilon) := by
    apply Real.rpow_le_rpow_of_exponent_le hx
    dsimp only [epsW, a]
    linarith
  exact hb.trans (mul_le_mul_of_nonneg_left hpow hCpsi.le)

/-- Terminal decay at height `c` confines every Xi zero to transverse width `1/2-c`. -/
theorem xiZeroHalfPlaneBound_of_woldResidualBorelTerminalWeight
    {c : ℝ} (hc0 : 0 < c) (hcHalf : c < 1 / 2)
    (hterminal : Tendsto (fun k : ℕ ↦
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy k| *
        Real.exp (c * xiMassNthPrimeLogHeight k)) atTop (𝓝 0)) :
    XiZeroHalfPlaneBound (1 / 2 - c) := by
  apply xiZeroHalfPlaneBound_of_chebyshevErrorPowerSpectrum (by linarith)
  exact chebyshevErrorPowerSpectrum_of_woldResidualBorelTerminalWeight
    hc0 hcHalf hterminal

end
end RHTower
