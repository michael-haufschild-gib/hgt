import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualBorelTerminalWidthSpectrum

/-!
# Exact natural Wold residual power spectrum

For every `0 ≤ alpha < 1/2`, natural-cutoff Wold residual decay at all powers strictly below
`1/2-alpha` is equivalent to `XiZeroHalfPlaneBound alpha`.

Forward transport uses generalized von Koch, theta-to-Mertens Abel summation, and Euler trace
correction. Reverse transport uses exact inverse Abel recovery of theta from the natural Wold
primitive, then prime-power correction and the Chebyshev-to-Xi width collision. Endpoint width is
recovered cofinally; no estimate at the boundary exponent is assumed.

This removes ordered-prime mesh interpolation from the invariant and supplies a natural-cutoff
coordinate for future local Tauberian or averaging producers.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Every natural-cutoff Wold residual power rate below the complement of `alpha`. -/
def WoldNatResidualPowerSpectrum (alpha : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 / 2 - alpha →
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ≤
        B * (N : ℝ) ^ (-c)

/-- Chebyshev width gives the complete complementary natural Wold power spectrum. -/
theorem woldNatResidualPowerSpectrum_of_chebyshevErrorPowerSpectrum
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hspectrum : ChebyshevErrorPowerSpectrum alpha) :
    WoldNatResidualPowerSpectrum alpha := by
  intro c hc0 hcFrontier
  let delta : ℝ := 1 / 2 - alpha - c
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  have hsubhalf : alpha + delta < 1 / 2 := by dsimp only [delta]; linarith
  obtain ⟨B, hB, hrate⟩ :=
    exists_woldNatResidual_power_rate_of_chebyshevErrorPowerSpectrum
      halpha hdelta hsubhalf hspectrum
  refine ⟨B, hB, ?_⟩
  simpa only [delta, show -(1 / 2 - (alpha + (1 / 2 - alpha - c))) = -c by ring]
    using hrate

/-- Cofinal natural Wold power rates recover the Chebyshev spectrum at the exact width. -/
theorem chebyshevErrorPowerSpectrum_of_woldNatResidualPowerSpectrum
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha < 1 / 2)
    (hWold : WoldNatResidualPowerSpectrum alpha) :
    ChebyshevErrorPowerSpectrum alpha := by
  intro epsilon hepsilon
  let eta : ℝ := min (epsilon / 2) ((1 / 2 - alpha) / 2)
  let c : ℝ := 1 / 2 - alpha - eta
  let epsW : ℝ := 1 / 2 - c
  have heta0 : 0 < eta := by
    dsimp only [eta]
    exact lt_min (by linarith) (by linarith)
  have hetaEpsilon : eta ≤ epsilon / 2 := by
    dsimp only [eta]
    exact min_le_left _ _
  have hetaFrontier : eta ≤ (1 / 2 - alpha) / 2 := by
    dsimp only [eta]
    exact min_le_right _ _
  have hc0 : 0 < c := by dsimp only [c]; linarith
  have hcFrontier : c < 1 / 2 - alpha := by dsimp only [c]; linarith
  have hepsW0 : 0 < epsW := by dsimp only [epsW, c]; linarith
  have hepsWHalf : epsW < 1 / 2 := by dsimp only [epsW]; linarith
  obtain ⟨B, hB, hrate⟩ := hWold c hc0 hcFrontier
  have hrate' : ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ≤
        B * (N : ℝ) ^ (-(1 / 2 - epsW)) := by
    refine ⟨B, hB, ?_⟩
    simpa only [epsW, show -(1 / 2 - (1 / 2 - c)) = -c by ring] using hrate
  obtain ⟨CthetaNat, hCthetaNat, hthetaNat⟩ :=
    exists_chebyshevTheta_nat_power_bound_of_woldNatResidual
      hepsW0 hepsWHalf hrate'
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
      x ^ (1 / 2 + alpha + epsilon) := by
    apply Real.rpow_le_rpow_of_exponent_le hx
    dsimp only [epsW, c]
    linarith
  exact hb.trans (mul_le_mul_of_nonneg_left hpow hCpsi.le)

/-- Exact all-width natural Wold law. -/
theorem xiZeroHalfPlaneBound_iff_woldNatResidualPowerSpectrum
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha < 1 / 2) :
    XiZeroHalfPlaneBound alpha ↔ WoldNatResidualPowerSpectrum alpha := by
  constructor
  · intro hXi
    exact woldNatResidualPowerSpectrum_of_chebyshevErrorPowerSpectrum halpha
      (chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound halpha hXi)
  · intro hWold
    exact xiZeroHalfPlaneBound_of_chebyshevErrorPowerSpectrum halpha
      (chebyshevErrorPowerSpectrum_of_woldNatResidualPowerSpectrum
        halpha halphaHalf hWold)

/-- Zero width specializes the all-width natural Wold law to RH. -/
theorem riemannHypothesis_iff_woldNatResidualPowerSpectrum_zero :
    RiemannHypothesis ↔ WoldNatResidualPowerSpectrum 0 := by
  rw [← xiZeroHalfPlaneBound_zero_iff_rh]
  exact xiZeroHalfPlaneBound_iff_woldNatResidualPowerSpectrum
    (by norm_num) (by norm_num)

end
end RHTower

