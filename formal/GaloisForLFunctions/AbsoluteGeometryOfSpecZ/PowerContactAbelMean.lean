import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerContactRealBoundaryResidue

/-!
# The logarithmic Abel mean of the power-normalized contact staircase

The exact step-profile Laplace identity divides the real contact residue
by its positive boundary exponent. Strict growth at the closed zero-width
boundary supplies integrability for every positive Abel parameter.
-/

noncomputable section

open Complex Filter Topology MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity TransHorizonIncidenceMechanics

/-- Logarithmic Abel averaging of the contact staircase, normalized by
the continuous power `exp(-(1-2a)u)`. -/
def powerContactAbelMean (a ε : ℝ) : ℂ :=
  (ε : ℂ) * ∫ u : ℝ,
    stepLaplaceIntegrand (powerContactPrefix a) ((1 - 2 * a + ε : ℝ) : ℂ) u

/-- Every positive Abel parameter is inside the summable Mellin region. -/
theorem integrable_powerContactAbelIntegrand
    {a ε : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (haw : a + SquareRootThreshold.zetaZeroWidth ≤ 1 / 2) (hε : 0 < ε) :
    Integrable (stepLaplaceIntegrand (powerContactPrefix a) ((1 - 2 * a + ε : ℝ) : ℂ)) := by
  apply integrable_stepLaplaceIntegrand (by simp [powerContactPrefix])
    (by simp only [ofReal_re]; linarith only [ha2, hε])
  exact summable_mellin_majorant_of_strict_power_growth
    (by simp [powerContactPrefix])
    (strictGrowth_powerContactPrefix_of_add_width_le_half ha ha2 haw)
    (by simp only [ofReal_re]; linarith only [hε])

theorem powerContactAbelMean_eq
    {a ε : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (haw : a + SquareRootThreshold.zetaZeroWidth ≤ 1 / 2) (hε : 0 < ε) :
    powerContactAbelMean a ε =
      ((ε : ℂ) * complexMellinPairing (powerContactPrefix a)
        ((1 - 2 * a + ε : ℝ) : ℂ)) / ((1 - 2 * a + ε : ℝ) : ℂ) := by
  rw [powerContactAbelMean, integral_stepLaplaceIntegrand
    (by simp [powerContactPrefix])
    (by simp only [ofReal_re]; linarith only [ha2, hε])
    (summable_mellin_majorant_of_strict_power_growth
      (by simp [powerContactPrefix])
      (strictGrowth_powerContactPrefix_of_add_width_le_half ha ha2 haw)
      (by simp only [ofReal_re]; linarith only [hε]))]
  ring

/-- The real contact residue determines a genuine Abel integral limit
throughout the closed zero-width range. -/
theorem tendsto_powerContactAbelMean_of_add_width_le_half
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (haw : a + SquareRootThreshold.zetaZeroWidth ≤ 1 / 2) :
    Tendsto (powerContactAbelMean a) (𝓝[>] 0)
      (𝓝 ((-deriv riemannZeta (1 - (a : ℂ)) / riemannZeta (1 - (a : ℂ)) -
        riemannZeta (1 - (a : ℂ))) / ((1 - 2 * a : ℝ) : ℂ))) := by
  have heps : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hp : Tendsto (fun ε : ℝ => ((1 - 2 * a + ε : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 ((1 - 2 * a : ℝ) : ℂ)) := by
    have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp (heps.const_add (1 - 2 * a))
    simpa only [add_zero] using hh
  have hne : ((1 - 2 * a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by linarith only [ha2])
  apply ((tendsto_mul_powerContactMellin_at_real_width_boundary ha ha2 haw).div hp hne).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (powerContactAbelMean_eq ha ha2 haw hε).symm

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
