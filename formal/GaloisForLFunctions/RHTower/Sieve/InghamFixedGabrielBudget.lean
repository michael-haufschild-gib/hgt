import GaloisForLFunctions.RHTower.Sieve.InghamGabrielExponent
import GaloisForLFunctions.RHTower.Sieve.InghamRightEdgePowerSaving

namespace RHTower.Sieve

noncomputable section

/-- Fixed Route T zero-density ordinate. -/
noncomputable def inghamFixedGabrielSigma : ℝ := 7 / 10

theorem inghamFixedGabrielLeftWeight_eq :
    inghamGabrielLeftWeight inghamFixedGabrielSigma inghamPowerSavingRightEdge =
      55 / 91 := by
  norm_num [inghamGabrielLeftWeight, inghamFixedGabrielSigma,
    inghamPowerSavingRightEdge]

theorem inghamFixedGabrielRightWeight_eq :
    inghamGabrielRightWeight inghamFixedGabrielSigma inghamPowerSavingRightEdge =
      36 / 91 := by
  norm_num [inghamGabrielRightWeight, inghamFixedGabrielSigma,
    inghamPowerSavingRightEdge]

theorem inghamFixedGabrielMomentParameter_eq :
    inghamGabrielMomentParameter inghamFixedGabrielSigma inghamPowerSavingRightEdge =
      237 / 364 := by
  rw [inghamGabrielMomentParameter_eq]
  norm_num [inghamFixedGabrielSigma, inghamPowerSavingRightEdge]

/-- Interior detector power `1/(w₁·3/4+w₂·1/2)`. -/
noncomputable def inghamFixedGabrielInteriorPower : ℝ :=
  (inghamGabrielMomentParameter inghamFixedGabrielSigma
    inghamPowerSavingRightEdge)⁻¹

theorem inghamFixedGabrielInteriorPower_eq :
    inghamFixedGabrielInteriorPower = 364 / 237 := by
  rw [inghamFixedGabrielInteriorPower, inghamFixedGabrielMomentParameter_eq]
  norm_num

theorem four_thirds_le_inghamFixedGabrielInteriorPower :
    (4 / 3 : ℝ) ≤ inghamFixedGabrielInteriorPower := by
  rw [inghamFixedGabrielInteriorPower_eq]
  norm_num

theorem inghamFixedGabrielInteriorPower_le_two :
    inghamFixedGabrielInteriorPower ≤ (2 : ℝ) := by
  rw [inghamFixedGabrielInteriorPower_eq]
  norm_num

/-- Fraction of the interpolated height exponent contributed by the critical endpoint. -/
noncomputable def inghamFixedGabrielCriticalShare : ℝ :=
  ((3 / 4 : ℝ) *
      inghamGabrielLeftWeight inghamFixedGabrielSigma inghamPowerSavingRightEdge) /
    inghamGabrielMomentParameter inghamFixedGabrielSigma inghamPowerSavingRightEdge

/-- Fraction of the interpolated height exponent contributed by the right endpoint. -/
noncomputable def inghamFixedGabrielRightShare : ℝ :=
  ((1 / 2 : ℝ) *
      inghamGabrielRightWeight inghamFixedGabrielSigma inghamPowerSavingRightEdge) /
    inghamGabrielMomentParameter inghamFixedGabrielSigma inghamPowerSavingRightEdge

theorem inghamFixedGabrielCriticalShare_eq :
    inghamFixedGabrielCriticalShare = 55 / 79 := by
  rw [inghamFixedGabrielCriticalShare, inghamFixedGabrielLeftWeight_eq,
    inghamFixedGabrielMomentParameter_eq]
  norm_num

theorem inghamFixedGabrielRightShare_eq :
    inghamFixedGabrielRightShare = 24 / 79 := by
  rw [inghamFixedGabrielRightShare, inghamFixedGabrielRightWeight_eq,
    inghamFixedGabrielMomentParameter_eq]
  norm_num

theorem inghamFixedGabrielShares_add :
    inghamFixedGabrielCriticalShare + inghamFixedGabrielRightShare = 1 := by
  rw [inghamFixedGabrielCriticalShare_eq, inghamFixedGabrielRightShare_eq]
  norm_num

/-- Height exponent after interpolating the formal critical loss `251/250` against the new
right-edge saving `-1/180`. -/
noncomputable def inghamFixedGabrielRouteTExponent : ℝ :=
  (251 / 250 : ℝ) * inghamFixedGabrielCriticalShare +
    (-(1 / 180 : ℝ)) * inghamFixedGabrielRightShare

theorem inghamFixedGabrielRouteTExponent_eq :
    inghamFixedGabrielRouteTExponent = 8263 / 11850 := by
  rw [inghamFixedGabrielRouteTExponent,
    inghamFixedGabrielCriticalShare_eq, inghamFixedGabrielRightShare_eq]
  norm_num

/-- Exact surviving margin below Route T's target after both formal endpoint losses. -/
theorem seven_tenths_sub_inghamFixedGabrielRouteTExponent :
    (7 / 10 : ℝ) - inghamFixedGabrielRouteTExponent = 16 / 5925 := by
  rw [inghamFixedGabrielRouteTExponent_eq]
  norm_num

theorem inghamFixedGabrielRouteTExponent_lt_seven_tenths :
    inghamFixedGabrielRouteTExponent < (7 / 10 : ℝ) := by
  rw [inghamFixedGabrielRouteTExponent_eq]
  norm_num

end

end RHTower.Sieve
