import GaloisForLFunctions.RHTower.Sieve.MaynardUpperPhaseHandoff

/-!
# Fixed prime-supply exponent for the Route-T upper phase

The exact handoff exponent `3/4 - d/2` still carries the tiny Route-T deficit `d`.  Quantitative
zero-density and explicit-formula estimates do not need to track that endpoint.  The fixed rational
exponent `7/10` lies uniformly below the handoff, while a density envelope of coefficient three
leaves the fixed exponent margin `1/10` there.

This module isolates the unconditional scalar interface.  The remaining analytic theorem is the
unconditional Ingham/Hoheisel prime-supply statement at exponent `7/10`; it is not assumed here.
-/

noncomputable section

namespace RHTower.Sieve

/-- Fixed short-interval exponent used to decouple prime supply from the tiny Route-T deficit. -/
def routeTPrimeSupplyExponent : ℝ := 7 / 10

/-- The coefficient-three density calculation has a fixed `1/10` power margin at the chosen
prime-supply exponent. -/
theorem routeTPrimeSupply_density_three_margin_identity :
    1 - 3 * (1 - routeTPrimeSupplyExponent) = 1 / 10 := by
  norm_num [routeTPrimeSupplyExponent]

theorem routeTPrimeSupply_density_three_fits :
    3 * (1 - routeTPrimeSupplyExponent) < 1 := by
  have h := routeTPrimeSupply_density_three_margin_identity
  linarith

/-- The exact critical density coefficient at exponent `7/10` is `10/3`. -/
theorem routeTPrimeSupply_criticalDensityCoefficient_identity :
    (10 / 3 : ℝ) * (1 - routeTPrimeSupplyExponent) = 1 := by
  norm_num [routeTPrimeSupplyExponent]

theorem routeTPrimeSupply_density_three_lt_critical :
    (3 : ℝ) < 10 / 3 := by
  norm_num

/-- `7/10` lies on the prime-supply side of the coefficient-three threshold `2/3`. -/
theorem two_thirds_lt_routeTPrimeSupplyExponent :
    (2 / 3 : ℝ) < routeTPrimeSupplyExponent := by
  norm_num [routeTPrimeSupplyExponent]

/-- The fixed exponent plus the explicit reserve `9/200` still lies strictly below the Route-T
physical handoff.  The reserve comes only from `d < 1/100`:
`(3/4-d/2) - 7/10 = 1/20-d/2 > 9/200`. -/
theorem routeTPrimeSupplyExponent_add_margin_lt_handoff :
    routeTPrimeSupplyExponent + 9 / 200 < routeTPhysicalSliceHandoffTheta := by
  have hd := maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  simp only [routeTPrimeSupplyExponent, routeTPhysicalSliceHandoffTheta]
  linarith

theorem routeTPrimeSupplyExponent_lt_handoff :
    routeTPrimeSupplyExponent < routeTPhysicalSliceHandoffTheta := by
  have h := routeTPrimeSupplyExponent_add_margin_lt_handoff
  linarith

/-- Every upper-phase height has width exponent strictly larger than the fixed prime-supply
exponent. -/
theorem routeTPrimeSupplyExponent_lt_widthExponent
    {mu : ℝ} (hmu : routeTPhysicalSliceHandoffMu ≤ mu) :
    routeTPrimeSupplyExponent < 1 - 1 / mu := by
  exact routeTPrimeSupplyExponent_lt_handoff.trans_le
    (routeTPhysicalSliceHandoffTheta_le_widthExponent hmu)

/-- On bases at least one, the fixed `7/10` window fits inside every upper-phase physical window. -/
theorem routeTPrimeSupply_rpow_le_width
    {x mu : ℝ} (hx : 1 ≤ x) (hmu : routeTPhysicalSliceHandoffMu ≤ mu) :
    x ^ routeTPrimeSupplyExponent ≤ x ^ (1 - 1 / mu) := by
  exact Real.rpow_le_rpow_of_exponent_le hx
    (routeTPrimeSupplyExponent_lt_widthExponent hmu).le

end RHTower.Sieve

