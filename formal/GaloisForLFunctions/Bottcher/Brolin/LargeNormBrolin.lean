import GaloisForLFunctions.Bottcher.JuliaMeasureZero
import GaloisForLFunctions.Bottcher.Q62BrolinThread
import GaloisForLFunctions.Bottcher.Q62BrolinFInvariance
import GaloisForLFunctions.Bottcher.Brolin.RieszSupport
import GaloisForLFunctions.Bottcher.Q62EquilibriumVanishing
import GaloisForLFunctions.Bottcher.Q62WeylDischarge

/-!
# The Brolin structure is unconditional for large parameters

For `‖c‖ ≥ 4` the filled Julia set of `z ↦ z² + c` is Lebesgue-null
(`volume_filledJulia_eq_zero_of_four_le_norm`).  That single fact discharges the `volume = 0`
side-condition of the whole Brolin/GAP-A layer, so on the explicit parameter region `‖c‖ ≥ 4` the
following hold with no analytic hypothesis: the filled Julia set has empty interior, the limiting
Brolin measure equals the equilibrium measure `gapAMu`, `gapAMu` is invariant under the dynamics, and
both are the Riesz measure of the dynamical Green function.
-/

open MeasureTheory

namespace Bottcher

/-- **Empty interior of the filled Julia set for `‖c‖ ≥ 4`.**  A Lebesgue-null set has empty
interior; `volume_filledJulia_eq_zero_of_four_le_norm` supplies the nullity. -/
theorem interior_filledJulia_eq_empty_of_four_le_norm {c : ℂ} (hc : (4 : ℝ) ≤ ‖c‖) :
    interior (filledJulia c) = ∅ :=
  interior_filledJulia_eq_empty_of_volume_zero (volume_filledJulia_eq_zero_of_four_le_norm hc)

/-- **The limiting Brolin measure equals the equilibrium measure for `‖c‖ ≥ 4`.**  The backward-orbit
limiting measure `limitingBrolinMeasureAt c a` coincides with `gapAMu c`, unconditionally on
`‖c‖ ≥ 4` (the `volume = 0` hypothesis of the weld is discharged). -/
theorem limitingBrolinMeasureAt_eq_gapAMu_of_four_le_norm {c a : ℂ} (hc : (4 : ℝ) ≤ ‖c‖) :
    limitingBrolinMeasureAt c a = gapAMu c :=
  limitingBrolinMeasureAt_eq_gapAMu_of_volume_zero (volume_filledJulia_eq_zero_of_four_le_norm hc)

/-- **`gapAMu c` is invariant under the quadratic map for `‖c‖ ≥ 4`.**  The pushforward of the
equilibrium measure by `z ↦ z² + c` is itself, unconditionally on `‖c‖ ≥ 4`. -/
theorem map_quadratic_gapAMu_eq_of_four_le_norm {c : ℂ} (hc : (4 : ℝ) ≤ ‖c‖) :
    Measure.map (quadratic c) (gapAMu c) = gapAMu c :=
  map_quadratic_gapAMu_eq_of_volume_filledJulia_zero (volume_filledJulia_eq_zero_of_four_le_norm hc)

/-- **The limiting Brolin measure is the Riesz measure of the Green function for `‖c‖ ≥ 4`.**
`limitingBrolinMeasureAt c a = (2π)⁻¹ Δ greenFunctionDyn c`, unconditionally on `‖c‖ ≥ 4`. -/
theorem isRieszMeasureOfSmooth_limitingBrolinMeasureAt_of_four_le_norm (c a : ℂ)
    (hc : (4 : ℝ) ≤ ‖c‖) :
    IsRieszMeasureOfSmooth (limitingBrolinMeasureAt c a) (greenFunctionDyn c) :=
  isRieszMeasureOfSmooth_limitingBrolinMeasureAt_of_filledJulia_null c a
    (volume_filledJulia_eq_zero_of_four_le_norm hc)

/-- **The Brolin scaling relation holds for `‖c‖ ≥ 4`.**  `BrolinScalingAt c a` — the backward-orbit
normalization scales correctly — unconditionally on `‖c‖ ≥ 4`. -/
theorem brolinScalingAt_of_four_le_norm {c a : ℂ} (hc : (4 : ℝ) ≤ ‖c‖) : BrolinScalingAt c a :=
  brolinScalingAt_of_volume_zero (volume_filledJulia_eq_zero_of_four_le_norm hc)

/-- **The potential is dominated on the filled Julia set for `‖c‖ ≥ 4`.**
`PotentialDominatedOnFilledJulia c a`, unconditionally on `‖c‖ ≥ 4`. -/
theorem potentialDominatedOnFilledJulia_of_four_le_norm {c a : ℂ} (hc : (4 : ℝ) ≤ ‖c‖) :
    PotentialDominatedOnFilledJulia c a :=
  potentialDominatedOnFilledJulia_of_volume_zero (volume_filledJulia_eq_zero_of_four_le_norm hc)

/-- **The equilibrium potential vanishes a.e. for `‖c‖ ≥ 4`.**  `EquilibriumPotentialVanishesAe c a`,
by feeding the scaling (`brolinScalingAt_of_four_le_norm`) and domination
(`potentialDominatedOnFilledJulia_of_four_le_norm`) relations, both unconditional here, into
`equilibriumPotentialVanishesAe_of_scaling_of_dominated`. -/
theorem equilibriumPotentialVanishesAe_of_four_le_norm (c a : ℂ) (hc : (4 : ℝ) ≤ ‖c‖) :
    EquilibriumPotentialVanishesAe c a :=
  equilibriumPotentialVanishesAe_of_scaling_of_dominated c a
    (brolinScalingAt_of_four_le_norm hc) (potentialDominatedOnFilledJulia_of_four_le_norm hc)

/-- **GAP-A support theorem for `‖c‖ ≥ 4`.**  The frontier of the filled Julia set is contained in
the support of the limiting Brolin measure, unconditionally on `‖c‖ ≥ 4`. -/
theorem frontier_filledJulia_subset_support_limitingBrolinMeasureAt_of_four_le_norm
    (c a : ℂ) (hc : (4 : ℝ) ≤ ‖c‖) :
    frontier (filledJulia c) ⊆ (limitingBrolinMeasureAt c a).support :=
  frontier_filledJulia_subset_support_limitingBrolinMeasureAt_of_equilibriumVanishes c a
    (equilibriumPotentialVanishesAe_of_four_le_norm c a hc)

end Bottcher
