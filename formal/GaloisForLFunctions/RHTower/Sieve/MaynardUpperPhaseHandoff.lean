import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSliceLargeValues

/-!
# Exact physical-slice / short-interval handoff for Route T

The fixed `1/100` reserve previously stopped the coefficient-faithful physical-slice receiver at
`mu = 39/10`.  That cutoff is not intrinsic.  Spending the already available Route-T moment
deficit itself gives a fixed positive reserve through

```text
mu <= 4 / (1 + 2 d),
```

where `d = maynardLongGlobalAmplitudeDeficit`.  The physical width at the endpoint has exponent

```text
1 - 1/mu = 3/4 - d/2 = 1/4 + routeTGapMomentNu.
```

Thus a prime-in-short-interval input need only cross this explicit exponent, infinitesimally below
`3/4`; it does not need to solve the signed boundary throughout the whole nominal `mu < 8` range.
-/

noncomputable section

namespace RHTower.Sieve

/-- Largest height exponent on which the physical-slice second moment retains the full Route-T
deficit as a fixed power reserve. -/
def routeTPhysicalSliceHandoffMu : ℝ :=
  4 / (1 + 2 * maynardLongGlobalAmplitudeDeficit)

/-- Additive-width exponent at the physical-slice handoff. -/
def routeTPhysicalSliceHandoffTheta : ℝ :=
  3 / 4 - maynardLongGlobalAmplitudeDeficit / 2

theorem routeTPhysicalSliceHandoffMu_pos :
    0 < routeTPhysicalSliceHandoffMu := by
  have hd : 0 < maynardLongGlobalAmplitudeDeficit :=
    maynardLongGlobalAmplitudeDeficit_pos
  dsimp only [routeTPhysicalSliceHandoffMu]
  positivity

theorem routeTPhysicalSliceHandoffTheta_eq_gapMoment :
    routeTPhysicalSliceHandoffTheta = 1 / 4 + routeTGapMomentNu := by
  simp only [routeTPhysicalSliceHandoffTheta, routeTGapMomentNu]
  ring

theorem routeTPhysicalSliceHandoffTheta_pos :
    0 < routeTPhysicalSliceHandoffTheta := by
  rw [routeTPhysicalSliceHandoffTheta_eq_gapMoment]
  linarith [routeTGapMomentNu_pos]

theorem routeTPhysicalSliceHandoffTheta_lt_three_fourths :
    routeTPhysicalSliceHandoffTheta < 3 / 4 := by
  dsimp only [routeTPhysicalSliceHandoffTheta]
  linarith [maynardLongGlobalAmplitudeDeficit_pos]

/-- Exact zero-density margin at the handoff.  A density envelope with coefficient three leaves
positive power room. -/
theorem routeT_densityCoefficient_three_margin_identity :
    1 - 3 * (1 - routeTPhysicalSliceHandoffTheta) =
      1 / 4 - 3 * maynardLongGlobalAmplitudeDeficit / 2 := by
  simp only [routeTPhysicalSliceHandoffTheta]
  ring

theorem routeT_densityCoefficient_three_fits_handoff :
    3 * (1 - routeTPhysicalSliceHandoffTheta) < 1 := by
  have hmargin := routeT_densityCoefficient_three_margin_identity
  have hd := maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  linarith

/-- Coefficient four is already on the wrong side of the handoff by exactly `2d`.  Thus the
short-interval pivot needs a genuine density coefficient below four; a generic `A=4` envelope
cannot be made to work by logarithmic refinements. -/
theorem routeT_densityCoefficient_four_excess_identity :
    4 * (1 - routeTPhysicalSliceHandoffTheta) =
      1 + 2 * maynardLongGlobalAmplitudeDeficit := by
  simp only [routeTPhysicalSliceHandoffTheta]
  ring

theorem routeT_densityCoefficient_four_fails_handoff :
    1 < 4 * (1 - routeTPhysicalSliceHandoffTheta) := by
  rw [routeT_densityCoefficient_four_excess_identity]
  linarith [maynardLongGlobalAmplitudeDeficit_pos]

/-- Exact endpoint identity: the physical width `x/T = x^(1-1/mu)` at the improved handoff has
exponent `1/4 + routeTGapMomentNu`, equivalently `3/4 - d/2`. -/
theorem routeTPhysicalSliceHandoff_widthExponent :
    1 - 1 / routeTPhysicalSliceHandoffMu =
      routeTPhysicalSliceHandoffTheta := by
  have hd : 0 < maynardLongGlobalAmplitudeDeficit :=
    maynardLongGlobalAmplitudeDeficit_pos
  have hden : 1 + 2 * maynardLongGlobalAmplitudeDeficit ≠ 0 := by
    positivity
  simp only [routeTPhysicalSliceHandoffMu, routeTPhysicalSliceHandoffTheta]
  field_simp [hden]
  ring

/-- The intrinsic lower-phase theorem.  Replacing the arbitrary `1/100` spend by the Route-T
deficit extends coefficient-faithful physical-slice control to the exact handoff exponent. -/
theorem routeT_physicalSlice_deficit_reserve_to_handoff
    {mu : ℝ} (hmu : mu ≤ routeTPhysicalSliceHandoffMu) :
    mu * (1 - routeTGapMomentNu) + maynardLongGlobalAmplitudeDeficit ≤ 2 := by
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  have hd0 : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have hdhalf : d < 1 / 2 := by
    have := maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
    dsimp only [d]
    linarith
  have hden0 : 0 < 1 + 2 * d := by linarith
  have hfactor : 0 ≤ 1 - routeTGapMomentNu := by
    linarith [routeTGapMomentNu_lt_half]
  have hmul :
      mu * (1 - routeTGapMomentNu) ≤
        (4 / (1 + 2 * d)) * (1 - routeTGapMomentNu) := by
    apply mul_le_mul_of_nonneg_right _ hfactor
    simpa only [routeTPhysicalSliceHandoffMu, d] using hmu
  have hendpoint :
      (4 / (1 + 2 * d)) * (1 - routeTGapMomentNu) + d ≤ 2 := by
    change (4 / (1 + 2 * d)) * (1 - (1 / 2 - d / 2)) + d ≤ 2
    have hquot : (2 + 2 * d) / (1 + 2 * d) ≤ 2 - d := by
      rw [div_le_iff₀ hden0]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hd0.le (by linarith : 2 * d - 1 ≤ 0)]
    calc
      (4 / (1 + 2 * d)) * (1 - (1 / 2 - d / 2)) + d =
          (2 + 2 * d) / (1 + 2 * d) + d := by ring
      _ ≤ 2 := by linarith
  linarith

/-- Above the handoff height, the physical width exponent is at least the explicit handoff
exponent.  This is the exact scalar gluing statement consumed by any future prime-short-interval
closure. -/
theorem routeTPhysicalSliceHandoffTheta_le_widthExponent
    {mu : ℝ} (hmu : routeTPhysicalSliceHandoffMu ≤ mu) :
    routeTPhysicalSliceHandoffTheta ≤ 1 - 1 / mu := by
  have hhpos : 0 < routeTPhysicalSliceHandoffMu :=
    routeTPhysicalSliceHandoffMu_pos
  have hmupos : 0 < mu := hhpos.trans_le hmu
  have hinv : 1 / mu ≤ 1 / routeTPhysicalSliceHandoffMu := by
    exact one_div_le_one_div_of_le hhpos hmu
  rw [← routeTPhysicalSliceHandoff_widthExponent]
  linarith

/-- Every positive Route-T height lies on one side of the exact handoff: either the physical slice
has fixed deficit reserve, or its additive physical width has exponent at least
`1/4 + routeTGapMomentNu < 3/4`. -/
theorem routeT_physicalSlice_or_upperWidth_handoff (mu : ℝ) :
    (mu * (1 - routeTGapMomentNu) + maynardLongGlobalAmplitudeDeficit ≤ 2) ∨
      (routeTPhysicalSliceHandoffTheta ≤ 1 - 1 / mu) := by
  by_cases hmu : mu ≤ routeTPhysicalSliceHandoffMu
  · exact Or.inl (routeT_physicalSlice_deficit_reserve_to_handoff hmu)
  · exact Or.inr (routeTPhysicalSliceHandoffTheta_le_widthExponent (le_of_not_ge hmu))

end RHTower.Sieve
