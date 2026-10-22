import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarParabolicCenteredBoundary
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarParabolicCompletedSourceBoundary

/-!
# Source-centered completed parabolic boundary

The finite matched--quantile codiagonal is not the completed source: the oriented terminal
quantile-to-physical-polar interval is indispensable.  This module performs the canonical
barycentric parabolic centering on that *completed* source, at the physical height `2a` of every
positive Suzuki aperture.

Its boundary mass is strictly positive without an extra hypothesis.  The common null shift of
the completed codiagonal and source boundary preserves their complete parabolic current.  Dividing
that current by the retained source mass gives one coefficient-faithful completed charge.  The
last theorem transports it exactly to the finite centered strict-cross current minus the full
literal terminal interaction and terminal form.

No sign, convergence, or RH consequence is asserted.  The produced charge is the actual
terminal-completed object whose cofinal control would be needed by the route.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The initial quantile mass coordinate is exactly `2`; indices `0` and `1` carry no
von-Mangoldt atom. -/
theorem ccmActualHeadQuantilePolarCoordinate_two :
    ccmActualHeadQuantilePolarCoordinate 2 = 2 := by
  have hzero : criticalMellinAtomWeight 0 = 0 := by
    unfold criticalMellinAtomWeight
    have hΛ : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by
      norm_num [ArithmeticFunction.vonMangoldt_eq_zero_iff]
    rw [hΛ]
    ring
  have hone : criticalMellinAtomWeight 1 = 0 := by
    unfold criticalMellinAtomWeight
    norm_num [ArithmeticFunction.vonMangoldt_apply_one]
  rw [ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative]
  norm_num [ccmOutgoingPrimeCumulative, Finset.sum_range_succ, hzero, hone]

/-- Zeroth coordinate of the literal completed quantile aggregate.  This keeps the terminal
orientation as an oriented mass difference. -/
theorem ccmActualHeadCompletedQuantileParabolicAggregate_zero (K : ℕ) (T : ℝ) :
    ccmActualHeadCompletedQuantileParabolicAggregate K T 0 =
      ccmActualHeadPolarMassCoordinate T - ccmActualHeadQuantilePolarCoordinate 2 := by
  rw [ccmActualHeadCompletedQuantileParabolicAggregate_eq_moment]
  simp [ccmParabolicMoment]

private theorem ccmActualHeadPolarMassCoordinate_gt_two {T : ℝ} (hT : 0 < T) :
    2 < ccmActualHeadPolarMassCoordinate T := by
  unfold ccmActualHeadPolarMassCoordinate
  have hexp : 1 < Real.exp (T / 2) := Real.one_lt_exp_iff.mpr (by linarith)
  nlinarith

/-- The completed source boundary mass separates the finite literal head mass and the oriented
terminal mass. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_zero
    (K : ℕ) (T : ℝ) :
    ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K T 0 =
      ccmActualHeadParabolicMass K +
        (ccmActualHeadPolarMassCoordinate T - ccmActualHeadQuantilePolarCoordinate 2) := by
  unfold ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary
  simp only [Pi.add_apply]
  rw [ccmActualHeadMatchedParabolicAggregate_zero,
    ccmActualHeadCompletedQuantileParabolicAggregate_zero]

/-- Positive physical apertures make the full terminal-completed source boundary strictly
mass-positive, with no added condition on the finite head. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicPhysicalSourceBoundary_zero_pos
    (a : SuzukiPositiveAperture) (K : ℕ) :
    0 < ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (2 * a.1) 0 := by
  have hT : 0 < 2 * a.1 := by nlinarith [a.2]
  rw [ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_zero,
    ccmActualHeadQuantilePolarCoordinate_two]
  nlinarith [ccmActualHeadParabolicMass_pos K,
    ccmActualHeadPolarMassCoordinate_gt_two hT]

/-- Retained mass of the literal terminal-completed source at physical aperture `a`. -/
def ccmActualHeadMatchedCompletedQuantileParabolicPhysicalBoundaryMass
    (a : SuzukiPositiveAperture) (K : ℕ) : ℝ :=
  ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (2 * a.1) 0

/-- Unique common null shift which barycentrically centers the completed source boundary. -/
def ccmActualHeadMatchedCompletedQuantileParabolicCenteredShift
    (a : SuzukiPositiveAperture) (K : ℕ) : ℝ :=
  -ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (2 * a.1) 1 /
    ccmActualHeadMatchedCompletedQuantileParabolicPhysicalBoundaryMass a K

/-- Completed source boundary in its canonical physical barycentric gauge. -/
def ccmActualHeadMatchedCompletedQuantileParabolicCenteredSourceBoundary
    (a : SuzukiPositiveAperture) (K : ℕ) : Fin 3 → ℝ :=
  ccmParabolicShift (ccmActualHeadMatchedCompletedQuantileParabolicCenteredShift a K)
    (ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (2 * a.1))

/-- Full matched-minus-completed-quantile codiagonal in the same physical gauge. -/
def ccmActualHeadMatchedCompletedQuantileParabolicCenteredCodiagonal
    (a : SuzukiPositiveAperture) (K : ℕ) : Fin 3 → ℝ :=
  ccmParabolicShift (ccmActualHeadMatchedCompletedQuantileParabolicCenteredShift a K)
    (ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K (2 * a.1))

/-- Coefficient-faithful normalized completed source current. -/
def ccmActualHeadMatchedCompletedQuantileParabolicCenteredCharge
    (a : SuzukiPositiveAperture) (K : ℕ) : ℝ :=
  ccmParabolicPairing
    (ccmActualHeadMatchedCompletedQuantileParabolicCenteredCodiagonal a K)
    (ccmActualHeadMatchedCompletedQuantileParabolicCenteredSourceBoundary a K) /
      ccmActualHeadMatchedCompletedQuantileParabolicPhysicalBoundaryMass a K

theorem ccmActualHeadMatchedCompletedQuantileParabolicPhysicalBoundaryMass_pos
    (a : SuzukiPositiveAperture) (K : ℕ) :
    0 < ccmActualHeadMatchedCompletedQuantileParabolicPhysicalBoundaryMass a K := by
  exact ccmActualHeadMatchedCompletedQuantileParabolicPhysicalSourceBoundary_zero_pos a K

/-- The completed source boundary is centered at its literal barycenter. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicCenteredSourceBoundary_one
    (a : SuzukiPositiveAperture) (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicCenteredSourceBoundary a K 1 = 0 := by
  change (-ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (2 * a.1) 1 /
      ccmActualHeadMatchedCompletedQuantileParabolicPhysicalBoundaryMass a K) *
        ccmActualHeadMatchedCompletedQuantileParabolicPhysicalBoundaryMass a K +
      ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (2 * a.1) 1 = 0
  have hne : ccmActualHeadMatchedCompletedQuantileParabolicPhysicalBoundaryMass a K ≠ 0 :=
    (ccmActualHeadMatchedCompletedQuantileParabolicPhysicalBoundaryMass_pos a K).ne'
  field_simp
  ring

/-- Common centering preserves the complete terminal-aware parabolic current. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicCentered_pairing_eq
    (a : SuzukiPositiveAperture) (K : ℕ) :
    ccmParabolicPairing
        (ccmActualHeadMatchedCompletedQuantileParabolicCenteredCodiagonal a K)
        (ccmActualHeadMatchedCompletedQuantileParabolicCenteredSourceBoundary a K) =
      ccmParabolicPairing
        (ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K (2 * a.1))
        (ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (2 * a.1)) := by
  rw [ccmActualHeadMatchedCompletedQuantileParabolicCenteredCodiagonal,
    ccmActualHeadMatchedCompletedQuantileParabolicCenteredSourceBoundary,
    ccmParabolicPairing_shift_same]

/-- The normalized completed charge is exactly the complete source current divided by its
positive physical boundary mass. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicPhysicalBoundaryMass_mul_centeredCharge
    (a : SuzukiPositiveAperture) (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicPhysicalBoundaryMass a K *
        ccmActualHeadMatchedCompletedQuantileParabolicCenteredCharge a K =
      ccmParabolicPairing
        (ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K (2 * a.1))
        (ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (2 * a.1)) := by
  rw [ccmActualHeadMatchedCompletedQuantileParabolicCenteredCharge,
    ← ccmActualHeadMatchedCompletedQuantileParabolicCentered_pairing_eq]
  have hne : ccmActualHeadMatchedCompletedQuantileParabolicPhysicalBoundaryMass a K ≠ 0 :=
    (ccmActualHeadMatchedCompletedQuantileParabolicPhysicalBoundaryMass_pos a K).ne'
  field_simp

/-- **Completed boundary-transport law.** The physical normalized charge equals the finite
centered strict-cross current after subtraction of the terminal's full interaction with the
quantile aggregate and its own parabolic form.  No terminal ordering or cancellation is assumed.
-/
theorem ccmActualHeadMatchedCompletedQuantileParabolicPhysicalBoundaryMass_mul_centeredCharge_eq_finite_sub_terminal
    (a : SuzukiPositiveAperture) (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicPhysicalBoundaryMass a K *
        ccmActualHeadMatchedCompletedQuantileParabolicCenteredCharge a K =
      2 * ccmActualHeadParabolicMass K *
          ccmActualHeadMatchedQuantileParabolicCenteredCharge K -
        (2 * ccmParabolicPairing (ccmActualHeadQuantileParabolicAggregate K)
            (ccmActualHeadQuantileParabolicTerminal K (2 * a.1)) +
          ccmParabolicForm (ccmActualHeadQuantileParabolicTerminal K (2 * a.1))) := by
  rw [ccmActualHeadMatchedCompletedQuantileParabolicPhysicalBoundaryMass_mul_centeredCharge,
    ccmActualHeadMatchedCompletedQuantileParabolic_pairing_eq_finite_sub_terminal,
    ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_crossKernel,
    ← two_mul_ccmActualHeadParabolicMass_mul_centeredCharge_eq_crossKernel]

end RHTower
