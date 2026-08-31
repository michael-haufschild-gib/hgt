import GaloisForLFunctions.RHTower.CoupledFloorMobiusAffineRieszHandoff
import GaloisForLFunctions.RHTower.SuzukiTransitionCoreAbelSourceMultiGateWeld

/-!
# Cofinal coupled-floor source landing in the aligned Xi transition core

The coupled floor--Möbius incidence already has a coefficient-faithful affine Riesz readout, and
the aligned Suzuki transition core already carries the completed signed Abel scalar through
Gamma completion, Xi selection, analytic multiplicity, both reflection orientations, and the
four-orientation non-spectral short.  This module closes the missing cross-complex handoff.

The Euler edge is removed and the polar-lattice, polar, and archimedean corrections are inserted
before Xi selection.  The resulting literal source readout differs from the exact completed Abel
source by only the normalized CFI landing error.  A source-selected positive critical schedule
makes that error smaller than the inverse square aperture, while the exact error-subtracted value
drives every aligned Xi short.  No boundedness, sign, or RH hypothesis is assumed.
-/

open Complex Filter Matrix Set Topology
open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

/-- Completed pre-divisor CFI readout.  Every correction is inserted before Xi selection. -/
def coupledFloorMobiusCompletedAbelReadout (omega : ℝ) (M : ℕ) : ℝ :=
  (coupledFloorMobiusAffineRieszReadout omega M -
      2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1) +
      coherentSquareRootPolarLatticeDefect M) / M -
    unitRieszSuzukiPolarCorrection (Real.log M) +
    unitRieszSuzukiArchCorrection (Real.log M)

/-- The only discrepancy between the completed CFI readout and the completed Abel source. -/
def coupledFloorMobiusCompletedAbelLandingError (omega : ℝ) (M : ℕ) : ℝ :=
  (coupledFloorMobiusAffineRieszReadout omega M -
    mobiusDivisorSquareRootAbelMoment M) / M

/-- Exact pre-divisor landing law.  It retains the signed error instead of hiding it in a norm. -/
theorem coupledFloorMobiusCompletedAbelReadout_eq_source_add_error
    {omega : ℝ} {M : ℕ} (hM : 1 ≤ M) :
    coupledFloorMobiusCompletedAbelReadout omega M =
      suzukiTransitionCoreCompletedAbelSource M +
        coupledFloorMobiusCompletedAbelLandingError omega M := by
  rw [coupledFloorMobiusCompletedAbelReadout,
    suzukiTransitionCoreCompletedAbelSource,
    coupledFloorMobiusCompletedAbelLandingError,
    mobiusDivisorSquareRootAbelMoment_eq_coherent_add_gammaBoundary hM]
  ring

/-- A `1/M` affine-Riesz landing error becomes `1/M^2` after completed-source normalization. -/
theorem abs_coupledFloorMobiusCompletedAbelLandingError_lt_inv_sq
    {omega : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (herror :
      |coupledFloorMobiusAffineRieszReadout omega M -
        mobiusDivisorSquareRootAbelMoment M| < 1 / (M : ℝ)) :
    |coupledFloorMobiusCompletedAbelLandingError omega M| <
      1 / (M : ℝ) ^ 2 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rw [coupledFloorMobiusCompletedAbelLandingError, abs_div, abs_of_pos hMR]
  calc
    |coupledFloorMobiusAffineRieszReadout omega M -
          mobiusDivisorSquareRootAbelMoment M| / (M : ℝ) <
        (1 / (M : ℝ)) / (M : ℝ) :=
      div_lt_div_of_pos_right herror hMR
    _ = 1 / (M : ℝ) ^ 2 := by ring

/-- Exact CFI-to-SP-E/Route-P multi-gate source law.  One positive source-selected critical
schedule has inverse-square completed landing error.  After subtracting that explicit error, the
same scalar drives the growing-rank transition core and every multiplicity-faithful Xi short with
both reflection orientations and the four-orientation non-spectral contraction. -/
theorem exists_coupledFloorMobiusCompletedAbelXiFissionSchedule :
    ∃ omega : ℕ → ℝ,
      Filter.Tendsto omega Filter.atTop (nhds 0) ∧
      ∀ N : ℕ, 1 ≤ N →
        0 < omega N ∧
        omega N < 1 / ((N : ℝ) + 1) ∧
        |coupledFloorMobiusCompletedAbelLandingError (omega N) (N + 1)| <
          1 / (((N + 1 : ℕ) : ℝ) ^ 2) ∧
        ∀ (_hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0)
            (rho : XiDivisorSupport) (r : ℝ),
          suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy (N + 1) rho r =
            2 * (xiSupportMultiplicity rho : ℝ) *
              suzukiNaturalApertureTransitionCoreCauchyEnergy (N + 1) *
                ((coupledFloorMobiusCompletedAbelReadout (omega N) (N + 1) -
                    coupledFloorMobiusCompletedAbelLandingError (omega N) (N + 1)) /
                  unitRieszCoherentPrimeOutgoingCharge (N + 1)) ^ 2 *
                Complex.normSq
                  (routePXiBaseConormalResidueFeature (rho : ℂ) r) := by
  obtain ⟨omega, homega, _hlimit, hpoint⟩ :=
    exists_coupledFloorMobiusAffineRieszCofinalSchedule
  refine ⟨omega, homega, ?_⟩
  intro N hN
  have hM : 1 ≤ N + 1 := by omega
  have hMtwo : 2 ≤ N + 1 := by omega
  have hpointError :
      |coupledFloorMobiusAffineRieszReadout (omega N) (N + 1) -
        mobiusDivisorSquareRootAbelMoment (N + 1)| <
          1 / (((N + 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (hpoint N).2.2
  refine ⟨(hpoint N).1, (hpoint N).2.1,
    abs_coupledFloorMobiusCompletedAbelLandingError_lt_inv_sq hM
      hpointError, ?_⟩
  intro hcharge rho r
  rw [suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy_eq_completedAbelSource
    hMtwo hcharge]
  have hlanding :=
    coupledFloorMobiusCompletedAbelReadout_eq_source_add_error
      (omega := omega N) hM
  rw [show suzukiTransitionCoreCompletedAbelSource (N + 1) =
      coupledFloorMobiusCompletedAbelReadout (omega N) (N + 1) -
        coupledFloorMobiusCompletedAbelLandingError (omega N) (N + 1) by
      linarith]

end

end GaloisForLFunctions.RHTower
