import GaloisForLFunctions.RHTower.RouteRResolutionCoreNoetherCharge
import GaloisForLFunctions.RHTower.XiHermitianStokesSupportBarcode

/-!
# Xi Stokes--Roos persistence bridge

The marked Hermitian Stokes support mismatch and the Gamma-damped Route R completion defect are
constructed independently.  This module proves that they carry the same resolution scale.  More
strongly, the Stokes barcode width is the exact aperture at which the literal fixed-tail derived
class changes from surviving to exact.

For an Xi support point `rho` and aperture `epsilon`, the damped Roos class survives precisely when
the Stokes mismatch is nonempty and `epsilon` is at most its width.  Thus the support interval is
not only another critical-line detector: its width is the death threshold of a source-derived
completion class.  Multiplicity weights the same threshold through the conserved Noether charge.

This is a comparison theorem.  It does not prove that the barcode is empty.
-/

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.BoundaryMigration

namespace RHTower

noncomputable section

/-- Stokes support width and fixed-tail completion-core radius are the same physical scale. -/
theorem xiHermitianStokesRadialBarcodeWidth_eq_resolutionCoreRadius
    (rho : XiDivisorSupport) :
    xiHermitianStokesRadialBarcodeWidth (rho : ℂ) =
      routeRPrimeGammaXiResolutionCoreRadius rho := by
  rw [xiHermitianStokesRadialBarcodeWidth,
    routeRPrimeGammaXiResolutionCoreRadius]
  have hscale :
      2 * (rho : ℂ).re - 1 = 2 * ((rho : ℂ).re - 1 / 2) := by
    ring
  rw [hscale, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

/-- The Stokes support width is the sharp exactness wall of the damped completion class. -/
theorem routeRPrimeGammaXiResolutionExactAt_iff_stokesBarcode
    (rho : XiDivisorSupport) (epsilon : ℝ) :
    (routeRPrimeGammaResolutionExactnessProfile
      (2 * (rho : ℂ).re - 1)).exactAt epsilon ↔
      xiHermitianStokesRadialBarcode (rho : ℂ) = ∅ ∨
        xiHermitianStokesRadialBarcodeWidth (rho : ℂ) < epsilon := by
  rw [(routeRPrimeGammaResolutionExactnessProfile
    (2 * (rho : ℂ).re - 1)).exactAt_iff]
  change
    (routeRPrimeGammaXiResolutionCoreRadius rho = 0 ∨
      routeRPrimeGammaXiResolutionCoreRadius rho < epsilon) ↔ _
  rw [routeRPrimeGammaXiResolutionCoreRadius_eq_zero_iff,
    xiHermitianStokesRadialBarcode_eq_empty_iff,
    xiHermitianStokesRadialBarcodeWidth_eq_resolutionCoreRadius]

/-- Literal derived-class form: survival lasts exactly through the marked Stokes width. -/
theorem routeRPrimeGammaXiTailRoosSurvival_iff_stokesBarcode
    (rho : XiDivisorSupport) (epsilon : ℝ) :
    routeRTailRoosExactnessFlag ∈ ExFlag.survival
        (routeRDiagonalMismatchInIdeal
          (routeRPrimeGammaDampedBocksteinSequence epsilon
            (2 * (rho : ℂ).re - 1))) ↔
      xiHermitianStokesRadialBarcode (rho : ℂ) ≠ ∅ ∧
        epsilon ≤ xiHermitianStokesRadialBarcodeWidth (rho : ℂ) := by
  have hexact := routeRPrimeGammaResolutionExactAt_iff_no_survival
    epsilon (2 * (rho : ℂ).re - 1)
  rw [routeRPrimeGammaXiResolutionExactAt_iff_stokesBarcode rho epsilon] at hexact
  constructor
  · intro hsurvival
    constructor
    · intro hempty
      exact (hexact.mp (Or.inl hempty)) hsurvival
    · by_contra hnotle
      exact (hexact.mp (Or.inr (lt_of_not_ge hnotle))) hsurvival
  · rintro ⟨hne, hle⟩
    by_contra hnotSurvival
    rcases hexact.mpr hnotSurvival with hempty | hlt
    · exact hne hempty
    · exact (not_lt_of_ge hle) hlt

/-- Cofinal exactness is exactly disappearance of the marked Stokes support mismatch. -/
theorem routeRPrimeGammaXiCofinallyExact_iff_stokesBarcode_eq_empty
    (rho : XiDivisorSupport) :
    (routeRPrimeGammaResolutionExactnessProfile
      (2 * (rho : ℂ).re - 1)).CofinallyExact ↔
      xiHermitianStokesRadialBarcode (rho : ℂ) = ∅ := by
  rw [routeRPrimeGammaXiCofinallyExact_iff_re_eq_half,
    xiHermitianStokesRadialBarcode_eq_empty_iff]

/-- Multiplicity-weighted Noether charge is the Stokes persistence width per divisor copy. -/
theorem abs_routeRPrimeGammaXiNoetherOrientationCharge_eq_barcodeWidth
    (rho : XiDivisorSupport) :
    |routeRPrimeGammaXiNoetherOrientationCharge rho| =
      ((analyticOrderAt xi (rho : ℂ)).toNat : ℝ) / 2 *
        xiHermitianStokesRadialBarcodeWidth (rho : ℂ) := by
  rw [abs_routeRPrimeGammaXiNoetherOrientationCharge_eq,
    xiHermitianStokesRadialBarcodeWidth_eq_resolutionCoreRadius]

end

end RHTower
