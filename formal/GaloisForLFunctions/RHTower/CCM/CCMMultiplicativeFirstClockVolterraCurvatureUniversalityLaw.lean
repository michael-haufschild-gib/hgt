import GaloisForLFunctions.RHTower.CCM.CCMFirstClockVolterra
import GaloisForLFunctions.RHTower.CCM.CCMMultiplicativeScrewCurvature

/-!
# Multiplicative first-clock Volterra curvature

The logarithmically sampled rectangular Weil form is a multiplicative midpoint curvature of the
Xi screw divisor.  The first physical clock independently expresses its rational divisor as that
screw value plus an exact signed Volterra history.  Applying the latter at all four multiplicative
apertures turns the rectangular detector into an exact finite difference of first-clock carriers
with memory corrections.
-/

open Complex

namespace RHTower

noncomputable section

/-- Signed Volterra memory relating the Xi screw divisor to the complete first-clock carrier. -/
def ccmFirstClockXiVolterraMemory (L : ℝ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..L,
    (((2 * Real.pi / L : ℝ) : ℂ) *
      Real.sin ((2 * Real.pi / L) * t)) * xiScrewDivisor t

/-- **Multiplicative first-clock Volterra-curvature universality law.**  On the physical aperture
range, the rectangular Weil value on `n, m*n, m^(2 : ℕ)*n` is exactly the multiplicative midpoint
curvature of the first-clock rational divisor after removing its Volterra memory. -/
theorem xiWeilPolarization_rectangular_log_mul_sq_eq_firstClockVolterraCurvature
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hLm : Real.pi / 2 ≤ Real.log m)
    (hLn : Real.pi / 2 ≤ Real.log n)
    (hLmn : Real.pi / 2 ≤ Real.log ((m * n : ℕ) : ℝ))
    (hLm2n : Real.pi / 2 ≤ Real.log ((m ^ 2 * n : ℕ) : ℝ)) :
    xiWeilPolarization
        (xiRectangularTwoEdgeTransform (Real.log m)
          (Real.log ((m ^ 2 * n : ℕ) : ℝ) / 2))
        (xiRectangularTwoEdgeTransform (Real.log m)
          (Real.log ((m ^ 2 * n : ℕ) : ℝ) / 2)) =
      2 *
        ((ccmFirstClockXiRationalDivisor (Real.log ((m ^ 2 * n : ℕ) : ℝ)) -
            ccmFirstClockXiVolterraMemory (Real.log ((m ^ 2 * n : ℕ) : ℝ))) +
          (ccmFirstClockXiRationalDivisor (Real.log n) -
            ccmFirstClockXiVolterraMemory (Real.log n)) -
          2 * (ccmFirstClockXiRationalDivisor (Real.log ((m * n : ℕ) : ℝ)) -
            ccmFirstClockXiVolterraMemory (Real.log ((m * n : ℕ) : ℝ))) +
          2 * (ccmFirstClockXiRationalDivisor (Real.log m) -
            ccmFirstClockXiVolterraMemory (Real.log m))) := by
  have hvolM2N := ccmFirstClockXiRationalDivisor_eq_screw_add_volterra hLm2n
  have hvolN := ccmFirstClockXiRationalDivisor_eq_screw_add_volterra hLn
  have hvolMN := ccmFirstClockXiRationalDivisor_eq_screw_add_volterra hLmn
  have hvolM := ccmFirstClockXiRationalDivisor_eq_screw_add_volterra hLm
  change ccmFirstClockXiRationalDivisor (Real.log ((m ^ 2 * n : ℕ) : ℝ)) =
      xiScrewDivisor (Real.log ((m ^ 2 * n : ℕ) : ℝ)) +
        ccmFirstClockXiVolterraMemory (Real.log ((m ^ 2 * n : ℕ) : ℝ)) at hvolM2N
  change ccmFirstClockXiRationalDivisor (Real.log n) =
      xiScrewDivisor (Real.log n) + ccmFirstClockXiVolterraMemory (Real.log n) at hvolN
  change ccmFirstClockXiRationalDivisor (Real.log ((m * n : ℕ) : ℝ)) =
      xiScrewDivisor (Real.log ((m * n : ℕ) : ℝ)) +
        ccmFirstClockXiVolterraMemory (Real.log ((m * n : ℕ) : ℝ)) at hvolMN
  change ccmFirstClockXiRationalDivisor (Real.log m) =
      xiScrewDivisor (Real.log m) + ccmFirstClockXiVolterraMemory (Real.log m) at hvolM
  rw [xiWeilPolarization_rectangular_log_mul_sq_eq_screwCurvature hm hn]
  rw [hvolM2N, hvolN, hvolMN, hvolM]
  ring

end

end RHTower
