import GaloisForLFunctions.RHTower.RouteRPrimeLogEssentialCapSingularStokesLaw
import GaloisForLFunctions.HTGeometry.PrimeSieveDensityTelescope

/-!
# Prime-sieve variation reporter for Route R

Nested Euler-sieve losses form a positive mass-one source measure. Pairing that
measure with the prime-log essential-cap ports gives a convergent, positive-
calibrated all-prime reporter. No critical-line or cap-nullity premise occurs.
-/

open Complex
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Source-only mass of the `n`th nested prime-sieve loss. -/
def routeRPrimeSieveVariationWeight
    (e : ℕ ≃ Nat.Primes) (n : ℕ) : ℝ :=
  sieveDensity (sievePrefix e n) / ((e n : ℕ) : ℝ)

/-- The positive local multiplier remaining in the prime-log essential cap. -/
def routeRPrimeSieveCapFactor (p : Nat.Primes) : ℝ :=
  (1 - ((p : ℕ) : ℝ)⁻¹) * (2 - ((p : ℕ) : ℝ)⁻¹)

/-- Positive source calibration of the prime-sieve variation reporter. -/
def routeRPrimeSieveCapCalibration (e : ℕ ≃ Nat.Primes) : ℝ :=
  ∑' n : ℕ,
    routeRPrimeSieveVariationWeight e n *
      routeRPrimeSieveCapFactor (e n)

/-- The all-prime fixed-orientation cap reporter. -/
def ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter
    (e : ℕ ≃ Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  ∑' n : ℕ,
    (routeRPrimeSieveVariationWeight e n : ℂ) *
      ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort (e n) rho

theorem routeRPrimeSieveVariationWeight_pos
    (e : ℕ ≃ Nat.Primes) (n : ℕ) :
    0 < routeRPrimeSieveVariationWeight e n := by
  rw [routeRPrimeSieveVariationWeight]
  exact div_pos (sieveDensity_pos _) (by
    linarith [one_lt_prime_cast (e n)])

theorem hasSum_routeRPrimeSieveVariationWeight
    (e : ℕ ≃ Nat.Primes) :
    HasSum (fun n : ℕ => routeRPrimeSieveVariationWeight e n) 1 := by
  simpa [routeRPrimeSieveVariationWeight] using
    (hasSum_sieveDensity_div_prime e)

theorem tsum_routeRPrimeSieveVariationWeight
    (e : ℕ ≃ Nat.Primes) :
    ∑' n : ℕ, routeRPrimeSieveVariationWeight e n = 1 :=
  (hasSum_routeRPrimeSieveVariationWeight e).tsum_eq

theorem routeRPrimeSieveCapFactor_pos (p : Nat.Primes) :
    0 < routeRPrimeSieveCapFactor p := by
  have hpPos : 0 < ((p : ℕ) : ℝ) :=
    zero_lt_one.trans (one_lt_prime_cast p)
  have hinvPos : 0 < (((p : ℕ) : ℝ))⁻¹ := inv_pos.mpr hpPos
  have hinvLt : (((p : ℕ) : ℝ))⁻¹ < 1 :=
    (inv_lt_one_iff₀).mpr (Or.inr (one_lt_prime_cast p))
  rw [routeRPrimeSieveCapFactor]
  exact mul_pos (sub_pos.mpr hinvLt) (by linarith)

theorem routeRPrimeSieveCapFactor_lt_two (p : Nat.Primes) :
    routeRPrimeSieveCapFactor p < 2 := by
  have hpPos : 0 < ((p : ℕ) : ℝ) :=
    zero_lt_one.trans (one_lt_prime_cast p)
  have hinvPos : 0 < (((p : ℕ) : ℝ))⁻¹ := inv_pos.mpr hpPos
  have hinvLt : (((p : ℕ) : ℝ))⁻¹ < 1 :=
    (inv_lt_one_iff₀).mpr (Or.inr (one_lt_prime_cast p))
  have hfirst : 1 - (((p : ℕ) : ℝ))⁻¹ < 1 := by linarith
  have hsecondPos : 0 < 2 - (((p : ℕ) : ℝ))⁻¹ := by linarith
  have hsecondLe : 2 - (((p : ℕ) : ℝ))⁻¹ ≤ 2 := by linarith
  rw [routeRPrimeSieveCapFactor]
  calc
    (1 - (((p : ℕ) : ℝ))⁻¹) * (2 - (((p : ℕ) : ℝ))⁻¹) <
        1 * (2 - (((p : ℕ) : ℝ))⁻¹) :=
      mul_lt_mul_of_pos_right hfirst hsecondPos
    _ ≤ 1 * 2 := mul_le_mul_of_nonneg_left hsecondLe zero_le_one
    _ = 2 := one_mul 2

theorem summable_routeRPrimeSieveCapCalibrationTerm
    (e : ℕ ≃ Nat.Primes) :
    Summable (fun n : ℕ =>
      routeRPrimeSieveVariationWeight e n *
        routeRPrimeSieveCapFactor (e n)) := by
  have hmajor : Summable (fun n : ℕ =>
      2 * routeRPrimeSieveVariationWeight e n) :=
    (hasSum_routeRPrimeSieveVariationWeight e).summable.mul_left 2
  refine Summable.of_nonneg_of_le
    (fun n => (mul_pos (routeRPrimeSieveVariationWeight_pos e n)
      (routeRPrimeSieveCapFactor_pos (e n))).le)
    (fun n => by
      simpa [mul_comm] using (mul_lt_mul_of_pos_left
        (routeRPrimeSieveCapFactor_lt_two (e n))
        (routeRPrimeSieveVariationWeight_pos e n)).le)
    hmajor

theorem routeRPrimeSieveCapCalibration_pos (e : ℕ ≃ Nat.Primes) :
    0 < routeRPrimeSieveCapCalibration e := by
  exact (summable_routeRPrimeSieveCapCalibrationTerm e).tsum_pos
    (fun n => (mul_pos (routeRPrimeSieveVariationWeight_pos e n)
      (routeRPrimeSieveCapFactor_pos (e n))).le)
    0
    (mul_pos (routeRPrimeSieveVariationWeight_pos e 0)
      (routeRPrimeSieveCapFactor_pos (e 0)))

theorem routeRPrimeSieveCapCalibration_lt_two (e : ℕ ≃ Nat.Primes) :
    routeRPrimeSieveCapCalibration e < 2 := by
  have hlt :
      (∑' n : ℕ, routeRPrimeSieveVariationWeight e n *
        routeRPrimeSieveCapFactor (e n)) <
      ∑' n : ℕ, 2 * routeRPrimeSieveVariationWeight e n :=
    (summable_routeRPrimeSieveCapCalibrationTerm e).tsum_lt_tsum
      (i := 0)
      (fun n => by
        simpa [mul_comm] using (mul_lt_mul_of_pos_left
          (routeRPrimeSieveCapFactor_lt_two (e n))
          (routeRPrimeSieveVariationWeight_pos e n)).le)
      (by
        simpa [mul_comm] using (mul_lt_mul_of_pos_left
          (routeRPrimeSieveCapFactor_lt_two (e 0))
          (routeRPrimeSieveVariationWeight_pos e 0)))
      ((hasSum_routeRPrimeSieveVariationWeight e).summable.mul_left 2)
  rw [routeRPrimeSieveCapCalibration]
  simpa [tsum_mul_left, tsum_routeRPrimeSieveVariationWeight e] using hlt

theorem routeRPrimeSieveCapCalibration_ne_zero (e : ℕ ≃ Nat.Primes) :
    routeRPrimeSieveCapCalibration e ≠ 0 :=
  (routeRPrimeSieveCapCalibration_pos e).ne'

/-- Absolute convergence of the all-prime reporter is a consequence, not a
hypothesis. -/
theorem summable_ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter
    (e : ℕ ≃ Nat.Primes) (rho : XiDivisorSupport) :
    Summable (fun n : ℕ =>
      (routeRPrimeSieveVariationWeight e n : ℂ) *
        ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort (e n) rho) := by
  have hcomplex : Summable (fun n : ℕ =>
      ((routeRPrimeSieveVariationWeight e n *
        routeRPrimeSieveCapFactor (e n) : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.hasSum
      (summable_routeRPrimeSieveCapCalibrationTerm e).hasSum).summable
  refine (hcomplex.mul_right
    (((primeDepthBVWoldXiCenteredRate rho : ℝ) : ℂ) *
      ccmRationalAdelicPrimeXiCartierCoefficient rho)).congr ?_
  intro n
  rw [ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort_eq]
  rw [routeRPrimeSieveCapFactor]
  push_cast
  ring

/-- Exact positive-calibration factorization of the all-prime reporter. -/
theorem ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter_eq
    (e : ℕ ≃ Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter e rho =
      ((primeDepthBVWoldXiCenteredRate rho *
        routeRPrimeSieveCapCalibration e : ℝ) : ℂ) *
          ccmRationalAdelicPrimeXiCartierCoefficient rho := by
  have hcomplex : HasSum (fun n : ℕ =>
      ((routeRPrimeSieveVariationWeight e n *
        routeRPrimeSieveCapFactor (e n) : ℝ) : ℂ))
      (routeRPrimeSieveCapCalibration e : ℂ) :=
    Complex.ofRealCLM.hasSum
      (summable_routeRPrimeSieveCapCalibrationTerm e).hasSum
  have hscaled := hcomplex.mul_right
    (((primeDepthBVWoldXiCenteredRate rho : ℝ) : ℂ) *
      ccmRationalAdelicPrimeXiCartierCoefficient rho)
  rw [ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter]
  calc
    (∑' n : ℕ, (routeRPrimeSieveVariationWeight e n : ℂ) *
      ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort (e n) rho) =
        ∑' n : ℕ,
          ((routeRPrimeSieveVariationWeight e n *
            routeRPrimeSieveCapFactor (e n) : ℝ) : ℂ) *
            (((primeDepthBVWoldXiCenteredRate rho : ℝ) : ℂ) *
              ccmRationalAdelicPrimeXiCartierCoefficient rho) := by
      apply tsum_congr
      intro n
      rw [ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort_eq,
        routeRPrimeSieveCapFactor]
      push_cast
      ring
    _ = (routeRPrimeSieveCapCalibration e : ℂ) *
          (((primeDepthBVWoldXiCenteredRate rho : ℝ) : ℂ) *
            ccmRationalAdelicPrimeXiCartierCoefficient rho) :=
      hscaled.tsum_eq
    _ = ((primeDepthBVWoldXiCenteredRate rho *
          routeRPrimeSieveCapCalibration e : ℝ) : ℂ) *
            ccmRationalAdelicPrimeXiCartierCoefficient rho := by
      push_cast
      ring

/-- Positive source calibration makes the reporter coefficient-faithful. -/
theorem ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter_eq_zero_iff
    (e : ℕ ≃ Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter e rho = 0 ↔
      primeDepthBVWoldXiCenteredRate rho = 0 := by
  rw [ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter_eq]
  simp [routeRPrimeSieveCapCalibration_ne_zero e,
    ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho]

/-- The new all-prime source reporter detects exactly the same fixed physical
port as singular Stokes flatness. -/
theorem ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter_eq_zero_iff_flat
    (e : ℕ ≃ Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter e rho = 0 ↔
      CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho :=
  (ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter_eq_zero_iff e rho).trans
    (ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).symm

/-- Global reporter flatness is RH. This is a reduction theorem, not a proof
of reporter flatness. -/
theorem forall_ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter_eq_zero_iff_RH
    (e : ℕ ≃ Nat.Primes) :
    (∀ rho : XiDivisorSupport,
      ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter e rho = 0) ↔
      RiemannHypothesis := by
  rw [← forall_ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff_RH]
  apply forall_congr'
  intro rho
  exact
    ccmRationalAdelicPrimeXiPrimeSieveVariationCapReporter_eq_zero_iff_flat e rho

end

end RHTower
