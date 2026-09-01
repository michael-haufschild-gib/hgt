import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms
import GaloisForLFunctions.RHTower.SoninSemilocalTwoPlaceCovariance

/-!
# Supercritical sharpness mechanisms for semilocal prime association

The paper's midpoint square-root alternative applies directly to the strictly positively
associated degree-zero Gram masses of two concrete prime Poisson factors.
-/

open MeasureTheory

noncomputable section

namespace RHTower.SemilocalTwoPlace

open RHTower

/-- One-place degree-zero Gram mass for the prime Poisson factor at `p`. -/
def semilocalPrimeMass (p : ℕ) : ℝ :=
  ∫ s, primeFactor ((p : ℝ) ^ (-(1 : ℝ) / 2)) (Real.log p) s
    ∂semilocalArchimedeanGammaMeasure

/-- Joint degree-zero Gram mass for prime Poisson factors at `p` and `q`. -/
def semilocalPrimeJointMass (p q : ℕ) : ℝ :=
  ∫ s, primeFactor ((p : ℝ) ^ (-(1 : ℝ) / 2)) (Real.log p) s
      * primeFactor ((q : ℝ) ^ (-(1 : ℝ) / 2)) (Real.log q) s
    ∂semilocalArchimedeanGammaMeasure

/-- The concrete prime pair `(2,3)` is strictly positively associated. -/
theorem semilocal_twoThreePrime_association :
    semilocalPrimeMass 2 * semilocalPrimeMass 3 < semilocalPrimeJointMass 2 3 := by
  simpa [semilocalPrimeMass, semilocalPrimeJointMass] using
    (semilocal_prime_twoPlace_association (p := 2) (q := 3) (by norm_num) (by norm_num))

/-- Midpoint extraction for the concrete `(2,3)` prime pair: at least one one-place Gram mass
is no larger than the square root of their joint mass. -/
theorem semilocal_twoThreePrime_midpoint_sqrt_alternative :
    semilocalPrimeMass 2 ≤ Real.sqrt (semilocalPrimeJointMass 2 3) ∨
      semilocalPrimeMass 3 ≤ Real.sqrt (semilocalPrimeJointMass 2 3) := by
  have h2 : 0 < semilocalPrimeMass 2 := by
    unfold semilocalPrimeMass
    exact integral_primeFactor_pos (primeRadius_pos (p := 2) (by norm_num)).le
      (primeRadius_lt_one (p := 2) (by norm_num)) (Real.log 2)
  have h3 : 0 < semilocalPrimeMass 3 := by
    unfold semilocalPrimeMass
    exact integral_primeFactor_pos (primeRadius_pos (p := 3) (by norm_num)).le
      (primeRadius_lt_one (p := 3) (by norm_num)) (Real.log 3)
  have hassoc := semilocal_twoThreePrime_association
  have hjoint : 0 < semilocalPrimeJointMass 2 3 := (mul_pos h2 h3).trans hassoc
  exact GaloisForLFunctions.HTGeometry.le_sqrt_or_le_sqrt_of_mul_le
    hjoint.le hassoc.le

end RHTower.SemilocalTwoPlace
