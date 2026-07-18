import GaloisForLFunctions.HTGeometry.PrimeClockPolynomialSaturation
import GaloisForLFunctions.HTGeometry.PrimeProfileJetPacket

/-!
# The arbitrary prime-profile jet is the prime-clock orbit

This leaf identifies the logarithmic jet already used by the profile Jacobian with the rotated
simple-spectrum clock on prime-power coordinates.  It then transfers polynomial saturation to the
actual arithmetic-function profile: no nonzero differential clock polynomial can turn a nonlocal
prime-power source into a finite-prime source.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Polynomial

noncomputable section

/-- Read an arithmetic function on the canonical prime-power coordinate system. -/
def primePowerCoordinateProfile (f : ArithmeticFunction ℂ) :
    PrimePowerClockIndex -> ℂ :=
  fun x => f (Nat.Primes.prodNatEquiv x : Nat)

/-- Clock locality of the coordinate profile is literally finiteness of the active prime rays. -/
theorem primePowerClockLocal_coordinateProfile_iff
    (f : ArithmeticFunction ℂ) :
    PrimePowerClockLocal (primePowerCoordinateProfile f) ↔
      {p : Nat.Primes | ∃ e : Nat, f ((p : Nat) ^ (e + 1)) ≠ 0}.Finite := by
  constructor
  · intro hlocal
    apply hlocal.subset
    rintro p ⟨e, he⟩
    exact ⟨(p, e), rfl, by
      simpa [primePowerCoordinateProfile] using he⟩
  · intro hlocal
    apply hlocal.subset
    rintro p ⟨⟨q, e⟩, hqp, he⟩
    change q = p at hqp
    subst q
    exact ⟨e, by
      simpa [primePowerCoordinateProfile] using he⟩

/-- The explicit profile jet is exactly the orbit of the rotated prime-power clock. -/
theorem primePowerCoordinateProfile_primeProfileRotatedLogJet
    (k : Nat) (f : ArithmeticFunction ℂ) :
    primePowerCoordinateProfile (primeProfileRotatedLogJet k f) =
      fun x => rotatedPrimePowerClockWeight x ^ k * primePowerCoordinateProfile f x := by
  funext x
  simp [primePowerCoordinateProfile, primeProfileRotatedLogJet_apply,
    rotatedPrimePowerClockWeight, primePowerClockWeight]

/-- Apply a polynomial in the rotated logarithmic clock directly to an arithmetic profile. -/
def primeProfilePolynomialOrbit (P : ℂ[X]) (f : ArithmeticFunction ℂ) :
    ArithmeticFunction ℂ where
  toFun n := P.eval (Complex.I * (Real.log n : ℂ)) * f n
  map_zero' := by simp

@[simp]
theorem primeProfilePolynomialOrbit_apply
    (P : ℂ[X]) (f : ArithmeticFunction ℂ) (n : Nat) :
    primeProfilePolynomialOrbit P f n =
      P.eval (Complex.I * (Real.log n : ℂ)) * f n :=
  rfl

/-- The arithmetic polynomial orbit and the coordinate polynomial-clock action agree exactly. -/
theorem primePowerCoordinateProfile_primeProfilePolynomialOrbit
    (P : ℂ[X]) (f : ArithmeticFunction ℂ) :
    primePowerCoordinateProfile (primeProfilePolynomialOrbit P f) =
      rotatedPrimePowerClockPolynomialApply P (primePowerCoordinateProfile f) := by
  funext x
  simp [primePowerCoordinateProfile, primeProfilePolynomialOrbit_apply,
    rotatedPrimePowerClockPolynomialApply, polynomialClockApply,
    rotatedPrimePowerClockWeight, primePowerClockWeight]

/-- Monomials in the polynomial orbit are the existing explicit logarithmic jets. -/
theorem primeProfilePolynomialOrbit_X_pow
    (k : Nat) (f : ArithmeticFunction ℂ) :
    primeProfilePolynomialOrbit (X ^ k) f = primeProfileRotatedLogJet k f := by
  ext n
  simp [primeProfilePolynomialOrbit_apply, primeProfileRotatedLogJet_apply]

/-- **Arithmetic prime-clock saturation.**  For a nonzero clock polynomial, the transformed
arithmetic profile is supported on finitely many prime rays exactly when the original profile is.
This is the direct source-level form consumed by the differential classification. -/
theorem primeProfilePolynomialOrbit_local_iff
    (P : ℂ[X]) (hP : P ≠ 0) (f : ArithmeticFunction ℂ) :
    PrimePowerClockLocal
        (primePowerCoordinateProfile (primeProfilePolynomialOrbit P f)) ↔
      PrimePowerClockLocal (primePowerCoordinateProfile f) := by
  rw [primePowerCoordinateProfile_primeProfilePolynomialOrbit]
  exact rotatedPrimePowerClockPolynomialApply_local_iff P hP
    (primePowerCoordinateProfile f)

/-- Quotient-zero form for actual arithmetic profiles. -/
theorem primeProfilePolynomialOrbit_quotient_eq_zero_iff
    (P : ℂ[X]) (hP : P ≠ 0) (f : ArithmeticFunction ℂ) :
    (rayLocalSubmodule primePowerClockRay).mkQ
        (primePowerCoordinateProfile (primeProfilePolynomialOrbit P f)) = 0 ↔
      (rayLocalSubmodule primePowerClockRay).mkQ
        (primePowerCoordinateProfile f) = 0 := by
  rw [primePowerCoordinateProfile_primeProfilePolynomialOrbit]
  exact rotatedPrimePowerClockQuotient_polynomialClock_eq_zero_iff P hP
    (primePowerCoordinateProfile f)

end

end GaloisForLFunctions.HTGeometry
