import GaloisForLFunctions.RHTower.CanonicalPadicBrauerConnesTate
import GaloisForLFunctions.RHTower.BrauerReciprocitySemilocalTrace

/-!
# Frobenius-canonical Brauer phases in semilocal trace and positivity

Every reciprocal finite `ℚ/ℤ` profile has a unique realization by local Brauer classes under the
canonical arithmetic-Frobenius invariants. Its phases are exactly the values of the corresponding
unramified Tate characters. Thus the actual finite Connes--Tate trace is a product of canonical
Brauer-twisted Euler factors, and its Hermitian square is the existing strictly positive density.

This does not identify a nontrivial twist with the untwisted Weil source. The local zero-class gate
in `CanonicalPadicBrauerConnesTate` proves that such an identification holds exactly for split
classes.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry.ABHN
open _root_.RHTower

noncomputable section

set_option maxRecDepth 4000

namespace ReciprocalFinitePrimeBrauerProfile

variable {n : ℕ} (B : ReciprocalFinitePrimeBrauerProfile n)

/-- Canonical local Brauer class realizing one coordinate of a reciprocal phase profile. -/
def canonicalBrauerClass (i : Fin n) :
    BrauerGroup ℚ_[((B.prime i : Nat.Primes) : ℕ)] :=
  canonicalPadicBrauerClassOfInvariant
    ((B.prime i : Nat.Primes) : ℕ) (B.invariant i)

/-- Every reciprocal profile phase is the Frobenius-canonical phase of its realized local
Brauer class. -/
theorem brauerPhase_eq_canonicalPadicBrauerPhase (i : Fin n) :
    B.brauerPhase i =
      canonicalPadicBrauerPhase ((B.prime i : Nat.Primes) : ℕ)
        (B.canonicalBrauerClass i) := by
  change ratModIntStdAddChar (B.invariant i) =
    canonicalPadicBrauerPhase ((B.prime i : Nat.Primes) : ℕ)
      (canonicalPadicBrauerClassOfInvariant
        ((B.prime i : Nat.Primes) : ℕ) (B.invariant i))
  exact (canonicalPadicBrauerPhase_classOfInvariant
    ((B.prime i : Nat.Primes) : ℕ) (B.invariant i)).symm

/-- ABHN reciprocity is product-one for the realized Frobenius-canonical phases. -/
theorem prod_canonicalPadicBrauerPhase_eq_one :
    ∏ i, canonicalPadicBrauerPhase ((B.prime i : Nat.Primes) : ℕ)
      (B.canonicalBrauerClass i) = 1 := by
  rw [← B.prod_brauerPhase_eq_one]
  apply Finset.prod_congr rfl
  intro i _
  exact (B.brauerPhase_eq_canonicalPadicBrauerPhase i).symm

/-- Every canonical phase in the semilocal integrand is evaluation of its unramified Tate
character on that valuation shell. -/
theorem connesPadicUnitBallProfile_criticalWeight_eq_canonicalCharacter
    (t : ℝ) (i : Fin n) (k : ℕ)
    (u : ℤ_[((B.prime i : Nat.Primes) : ℕ)]ˣ) :
    connesPadicUnitBallProfile (B.criticalWeight t i) (k : ℤ) =
      canonicalPadicBrauerUnramifiedCharacter
          ((B.prime i : Nat.Primes) : ℕ) (B.canonicalBrauerClass i)
          (fieldOnePadicValuationUnitContinuousMulEquiv
            ((B.prime i : Nat.Primes) : ℕ)
            (Multiplicative.ofAdd (k : ℤ), u)) *
        (((semilocalPrimePoissonRatio (B.prime i) : ℂ) *
          semilocalPrimePhase (B.prime i) t) ^ k) := by
  have hw : B.criticalWeight t i =
      canonicalPadicBrauerPhase ((B.prime i : Nat.Primes) : ℕ)
          (B.canonicalBrauerClass i) *
        ((semilocalPrimePoissonRatio (B.prime i) : ℂ) *
          semilocalPrimePhase (B.prime i) t) := by
    rw [criticalWeight, criticalPhase,
      B.brauerPhase_eq_canonicalPadicBrauerPhase]
    ring
  rw [hw]
  exact connesPadicUnitBallProfile_canonicalBrauer_eq_unramifiedCharacter
    ((B.prime i : Nat.Primes) : ℕ) (B.canonicalBrauerClass i)
    ((semilocalPrimePoissonRatio (B.prime i) : ℂ) *
      semilocalPrimePhase (B.prime i) t) k u

/-- Actual semilocal Connes--Tate trace is product of canonical Brauer-twisted Euler factors. -/
theorem tateTrace_eq_canonicalTwistedEulerProduct (t : ℝ) :
    B.tateTrace t =
      ∏ i, canonicalPadicBrauerTwistedLocalEulerFactor
        ((B.prime i : Nat.Primes) : ℕ) (B.canonicalBrauerClass i)
        ((semilocalPrimePoissonRatio (B.prime i) : ℂ) *
          semilocalPrimePhase (B.prime i) t) := by
  rw [B.tateTrace_eq_eulerProduct]
  apply Finset.prod_congr rfl
  intro i _
  unfold canonicalPadicBrauerTwistedLocalEulerFactor
  unfold brauerInvariantTwistedLocalEulerFactor localEulerFactor
  change (1 - B.criticalWeight t i)⁻¹ =
    (1 - canonicalPadicBrauerPhase ((B.prime i : Nat.Primes) : ℕ)
        (B.canonicalBrauerClass i) *
      ((semilocalPrimePoissonRatio (B.prime i) : ℂ) *
        semilocalPrimePhase (B.prime i) t))⁻¹
  congr 2
  rw [criticalWeight, criticalPhase,
    B.brauerPhase_eq_canonicalPadicBrauerPhase]
  ring

/-- Source-side positivity: Hermitian square of actual canonical-phase Tate trace is strictly
positive local-factor density. -/
theorem normSq_tateTrace_eq_canonicalBrauerPositiveDensity (t : ℝ) :
    Complex.normSq (B.tateTrace t) = B.tateDensity t ∧
      0 < B.tateDensity t :=
  ⟨B.normSq_tateTrace_eq_tateDensity t, B.tateDensity_pos t⟩

end ReciprocalFinitePrimeBrauerProfile

end


end GaloisForLFunctions.RHTower
