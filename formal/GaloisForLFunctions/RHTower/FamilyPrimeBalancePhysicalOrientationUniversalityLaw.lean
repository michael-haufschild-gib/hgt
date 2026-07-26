import GaloisForLFunctions.HTGeometry.PhysicalDefectOrientationAnomaly
import GaloisForLFunctions.RHTower.FamilyPrimeBalanceDiagonalScaleUniversalityLaw

/-!
# Family prime-balance physical-orientation universality

Coordinatewise prime balance makes every prime-coordinate physical defect source balanced.
Consequently full reversal retains only family-cardinality parity, and even families are completely
reversal-invariant, alongside the existing diagonal and shared-scale cancellations.
-/

namespace GaloisForLFunctions

open scoped BigOperators

noncomputable section

/-- Arithmetic, diagonal, scale, and physical-orientation consequences of finite family balance. -/
structure FamilyPrimeBalancePhysicalOrientationCertificate
    {ι G : Type*} [Fintype ι] [CommGroup G]
    (m : ι → Nat.Primes →₀ ℤ) (twist : ι → Nat.Primes → G) : Prop where
  balanceZero :
    familyPrimeBalance m = 0
  coordinateBalance :
    ∀ p : Nat.Primes, ∑ i, m i p = 0
  diagonalBalance :
    ∀ z : ℂ,
      diagonalPrimeMonomial (positivePart (familyPrimeBalance m)) z =
        diagonalPrimeMonomial (negativePart (familyPrimeBalance m)) z
  sharedScaleCancellation :
    ∀ scale : Nat.Primes → G,
      familyTwistedProduct twist scale m =
        ∏ i, bohrCharacter (m i) (twist i)
  coordinatePhysicalReversalParity :
    ∀ p : Nat.Primes, ∀ z : ℂ,
      physicalDefectProduct (Finset.univ : Finset ι)
          (-(fun i => ((m i p : ℤ) : ℂ))) z =
        (-1 : ℂ) ^ Fintype.card ι *
          physicalDefectProduct (Finset.univ : Finset ι)
            (fun i => ((m i p : ℤ) : ℂ)) z
  evenCoordinatePhysicalReversalInvisible :
    Even (Fintype.card ι) →
      ∀ p : Nat.Primes, ∀ z : ℂ,
        physicalDefectProduct (Finset.univ : Finset ι)
            (-(fun i => ((m i p : ℤ) : ℂ))) z =
          physicalDefectProduct (Finset.univ : Finset ι)
            (fun i => ((m i p : ℤ) : ℂ)) z

/-- Every balanced prime coordinate is a balanced physical source. -/
private theorem familyPrimeBalance_coordinatePhysicalSource_sum_eq_zero
    {ι : Type*} [Fintype ι]
    (m : ι → Nat.Primes →₀ ℤ)
    (hcoordinate : ∀ p : Nat.Primes, ∑ i, m i p = 0)
    (p : Nat.Primes) :
    ∑ i ∈ (Finset.univ : Finset ι), ((m i p : ℤ) : ℂ) = 0 := by
  exact_mod_cast hcoordinate p

/-- **Family prime-balance physical-orientation universality law.** -/
theorem familyPrimeBalance_physicalOrientationUniversality
    {ι G : Type*} [Fintype ι] [CommGroup G]
    (m : ι → Nat.Primes →₀ ℤ) (twist : ι → Nat.Primes → G) :
    primeProduct (positivePart (familyPrimeBalance m)) =
        primeProduct (negativePart (familyPrimeBalance m)) ↔
      FamilyPrimeBalancePhysicalOrientationCertificate m twist := by
  constructor
  · intro hprime
    have hfamily :=
      (familyPrimeBalance_diagonalScaleUniversality m twist).mp hprime
    have hparity : ∀ p : Nat.Primes, ∀ z : ℂ,
        physicalDefectProduct (Finset.univ : Finset ι)
            (-(fun i => ((m i p : ℤ) : ℂ))) z =
          (-1 : ℂ) ^ Fintype.card ι *
            physicalDefectProduct (Finset.univ : Finset ι)
              (fun i => ((m i p : ℤ) : ℂ)) z := by
      intro p z
      have hbalanced :=
        familyPrimeBalance_coordinatePhysicalSource_sum_eq_zero
          m hfamily.2.1 p
      simpa only [Finset.card_univ] using
        physicalDefectProduct_neg_eq_parity_of_balanced
          (Finset.univ : Finset ι)
          (fun i => ((m i p : ℤ) : ℂ)) z hbalanced
    have heven : Even (Fintype.card ι) →
        ∀ p : Nat.Primes, ∀ z : ℂ,
          physicalDefectProduct (Finset.univ : Finset ι)
              (-(fun i => ((m i p : ℤ) : ℂ))) z =
            physicalDefectProduct (Finset.univ : Finset ι)
              (fun i => ((m i p : ℤ) : ℂ)) z := by
      intro hcard p z
      have hbalanced :=
        familyPrimeBalance_coordinatePhysicalSource_sum_eq_zero
          m hfamily.2.1 p
      have hcard' : Even (Finset.univ : Finset ι).card := by
        simpa only [Finset.card_univ] using hcard
      exact physicalDefectProduct_neg_eq_of_even_balanced
        (Finset.univ : Finset ι)
        (fun i => ((m i p : ℤ) : ℂ)) z hcard' hbalanced
    exact
      ⟨hfamily.1, hfamily.2.1, hfamily.2.2.1, hfamily.2.2.2,
        hparity, heven⟩
  · intro h
    exact
      (familyPrimeBalance_diagonalScaleUniversality m twist).mpr
        ⟨h.balanceZero, h.coordinateBalance, h.diagonalBalance,
          h.sharedScaleCancellation⟩

end

end GaloisForLFunctions
