import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalizedPrimeFibers
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerDistinguishedMembership
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalPrimeCoordinate

/-!
# Exact finite rational-prime classification

The constructed nonzero fibers and auxiliary-field fibers are disjoint.
Their union contains exactly the normalization primes whose residue field
is the constant field: every such prime supplies a soluble coordinate,
and the finite-field reconstruction classifies that coordinate.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)

/-- Constructed nonzero fibers and auxiliary-field fibers have no normalization prime in common. -/
theorem kummerConstructedPrimes_disjoint_distinguished :
    Disjoint (kummerConstructedPrimes p (kummerSquareIndex d n) d r)
      (squareKummerFiniteBranchPrimes p d n (kummerExponent (p ^ (d + 1)) (r + 1))
        (kummerTraceConstant p (kummerSquareIndex d n))) := by
  classical
  apply Finset.disjoint_left.mpr
  intro P hP hP'
  obtain ⟨_, i, hi⟩ := (mem_kummerConstructedPrimes_iff p (kummerSquareIndex d n) d r P).mp hP
  obtain ⟨_, a, ha⟩ := (mem_squareKummerFiniteBranchPrimes_iff p d n
    (kummerExponent (p ^ (d + 1)) (r + 1)) (kummerTraceConstant p (kummerSquareIndex d n)) P).mp hP'
  letI := hi
  letI := ha
  have heq := linearPlace_liesOver_unique P (kummerConstructedOrdinate p (kummerSquareIndex d n) d r i)
    (a : SquareConstantField p (kummerSquareIndex d n))
  apply kummerConstructedOrdinate_branch_ne_zero p (kummerSquareIndex d n) d r i
  rw [heq]
  exact (normalizedKummerBranch_eq_zero_iff p (kummerSquareIndex d n) d r a).mpr a.property

/-- All finite rational primes of the normalized prime-power Kummer field. -/
def normalizedKummerRationalPrimes :
    Finset (Ideal (NormalizedKummerNormalization p (kummerSquareIndex d n) d r)) := by
  classical
  exact kummerConstructedPrimes p (kummerSquareIndex d n) d r ∪
    squareKummerFiniteBranchPrimes p d n (kummerExponent (p ^ (d + 1)) (r + 1))
      (kummerTraceConstant p (kummerSquareIndex d n))

/-- The explicit finite prime set contains exactly the primes with constant residue field. -/
theorem mem_normalizedKummerRationalPrimes_iff
    (P : Ideal (NormalizedKummerNormalization p (kummerSquareIndex d n) d r)) :
    P ∈ normalizedKummerRationalPrimes p d n r ↔ P.IsPrime ∧
      Function.Surjective (algebraMap (SquareConstantField p (kummerSquareIndex d n))
        (NormalizedKummerNormalization p (kummerSquareIndex d n) d r ⧸ P)) := by
  classical
  rw [normalizedKummerRationalPrimes, Finset.mem_union]
  constructor
  · rintro (hP | hP)
    · exact ⟨((mem_kummerConstructedPrimes_iff p (kummerSquareIndex d n) d r P).mp hP).1,
        kummerConstructedPrimes_rational p (kummerSquareIndex d n) d r P hP⟩
    · exact ⟨((mem_squareKummerFiniteBranchPrimes_iff p d n _ _ P).mp hP).1,
        squareKummerFiniteBranchPrimes_rational p d n _ _ P hP⟩
  · rintro ⟨hp, hsurj⟩
    letI := hp
    obtain ⟨a, β, hover, hβ⟩ := squareKummer_rationalPrime_coordinate p (kummerSquareIndex d n)
      _ _ _ P hsurj
    letI := hover
    rcases (normalizedKummer_soluble_ordinate_iff p (kummerSquareIndex d n) d r a).mp ⟨β, hβ⟩ with ha | hi
    · right
      exact (mem_squareKummerFiniteBranchPrimes_iff p d n _ _ P).mpr ⟨hp, ⟨a, ha⟩, hover⟩
    · left
      obtain ⟨i, rfl⟩ := hi
      exact (mem_kummerConstructedPrimes_iff p (kummerSquareIndex d n) d r P).mpr ⟨hp, i, hover⟩

/-- The finite rational prime count is the full nonzero-fiber contribution plus the resolved branch contribution. -/
theorem normalizedKummerRationalPrimes_card :
    (normalizedKummerRationalPrimes p d n r).card =
      Nat.card (KummerOrdinateParameters p (kummerSquareIndex d n) d r) *
        (p ^ (kummerSquareIndex d n + 1) + 1) +
      (p ^ (d + 1) - 1) * Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1)
        (kummerExponent (p ^ (d + 1)) (r + 1)) + 1 := by
  classical
  rw [normalizedKummerRationalPrimes,
    Finset.card_union_of_disjoint (kummerConstructedPrimes_disjoint_distinguished p d n r),
    kummerConstructedPrimes_card, squareKummerFiniteBranchPrimes_card]
  omega

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
