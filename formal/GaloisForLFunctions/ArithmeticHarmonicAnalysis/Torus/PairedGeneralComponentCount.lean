import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedGeneralMinimalPrimes
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Exact component counts over arbitrary neutral ideals

For each minimal prime `P` over a neutral ideal `J`, let `s(P)` count the
coordinates with `hᵢ ∈ P`. Prime contraction has exactly `2 ^ s(P)` minimal
paired primes above `P`. Thus the total number of paired minimal primes, and
equivalently native irreducible components, is the sum of these powers of two.

Finite-variable polynomial rings are Noetherian, so the indexing set of
minimal neutral primes is finite. No primality, reducedness, properness, or
algebraic-closure assumption is needed. For the unit ideal the sum is empty.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- Noetherianity supplies the finite index set used by the component sum. -/
local instance (J : Ideal (MvPolynomial ι K)) : Fintype J.minimalPrimes :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial ι K) J).fintype

/-- Each vanishing coordinate doubles the number of minimal paired primes over a neutral prime. -/
theorem card_pairedMinimalPrimeFiber (J : Ideal (MvPolynomial ι K)) (P : J.minimalPrimes) :
    Nat.card {Q : (J.map (invariantSubstitution K)).minimalPrimes //
      Q.1.comap (invariantSubstitution K) = P.1} =
      2 ^ Fintype.card (PairedZeroCoordinate K P.1) := by
  rw [← Nat.card_congr (pairedMinimalPrimeFiberEquiv K J P)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool]

/-- Count minimal paired primes by summing the binary fibers over minimal neutral primes. -/
theorem card_pairedMinimalPrimes_eq_sum (J : Ideal (MvPolynomial ι K)) :
    Nat.card (J.map (invariantSubstitution K)).minimalPrimes =
      ∑ P : J.minimalPrimes, 2 ^ Fintype.card (PairedZeroCoordinate K P.1) := by
  rw [← Nat.card_congr (pairedGeneralMinimalPrimeEquiv K J)]
  change Nat.card (Σ P : J.minimalPrimes, PairedZeroCoordinate K P.1 → Bool) = _
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro P _
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool]

/-- The same finite sum counts the native irreducible components of the paired zero locus. -/
theorem card_pairedIrreducibleComponents_eq_sum (J : Ideal (MvPolynomial ι K)) :
    Nat.card (irreducibleComponents (PrimeSpectrum.zeroLocus
      ((J.map (invariantSubstitution K)) : Set (MvPolynomial (ι ⊕ ι) K)))) =
      ∑ P : J.minimalPrimes, 2 ^ Fintype.card (PairedZeroCoordinate K P.1) := by
  rw [card_pairedIrreducibleComponents_eq_minimalPrimes, card_pairedMinimalPrimes_eq_sum]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.card_pairedMinimalPrimes_eq_sum
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.card_pairedMinimalPrimeFiber
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.card_pairedIrreducibleComponents_eq_sum
