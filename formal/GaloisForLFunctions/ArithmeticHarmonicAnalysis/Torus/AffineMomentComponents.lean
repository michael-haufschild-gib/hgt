import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedMinimalPrimes
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.AffineMomentDomain

/-!
# Exact component counts for affine paired moment equations

Every affine moment ideal has a polynomial neutral quotient. Its paired
minimal primes therefore correspond to binary choices at the coordinate
unit vectors lying in the zero-level relation space. This identifies the
actual minimal-prime set and counts the irreducible components of its
Zariski zero locus over the original field.

For arbitrary, possibly infinite equation families, inconsistency gives
no components. Otherwise each forced-zero coordinate doubles the count.
Such a coordinate is detected by a finite linear combination of equations
with its unit coefficient row and zero constant.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- Unit coordinate relations whose prescribed level is zero. -/
abbrev AffineMomentZeroCoordinate (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :=
  {i : ι // ∃ h : Pi.basisFun K ι i ∈ L, ℓ ⟨Pi.basisFun K ι i, h⟩ = 0}

/-- Exact affine ideal membership identifies the coordinates that split into branches. -/
def affineMomentZeroCoordinateEquiv (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    PairedZeroCoordinate K (affineMomentIdeal K L ℓ) ≃ AffineMomentZeroCoordinate K L ℓ :=
  Equiv.subtypeEquivRight (affineMomentIdeal_X_mem_iff K L ℓ)

/-- The binary branch ideals exhaust the affine paired minimal primes. -/
theorem affinePairedMinimalPrimes_eq_range (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    ((affineMomentIdeal K L ℓ).map (invariantSubstitution K)).minimalPrimes =
      Set.range (pairedMinimalBranchIdeal K (affineMomentIdeal K L ℓ)) := by
  letI : (affineMomentIdeal K L ℓ).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (affineMomentQuotient_isDomain K L ℓ)
  exact pairedMinimalPrimes_eq_range K _

/-- Each zero-level coordinate relation doubles the number of minimal primes. -/
theorem card_affinePairedMinimalPrimes (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    Nat.card ((affineMomentIdeal K L ℓ).map (invariantSubstitution K)).minimalPrimes =
      2 ^ Fintype.card (AffineMomentZeroCoordinate K L ℓ) := by
  letI : (affineMomentIdeal K L ℓ).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (affineMomentQuotient_isDomain K L ℓ)
  rw [card_pairedMinimalPrimes, Fintype.card_congr (affineMomentZeroCoordinateEquiv K L ℓ)]

/-- Exact irreducible-component count for every relation space and affine level. -/
theorem card_affinePairedIrreducibleComponents (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    Nat.card (irreducibleComponents (PrimeSpectrum.zeroLocus
      (((affineMomentIdeal K L ℓ).map (invariantSubstitution K)) :
        Set (MvPolynomial (ι ⊕ ι) K)))) =
      2 ^ Fintype.card (AffineMomentZeroCoordinate K L ℓ) := by
  rw [card_pairedIrreducibleComponents_eq_minimalPrimes, card_affinePairedMinimalPrimes]

namespace AffineMomentSystem
variable {α : Type*}

/-- A finite combination of equations forcing one neutral coordinate to vanish. -/
abbrev ForcedZeroCoordinate (a : α → ι → K) (b : α → K) :=
  {i : ι // ∃ v : α →₀ K,
    rowMap K a v = Pi.basisFun K ι i ∧ valueMap K b v = 0}

/-- In a compatible system, zero-coordinate certificates detect exactly ideal membership. -/
def forcedZeroCoordinateEquiv (a : α → ι → K) (b : α → K) (h : Compatible K a b) :
    PairedZeroCoordinate K (ideal K a b) ≃ ForcedZeroCoordinate K a b :=
  Equiv.subtypeEquivRight (fun i => by
    simpa only [h, not_true_eq_false, false_or] using ideal_X_mem_iff K a b i)

/-- Unconditional classification, including the empty minimal-prime set of an inconsistent system. -/
theorem pairedMinimalPrimes_eq_range (a : α → ι → K) (b : α → K) :
    ((ideal K a b).map (invariantSubstitution K)).minimalPrimes =
      if Compatible K a b then Set.range (pairedMinimalBranchIdeal K (ideal K a b)) else ∅ := by
  by_cases h : Compatible K a b
  · rw [if_pos h]
    letI : (ideal K a b).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp ((neutralQuotient_isDomain_iff K a b).mpr h)
    exact GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedMinimalPrimes_eq_range K _
  · rw [if_neg h, ideal_eq_top_of_not_compatible K a b h, Ideal.map_top,
      Ideal.minimalPrimes_top]

/-- Compatibility and finite coordinate-zero certificates determine the exact minimal-prime count. -/
theorem card_pairedMinimalPrimes (a : α → ι → K) (b : α → K) :
    Nat.card ((ideal K a b).map (invariantSubstitution K)).minimalPrimes =
      if Compatible K a b then 2 ^ Fintype.card (ForcedZeroCoordinate K a b) else 0 := by
  by_cases h : Compatible K a b
  · rw [if_pos h]
    letI : (ideal K a b).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp ((neutralQuotient_isDomain_iff K a b).mpr h)
    rw [GaloisForLFunctions.ArithmeticHarmonicAnalysis.card_pairedMinimalPrimes,
      Fintype.card_congr (forcedZeroCoordinateEquiv K a b h)]
  · rw [if_neg h, ideal_eq_top_of_not_compatible K a b h, Ideal.map_top,
      Ideal.minimalPrimes_top]
    simp

/-- The affine paired zero locus has zero components if inconsistent and otherwise `2^s`. -/
theorem card_pairedIrreducibleComponents (a : α → ι → K) (b : α → K) :
    Nat.card (irreducibleComponents (PrimeSpectrum.zeroLocus
      (((ideal K a b).map (invariantSubstitution K)) : Set (MvPolynomial (ι ⊕ ι) K)))) =
      if Compatible K a b then 2 ^ Fintype.card (ForcedZeroCoordinate K a b) else 0 := by
  rw [card_pairedIrreducibleComponents_eq_minimalPrimes, card_pairedMinimalPrimes]

end AffineMomentSystem
end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.affinePairedMinimalPrimes_eq_range
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.card_affinePairedIrreducibleComponents
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem.pairedMinimalPrimes_eq_range
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem.card_pairedIrreducibleComponents
