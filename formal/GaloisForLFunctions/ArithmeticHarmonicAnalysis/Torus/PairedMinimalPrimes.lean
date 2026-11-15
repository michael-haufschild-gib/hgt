import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedNeutralBranches
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Minimal primes of paired neutral extensions

For a prime neutral ideal `J`, the extension under `hᵢ ↦ zᵢwᵢ` has one
minimal prime for each choice of `zᵢ` or `wᵢ` at every coordinate with
`hᵢ ∈ J`. Laurent kernels prove primality; primality of an arbitrary
overideal forces one such choice and proves that the list is exhaustive.

Thus both the native minimal-prime set and the irreducible components of
its Zariski zero locus have cardinality `2^s`, where `s` counts those
vanishing neutral coordinates. These are components over the original
field; algebraic closure is unnecessary.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- Coordinates whose neutral class vanishes. -/
abbrev PairedZeroCoordinate (J : Ideal (MvPolynomial ι K)) :=
  {i : ι // (X i : MvPolynomial ι K) ∈ J}

/-- Extend the choices on vanishing coordinates by an arbitrary fixed choice elsewhere. -/
def extendPairedBranch (J : Ideal (MvPolynomial ι K))
    (ε : PairedZeroCoordinate K J → Bool) : ι → Bool :=
  fun i => if hi : (X i : MvPolynomial ι K) ∈ J then ε ⟨i, hi⟩ else true

omit [Fintype ι] in
@[simp] theorem extendPairedBranch_apply_zero (J : Ideal (MvPolynomial ι K))
    (ε : PairedZeroCoordinate K J → Bool) (i : PairedZeroCoordinate K J) :
    extendPairedBranch K J ε i.1 = ε i := by
  simp [extendPairedBranch, i.2]

/-- A branch indexed only by the coordinates on which its choice matters. -/
def pairedMinimalBranchIdeal (J : Ideal (MvPolynomial ι K))
    (ε : PairedZeroCoordinate K J → Bool) : Ideal (MvPolynomial (ι ⊕ ι) K) :=
  pairedBranchIdeal K J (extendPairedBranch K J ε)

omit [Fintype ι] in
theorem pairedBranchIdeal_eq_minimalBranch (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool) :
    pairedBranchIdeal K J ε = pairedMinimalBranchIdeal K J (fun i => ε i.1) := by
  apply pairedBranchIdeal_congr
  intro i hi
  simp [extendPairedBranch, hi]

/-- Different choices on vanishing coordinates give different prime ideals. -/
theorem pairedMinimalBranchIdeal_injective (J : Ideal (MvPolynomial ι K)) [J.IsPrime] :
    Function.Injective (pairedMinimalBranchIdeal K J) := by
  intro ε δ h
  funext i
  have he := (pairedBranchIdeal_le_iff K J (extendPairedBranch K J ε)
    (extendPairedBranch K J δ)).mp h.le i.1 i.2
  simpa only [extendPairedBranch_apply_zero] using he

/-- Every Laurent branch is minimal among the primes containing the extended ideal. -/
theorem pairedBranchIdeal_mem_minimalPrimes (J : Ideal (MvPolynomial ι K)) [J.IsPrime]
    (ε : ι → Bool) :
    pairedBranchIdeal K J ε ∈ (J.map (invariantSubstitution K)).minimalPrimes := by
  refine ⟨⟨pairedBranchIdeal_isPrime K J ε, extended_le_pairedBranchIdeal K J ε⟩, ?_⟩
  intro Q hQ hle
  letI := hQ.1
  obtain ⟨δ, hδ⟩ := exists_pairedBranchIdeal_le K J Q hQ.2
  have he := (pairedBranchIdeal_le_iff K J δ ε).mp (hδ.trans hle)
  rw [← pairedBranchIdeal_congr K J δ ε he]
  exact hδ

/-- The Laurent branches exhaust all minimal primes of the extension. -/
theorem pairedMinimalPrimes_eq_range (J : Ideal (MvPolynomial ι K)) [J.IsPrime] :
    (J.map (invariantSubstitution K)).minimalPrimes = Set.range (pairedMinimalBranchIdeal K J) := by
  ext Q
  constructor
  · intro hQ
    letI := hQ.isPrime
    obtain ⟨ε, he⟩ := exists_pairedBranchIdeal_le K J Q hQ.le
    have hr := hQ.2 ⟨pairedBranchIdeal_isPrime K J ε, extended_le_pairedBranchIdeal K J ε⟩ he
    refine ⟨fun i => ε i.1, ?_⟩
    exact (pairedBranchIdeal_eq_minimalBranch K J ε).symm.trans (le_antisymm he hr)
  · rintro ⟨ε, rfl⟩
    exact pairedBranchIdeal_mem_minimalPrimes K J (extendPairedBranch K J ε)

/-- Minimal primes are exactly binary choices on the vanishing neutral coordinates. -/
def pairedMinimalPrimeEquiv (J : Ideal (MvPolynomial ι K)) [J.IsPrime] :
    (PairedZeroCoordinate K J → Bool) ≃ (J.map (invariantSubstitution K)).minimalPrimes :=
  Equiv.ofBijective
    (fun ε => ⟨pairedMinimalBranchIdeal K J ε,
      pairedBranchIdeal_mem_minimalPrimes K J (extendPairedBranch K J ε)⟩)
    ⟨fun ε δ h => pairedMinimalBranchIdeal_injective K J (congrArg Subtype.val h), by
      intro Q
      have hm : Q.1 ∈ Set.range (pairedMinimalBranchIdeal K J) := by
        rw [← pairedMinimalPrimes_eq_range]
        exact Q.2
      obtain ⟨ε, he⟩ := hm
      exact ⟨ε, Subtype.ext he⟩⟩

/-- Each vanishing neutral coordinate doubles the number of minimal primes. -/
theorem card_pairedMinimalPrimes (J : Ideal (MvPolynomial ι K)) [J.IsPrime] :
    Nat.card (J.map (invariantSubstitution K)).minimalPrimes =
      2 ^ Fintype.card (PairedZeroCoordinate K J) := by
  rw [← Nat.card_congr (pairedMinimalPrimeEquiv K J)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool]

omit [Fintype ι] in
/-- Native Zariski components and native minimal primes have the same cardinality. -/
theorem card_pairedIrreducibleComponents_eq_minimalPrimes (J : Ideal (MvPolynomial ι K)) :
    Nat.card (irreducibleComponents (PrimeSpectrum.zeroLocus
      ((J.map (invariantSubstitution K)) : Set (MvPolynomial (ι ⊕ ι) K)))) =
      Nat.card (J.map (invariantSubstitution K)).minimalPrimes := by
  exact (Nat.card_congr
    (Ideal.minimalPrimes.equivIrreducibleComponents (J.map (invariantSubstitution K))).toEquiv).symm

/-- The paired zero locus has exactly one irreducible component per binary branch choice. -/
theorem card_pairedIrreducibleComponents (J : Ideal (MvPolynomial ι K)) [J.IsPrime] :
    Nat.card (irreducibleComponents (PrimeSpectrum.zeroLocus
      ((J.map (invariantSubstitution K)) : Set (MvPolynomial (ι ⊕ ι) K)))) =
      2 ^ Fintype.card (PairedZeroCoordinate K J) := by
  rw [card_pairedIrreducibleComponents_eq_minimalPrimes, card_pairedMinimalPrimes]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedMinimalPrimes_eq_range
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedMinimalPrimeEquiv
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.card_pairedMinimalPrimes
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.card_pairedIrreducibleComponents
