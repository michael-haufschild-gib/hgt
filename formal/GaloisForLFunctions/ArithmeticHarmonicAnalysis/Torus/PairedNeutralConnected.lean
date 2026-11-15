import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedMinimalPrimes

/-!
# The prime branches of a paired neutral extension meet

Specialize both paired variables to zero at every vanishing neutral
coordinate; elsewhere specialize them to `1` and the neutral coordinate.
This preserves all neutral equations and kills the generators of every
branch simultaneously. Over a prime neutral ideal, its kernel is a prime
belonging to all branch zero loci.

Every prime over the extended ideal contains a branch, so those zero loci
cover the original locus. Each branch is irreducible. Their common point
therefore makes the entire paired zero locus connected, even when its
irreducible-component count exceeds one.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
variable {ι : Type*} (K : Type*) [Field K]

/-- A simultaneous specialization of every branch into the neutral quotient. -/
def pairedBranchSpecialization (J : Ideal (MvPolynomial ι K)) :
    MvPolynomial (ι ⊕ ι) K →+* (MvPolynomial ι K ⧸ J) :=
  eval₂Hom ((Ideal.Quotient.mk J).comp C)
    (Sum.elim (fun i => if (X i : MvPolynomial ι K) ∈ J then 0 else 1)
      (fun i => Ideal.Quotient.mk J (X i)))

/-- The specialization restricts to the identity on neutral quotient coordinates. -/
theorem pairedBranchSpecialization_invariant (J : Ideal (MvPolynomial ι K))
    (f : MvPolynomial ι K) :
    pairedBranchSpecialization K J (invariantSubstitution K f) = Ideal.Quotient.mk J f := by
  have he : (pairedBranchSpecialization K J).comp (invariantSubstitution K) =
      Ideal.Quotient.mk J := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [pairedBranchSpecialization, invariantSubstitution]
    · intro i
      by_cases hi : (X i : MvPolynomial ι K) ∈ J
      · have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hi
        simp [pairedBranchSpecialization, invariantSubstitution, hi, hz]
      · simp [pairedBranchSpecialization, invariantSubstitution, hi]
  exact DFunLike.congr_fun he f

/-- All extended neutral equations vanish under simultaneous branch specialization. -/
theorem extended_le_ker_pairedBranchSpecialization (J : Ideal (MvPolynomial ι K)) :
    J.map (invariantSubstitution K) ≤ RingHom.ker (pairedBranchSpecialization K J) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro f hf
  change pairedBranchSpecialization K J (invariantSubstitution K f) = 0
  rw [pairedBranchSpecialization_invariant]
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr hf

/-- Every branch ideal lies in the same specialization kernel. -/
theorem pairedBranchIdeal_le_ker_specialization (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool) :
    pairedBranchIdeal K J ε ≤ RingHom.ker (pairedBranchSpecialization K J) := by
  apply sup_le (extended_le_ker_pairedBranchSpecialization K J)
  rw [Ideal.span_le]
  rintro _ ⟨⟨i, hi⟩, rfl⟩
  apply RingHom.mem_ker.mpr
  have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hi
  cases h : ε i <;> simp [pairedBranchSpecialization, pairedBranchVariable, h, hi, hz]

/-- A common prime specialization of all branches over a prime neutral ideal. -/
def pairedBranchCommonPrime (J : Ideal (MvPolynomial ι K)) [J.IsPrime] :
    PrimeSpectrum (MvPolynomial (ι ⊕ ι) K) :=
  ⟨RingHom.ker (pairedBranchSpecialization K J), RingHom.ker_isPrime _⟩

/-- The common prime belongs to each branch zero locus. -/
theorem pairedBranchCommonPrime_mem (J : Ideal (MvPolynomial ι K)) [J.IsPrime] (ε : ι → Bool) :
    pairedBranchCommonPrime K J ∈
      PrimeSpectrum.zeroLocus ((pairedBranchIdeal K J ε) : Set (MvPolynomial (ι ⊕ ι) K)) :=
  pairedBranchIdeal_le_ker_specialization K J ε

/-- Branch zero loci cover the paired zero locus for every neutral ideal. -/
theorem pairedZeroLocus_eq_iUnion_branches (J : Ideal (MvPolynomial ι K)) :
    PrimeSpectrum.zeroLocus ((J.map (invariantSubstitution K)) : Set (MvPolynomial (ι ⊕ ι) K)) =
      ⋃ ε : ι → Bool, PrimeSpectrum.zeroLocus
        ((pairedBranchIdeal K J ε) : Set (MvPolynomial (ι ⊕ ι) K)) := by
  ext Q
  simp only [Set.mem_iUnion]
  change J.map (invariantSubstitution K) ≤ Q.asIdeal ↔
    ∃ ε, pairedBranchIdeal K J ε ≤ Q.asIdeal
  constructor
  · intro h
    exact exists_pairedBranchIdeal_le K J Q.asIdeal h
  · rintro ⟨ε, h⟩
    exact (extended_le_pairedBranchIdeal K J ε).trans h

/-- All branches meet simultaneously, not merely pairwise. -/
theorem pairedBranches_inter_nonempty (J : Ideal (MvPolynomial ι K)) [J.IsPrime] :
    (⋂ ε : ι → Bool, PrimeSpectrum.zeroLocus
      ((pairedBranchIdeal K J ε) : Set (MvPolynomial (ι ⊕ ι) K))).Nonempty :=
  ⟨pairedBranchCommonPrime K J, Set.mem_iInter.mpr (pairedBranchCommonPrime_mem K J)⟩

variable [Fintype ι]

/-- The paired zero locus over a prime neutral ideal is connected. -/
theorem pairedZeroLocus_isConnected (J : Ideal (MvPolynomial ι K)) [J.IsPrime] :
    IsConnected (PrimeSpectrum.zeroLocus
      ((J.map (invariantSubstitution K)) : Set (MvPolynomial (ι ⊕ ι) K))) := by
  refine ⟨⟨pairedBranchCommonPrime K J, extended_le_ker_pairedBranchSpecialization K J⟩, ?_⟩
  rw [pairedZeroLocus_eq_iUnion_branches]
  apply isPreconnected_iUnion (pairedBranches_inter_nonempty K J)
  intro ε
  have hp := pairedBranchIdeal_isPrime K J ε
  exact ((PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical _ hp.isRadical).mpr hp).isConnected.2

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedBranchIdeal_le_ker_specialization
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedBranches_inter_nonempty
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedZeroLocus_isConnected
