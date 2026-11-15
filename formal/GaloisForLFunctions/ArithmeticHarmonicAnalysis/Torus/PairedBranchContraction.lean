import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedMinimalPrimes

/-!
# Every oriented paired branch contracts to its neutral ideal

The neutral-coordinate contraction of a branch is exactly the original ideal,
without primality or reducedness assumptions. A branch lies in the kernel of
its oriented Laurent chart, whose restriction to neutral polynomials is the
quotient map followed by inclusion as constant Laurent polynomials. Taking the
zero Laurent coefficient recovers membership in the neutral ideal.

Consequently branches over distinct neutral ideals cannot coincide.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
open scoped PairedNeutral
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- Adding oriented zero-coordinate branch equations creates no new neutral relations. -/
theorem pairedBranchIdeal_comap (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool) :
    (pairedBranchIdeal K J ε).comap (invariantSubstitution K) = J := by
  apply le_antisymm
  · intro f hf
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hz := RingHom.mem_ker.mp (pairedBranchIdeal_le_ker K J ε hf)
    rw [pairedChartMap_invariant] at hz
    have hc := congrArg (fun p : NeutralLaurent K J => p.coeff 0) hz
    simpa using hc
  · intro f hf
    exact extended_le_pairedBranchIdeal K J ε
      (Ideal.mem_map_of_mem (invariantSubstitution K) hf)

/-- The branch indexed by vanishing coordinates contracts to its original neutral ideal. -/
theorem pairedMinimalBranchIdeal_comap (J : Ideal (MvPolynomial ι K))
    (ε : PairedZeroCoordinate K J → Bool) :
    (pairedMinimalBranchIdeal K J ε).comap (invariantSubstitution K) = J :=
  pairedBranchIdeal_comap K J (extendPairedBranch K J ε)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedBranchIdeal_comap
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedMinimalBranchIdeal_comap

