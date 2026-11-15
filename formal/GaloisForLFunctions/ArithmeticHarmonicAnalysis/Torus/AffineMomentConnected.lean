import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedNeutralConnected
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.AffineMomentDomain

/-!
# Connectedness of every compatible affine paired moment locus

Affine neutral moment quotients are polynomial domains. The common prime
specialization of their paired branches therefore proves that all branches
meet simultaneously and that the full paired zero locus is connected.

For arbitrary equation families, including infinite families, connectedness
is equivalent to compatibility. Incompatible systems have empty zero locus.
Thus every affine paired moment locus is preconnected, although a compatible
one can have many irreducible components.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- Every relation space and affine level gives a connected paired zero locus. -/
theorem affinePairedZeroLocus_isConnected (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    IsConnected (PrimeSpectrum.zeroLocus
      (((affineMomentIdeal K L ℓ).map (invariantSubstitution K)) :
        Set (MvPolynomial (ι ⊕ ι) K))) := by
  letI : (affineMomentIdeal K L ℓ).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (affineMomentQuotient_isDomain K L ℓ)
  exact pairedZeroLocus_isConnected K _

/-- All irreducible branches at an affine moment level have a common prime point. -/
theorem affinePairedBranches_inter_nonempty (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    (⋂ ε : ι → Bool, PrimeSpectrum.zeroLocus
      ((pairedBranchIdeal K (affineMomentIdeal K L ℓ) ε) : Set (MvPolynomial (ι ⊕ ι) K))).Nonempty := by
  letI : (affineMomentIdeal K L ℓ).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (affineMomentQuotient_isDomain K L ℓ)
  exact pairedBranches_inter_nonempty K _

namespace AffineMomentSystem
variable {α : Type*}

/-- The paired zero locus is empty exactly when the affine equations are incompatible. -/
theorem pairedZeroLocus_eq_empty_iff (a : α → ι → K) (b : α → K) :
    PrimeSpectrum.zeroLocus
      (((ideal K a b).map (invariantSubstitution K)) : Set (MvPolynomial (ι ⊕ ι) K)) = ∅ ↔
      ¬ Compatible K a b := by
  constructor
  · intro he hc
    letI : (ideal K a b).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp ((neutralQuotient_isDomain_iff K a b).mpr hc)
    have hn := (GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedZeroLocus_isConnected
      K (ideal K a b)).1
    rw [he] at hn
    exact Set.not_nonempty_empty hn
  · intro hc
    apply PrimeSpectrum.zeroLocus_empty_of_one_mem
    rw [ideal_eq_top_of_not_compatible K a b hc, Ideal.map_top]
    trivial

/-- Compatibility is the complete connectedness criterion for arbitrary affine equation families. -/
theorem pairedZeroLocus_isConnected_iff (a : α → ι → K) (b : α → K) :
    IsConnected (PrimeSpectrum.zeroLocus
      (((ideal K a b).map (invariantSubstitution K)) : Set (MvPolynomial (ι ⊕ ι) K))) ↔
      Compatible K a b := by
  constructor
  · intro h
    by_contra hc
    have he := (pairedZeroLocus_eq_empty_iff K a b).mpr hc
    exact Set.not_nonempty_empty (he ▸ h.1)
  · intro hc
    letI : (ideal K a b).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp ((neutralQuotient_isDomain_iff K a b).mpr hc)
    exact GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedZeroLocus_isConnected K _

/-- Every affine paired zero locus is preconnected, including the empty inconsistent case. -/
theorem pairedZeroLocus_isPreconnected (a : α → ι → K) (b : α → K) :
    IsPreconnected (PrimeSpectrum.zeroLocus
      (((ideal K a b).map (invariantSubstitution K)) : Set (MvPolynomial (ι ⊕ ι) K))) := by
  by_cases hc : Compatible K a b
  · exact ((pairedZeroLocus_isConnected_iff K a b).mpr hc).2
  · rw [(pairedZeroLocus_eq_empty_iff K a b).mpr hc]
    exact isPreconnected_empty

/-- The branches meet simultaneously exactly when the affine equations are compatible. -/
theorem pairedBranches_inter_nonempty_iff (a : α → ι → K) (b : α → K) :
    (⋂ ε : ι → Bool, PrimeSpectrum.zeroLocus
      ((pairedBranchIdeal K (ideal K a b) ε) : Set (MvPolynomial (ι ⊕ ι) K))).Nonempty ↔
      Compatible K a b := by
  constructor
  · rintro ⟨Q, hQ⟩
    have hb := Set.mem_iInter.mp hQ (fun _ => true)
    have he : Q ∈ PrimeSpectrum.zeroLocus
        (((ideal K a b).map (invariantSubstitution K)) : Set (MvPolynomial (ι ⊕ ι) K)) :=
      (extended_le_pairedBranchIdeal K (ideal K a b) (fun _ => true)).trans hb
    by_contra hc
    rw [(pairedZeroLocus_eq_empty_iff K a b).mpr hc] at he
    exact he
  · intro hc
    letI : (ideal K a b).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp ((neutralQuotient_isDomain_iff K a b).mpr hc)
    exact GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedBranches_inter_nonempty K _

end AffineMomentSystem
end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.affinePairedZeroLocus_isConnected
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.affinePairedBranches_inter_nonempty
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem.pairedZeroLocus_isConnected_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem.pairedBranches_inter_nonempty_iff
