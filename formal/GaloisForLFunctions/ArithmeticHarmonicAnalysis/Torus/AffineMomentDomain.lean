import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.AffineMomentIdealMembership
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedNeutralLaurent

/-!
# Domain classification for affine paired moment systems

A neutral affine moment quotient is always a polynomial domain. Its paired
quotient is a domain exactly when no coordinate unit vector belongs to the
zero-level relation space. For an arbitrary family of affine equations, the
criterion is compatibility together with the absence of a finite linear
combination forcing any single neutral coordinate to zero.

This combines the Laurent embedding for arbitrary neutral ideals with the
exact affine linear membership criterion. Every statement is over the
original field and includes dependent or infinitely many equations. No
assumption of an algebraically closed or infinite field is needed.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- Polynomial coordinates make every neutral moment-level quotient a domain. -/
theorem affineMomentQuotient_isDomain (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    IsDomain (MvPolynomial ι K ⧸ affineMomentIdeal K L ℓ) :=
  Function.Injective.isDomain (affineMomentPolynomialEquiv K L ℓ)
    (affineMomentPolynomialEquiv K L ℓ).injective

/-- A paired affine level is a domain precisely when every coordinate relation has nonzero level. -/
theorem affinePairedQuotient_isDomain_iff (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    IsDomain (MvPolynomial (ι ⊕ ι) K ⧸
      (affineMomentIdeal K L ℓ).map (invariantSubstitution K)) ↔
      ∀ i, ∀ h : Pi.basisFun K ι i ∈ L, ℓ ⟨Pi.basisFun K ι i, h⟩ ≠ 0 := by
  rw [pairedNeutralQuotient_isDomain_iff]
  constructor
  · rintro ⟨_, h⟩ i hi hz
    exact h i ((affineMomentIdeal_X_mem_iff K L ℓ i).mpr ⟨hi, hz⟩)
  · intro h
    refine ⟨affineMomentQuotient_isDomain K L ℓ, ?_⟩
    intro i hi
    obtain ⟨hm, hz⟩ := (affineMomentIdeal_X_mem_iff K L ℓ i).mp hi
    exact h i hm hz

namespace AffineMomentSystem
variable {α : Type*}

/-- For arbitrary affine equations, consistency is exactly the neutral domain condition. -/
theorem neutralQuotient_isDomain_iff (a : α → ι → K) (b : α → K) :
    IsDomain (MvPolynomial ι K ⧸ ideal K a b) ↔ Compatible K a b := by
  constructor
  · intro h
    exact (ideal_ne_top_iff K a b).mp ((Ideal.Quotient.isDomain_iff_prime _).mp h).ne_top
  · intro h
    exact Function.Injective.isDomain (quotientPolynomialEquiv K a b h)
      (quotientPolynomialEquiv K a b h).injective

/-- The full paired domain criterion is compatibility and absence of coordinate-zero certificates. -/
theorem pairedQuotient_isDomain_iff (a : α → ι → K) (b : α → K) :
    IsDomain (MvPolynomial (ι ⊕ ι) K ⧸ (ideal K a b).map (invariantSubstitution K)) ↔
      Compatible K a b ∧ ∀ i, ¬ ∃ v : α →₀ K,
        rowMap K a v = Pi.basisFun K ι i ∧ valueMap K b v = 0 := by
  rw [pairedNeutralQuotient_isDomain_iff, neutralQuotient_isDomain_iff]
  constructor
  · rintro ⟨hc, hn⟩
    exact ⟨hc, fun i he => hn i ((ideal_X_mem_iff K a b i).mpr (Or.inr he))⟩
  · rintro ⟨hc, hn⟩
    refine ⟨hc, ?_⟩
    intro i hi
    rcases (ideal_X_mem_iff K a b i).mp hi with hb | he
    · exact hb hc
    · exact hn i he

/-- Primality of the paired moment ideal is characterized entirely by finite linear relations. -/
theorem pairedIdeal_isPrime_iff (a : α → ι → K) (b : α → K) :
    ((ideal K a b).map (invariantSubstitution K)).IsPrime ↔
      Compatible K a b ∧ ∀ i, ¬ ∃ v : α →₀ K,
        rowMap K a v = Pi.basisFun K ι i ∧ valueMap K b v = 0 := by
  rw [← Ideal.Quotient.isDomain_iff_prime, pairedQuotient_isDomain_iff]

end AffineMomentSystem
end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.affinePairedQuotient_isDomain_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem.pairedQuotient_isDomain_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem.pairedIdeal_isPrime_iff
