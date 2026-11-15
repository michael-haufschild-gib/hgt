import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedNeutralCharts
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.LaurentNilpotence
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Neutral substitution preserves the exact nilradical

An element of an arbitrary paired neutral quotient is nilpotent exactly
when all its relative weight coefficients are nilpotent in the neutral
quotient. Oriented Laurent charts detect necessity, while the finite basis
expansion proves sufficiency.

Consequently the paired quotient is reduced exactly when the neutral
quotient is reduced, and radical formation commutes with extension under
`hᵢ ↦ zᵢwᵢ`. The zero-weight coordinate retracts the coefficient-ring map,
so nilpotents already present in the neutral quotient cannot disappear.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module
open scoped PairedNeutral
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- Nilpotence in the actual paired quotient is exactly nilpotence of all neutral weight coefficients. -/
theorem pairedNeutralQuotient_isNilpotent_iff (J : Ideal (MvPolynomial ι K))
    (x : MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) :
    IsNilpotent x ↔ ∀ q, IsNilpotent (pairedNeutralQuotientEquiv K J x q) := by
  classical
  constructor
  · intro hx q
    have h := laurent_isNilpotent_coeff
      (pairedQuotientChartMap K J (weightOrientation q) x)
      (hx.map (pairedQuotientChartMap K J (weightOrientation q))) q
    rwa [pairedQuotientChartMap_recovers] at h
  · intro h
    have he : x = ((pairedNeutralQuotientBasis K J).repr x).sum
        (fun q a => a • pairedNeutralQuotientBasis K J q) :=
      ((pairedNeutralQuotientBasis K J).linearCombination_repr x).symm
    rw [he]
    apply isNilpotent_sum
    intro q _
    change IsNilpotent (((pairedNeutralQuotientBasis K J).repr x q) •
      pairedNeutralQuotientBasis K J q)
    rw [Algebra.smul_def]
    exact (Commute.all _ _).isNilpotent_mul_right
      ((h q).map (algebraMap (MvPolynomial ι K ⧸ J)
        (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))))

/-- Extracting weight zero is a left inverse to the neutral quotient coefficient map. -/
theorem pairedNeutralQuotient_neutral_retract (J : Ideal (MvPolynomial ι K))
    (r : MvPolynomial ι K ⧸ J) :
    pairedNeutralQuotientEquiv K J
      (algebraMap (MvPolynomial ι K ⧸ J)
        (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) r) 0 = r := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
  change pairedNeutralQuotientEquiv K J (Ideal.Quotient.mk _ (invariantSubstitution K f)) 0 = _
  rw [pairedNeutralQuotientEquiv_mk]
  have he := pairedWeightExtraction_smul_minimal K (0 : ι → ℤ) 0 f
  rw [minimalPairedMonomial_zero, pairedNeutral_smul, mul_one] at he
  simpa only [if_pos rfl, ite_true] using congrArg (Ideal.Quotient.mk J) he

/-- Every neutral quotient embeds faithfully as the coefficient ring of its paired quotient. -/
theorem pairedNeutralQuotient_algebraMap_injective (J : Ideal (MvPolynomial ι K)) :
    Function.Injective (algebraMap (MvPolynomial ι K ⧸ J)
      (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))) := by
  intro r s h
  have he := congrArg (fun x => pairedNeutralQuotientEquiv K J x 0) h
  simpa only [pairedNeutralQuotient_neutral_retract] using he

/-- Paired neutral extension preserves and reflects reducedness. -/
theorem pairedNeutralQuotient_isReduced_iff (J : Ideal (MvPolynomial ι K)) :
    IsReduced (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) ↔
      IsReduced (MvPolynomial ι K ⧸ J) := by
  constructor
  · intro h
    letI := h
    constructor
    intro r hr
    apply pairedNeutralQuotient_algebraMap_injective K J
    rw [map_zero]
    exact (hr.map (algebraMap (MvPolynomial ι K ⧸ J)
      (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)))).eq_zero
  · intro h
    letI := h
    constructor
    intro x hx
    apply (pairedNeutralQuotientEquiv K J).injective
    ext q
    simpa only [map_zero, Finsupp.zero_apply] using
      ((pairedNeutralQuotient_isNilpotent_iff K J x).mp hx q).eq_zero

/-- Nilpotence modulo an ideal means membership in its radical. -/
private theorem quotient_nilpotent_iff {R : Type*} [CommRing R] (J : Ideal R) (f : R) :
    IsNilpotent (Ideal.Quotient.mk J f) ↔ f ∈ J.radical := by
  simp only [IsNilpotent, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_radical_iff]

/-- Taking radicals commutes with extending any neutral ideal to the paired polynomial ring. -/
theorem pairedNeutral_radical_map (J : Ideal (MvPolynomial ι K)) :
    (J.map (invariantSubstitution K)).radical = J.radical.map (invariantSubstitution K) := by
  ext P
  rw [← quotient_nilpotent_iff, pairedNeutralQuotient_isNilpotent_iff,
    mem_extended_ideal_iff_extractions]
  simp only [pairedNeutralQuotientEquiv_mk, quotient_nilpotent_iff]

/-- An extended neutral ideal is radical exactly when the original ideal is radical. -/
theorem pairedNeutralIdeal_isRadical_iff (J : Ideal (MvPolynomial ι K)) :
    (J.map (invariantSubstitution K)).IsRadical ↔ J.IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced, pairedNeutralQuotient_isReduced_iff,
    Ideal.isRadical_iff_quotient_reduced]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralQuotient_isNilpotent_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralQuotient_algebraMap_injective
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralQuotient_isReduced_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutral_radical_map
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralIdeal_isRadical_iff
