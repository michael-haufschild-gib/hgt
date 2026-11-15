import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedNeutralBaseChange
import Mathlib.RingTheory.Ideal.Over

/-!
# Every neutral quotient retains the full relative weight basis

For an arbitrary ideal `J ≤ K[hᵢ]`, the actual quotient of `K[zᵢ,wᵢ]` by
the substituted relations is free over `K[hᵢ]/J`. Its basis is the image of
the minimal monomials, indexed by all integral weights. Its coordinates are
the original weight extractions reduced modulo `J`.

The construction uses the tensor description of the actual ideal quotient
and then descends scalar linearity to the quotient coefficient ring. Thus
the statement includes nonlinear relations, nonreduced coefficient rings,
and the unit ideal. The resulting extension is faithfully flat in every case.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module
open scoped TensorProduct PairedNeutral
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

namespace PairedNeutral
/-- The canonical quotient scalar action, presented using the explicit invariant substitution. -/
scoped instance quotientAlgebra (J : Ideal (MvPolynomial ι K)) :
    Algebra (MvPolynomial ι K ⧸ J)
      (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) := by
  change Algebra (MvPolynomial ι K ⧸ J)
    (MvPolynomial (ι ⊕ ι) K ⧸ J.map (algebraMap (MvPolynomial ι K) (MvPolynomial (ι ⊕ ι) K)))
  infer_instance
end PairedNeutral

/-- Tensor coordinates identify the actual quotient as a module over neutral polynomials. -/
def pairedNeutralQuotientLinearEquiv (J : Ideal (MvPolynomial ι K)) :
    (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) ≃ₗ[MvPolynomial ι K]
      ((ι → ℤ) →₀ (MvPolynomial ι K ⧸ J)) :=
  ((Ideal.qoutMapEquivTensorQout (MvPolynomial (ι ⊕ ι) K) (I := J)).restrictScalars
    (MvPolynomial ι K)).trans (pairedNeutralTensorEquiv K (MvPolynomial ι K ⧸ J))

theorem pairedNeutralQuotientLinearEquiv_mk (J : Ideal (MvPolynomial ι K))
    (P : MvPolynomial (ι ⊕ ι) K) (q : ι → ℤ) :
    pairedNeutralQuotientLinearEquiv K J (Ideal.Quotient.mk _ P) q =
      Ideal.Quotient.mk J (pairedWeightExtraction K q P) := by
  change pairedNeutralTensorEquiv K (MvPolynomial ι K ⧸ J)
    (P ⊗ₜ[MvPolynomial ι K] (1 : MvPolynomial ι K ⧸ J)) q = _
  rw [pairedNeutralTensorEquiv_tmul]
  change Ideal.Quotient.mk J (pairedWeightExtraction K q P * 1) = _
  rw [mul_one]

/-- The coordinate equivalence is linear over the quotient neutral ring itself. -/
def pairedNeutralQuotientEquiv (J : Ideal (MvPolynomial ι K)) :
    (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) ≃ₗ[MvPolynomial ι K ⧸ J]
      ((ι → ℤ) →₀ (MvPolynomial ι K ⧸ J)) where
  __ := (pairedNeutralQuotientLinearEquiv K J).toAddEquiv
  map_smul' := by
    intro r p
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective p
    apply Finsupp.ext
    intro q
    change pairedNeutralQuotientLinearEquiv K J
        (Ideal.Quotient.mk _ (invariantSubstitution K f * P)) q =
      (Ideal.Quotient.mk J f) * pairedNeutralQuotientLinearEquiv K J (Ideal.Quotient.mk _ P) q
    rw [pairedNeutralQuotientLinearEquiv_mk, pairedWeightExtraction_invariant_mul,
      map_mul, pairedNeutralQuotientLinearEquiv_mk]

/-- Quotient coordinates are extracted before reduction and then reduced coefficientwise. -/
theorem pairedNeutralQuotientEquiv_mk (J : Ideal (MvPolynomial ι K))
    (P : MvPolynomial (ι ⊕ ι) K) (q : ι → ℤ) :
    pairedNeutralQuotientEquiv K J (Ideal.Quotient.mk _ P) q =
      Ideal.Quotient.mk J (pairedWeightExtraction K q P) :=
  pairedNeutralQuotientLinearEquiv_mk K J P q

/-- The images of minimal weight monomials give a basis after arbitrary neutral relations. -/
def pairedNeutralQuotientBasis (J : Ideal (MvPolynomial ι K)) :
    Basis (ι → ℤ) (MvPolynomial ι K ⧸ J)
      (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) :=
  Basis.ofRepr (pairedNeutralQuotientEquiv K J)

theorem pairedNeutralQuotientBasis_apply (J : Ideal (MvPolynomial ι K)) (q : ι → ℤ) :
    pairedNeutralQuotientBasis K J q = Ideal.Quotient.mk _ (minimalPairedMonomial K q) := by
  apply (pairedNeutralQuotientBasis K J).repr.injective
  rw [Basis.repr_self]
  rw [show (pairedNeutralQuotientBasis K J).repr = pairedNeutralQuotientEquiv K J from rfl]
  ext r
  rw [pairedNeutralQuotientEquiv_mk]
  have he := pairedWeightExtraction_smul_minimal K r q (1 : MvPolynomial ι K)
  rw [one_smul] at he
  rw [he]
  by_cases h : q = r <;> simp [h]

/-- The whole paired quotient is free over its neutral coefficient quotient. -/
theorem pairedNeutralQuotient_free (J : Ideal (MvPolynomial ι K)) :
    Module.Free (MvPolynomial ι K ⧸ J)
      (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) :=
  Module.Free.of_basis (pairedNeutralQuotientBasis K J)

/-- Every neutral specialization remains faithfully flat, including nonreduced specializations. -/
theorem pairedNeutralQuotient_faithfullyFlat (J : Ideal (MvPolynomial ι K)) :
    Module.FaithfullyFlat (MvPolynomial ι K ⧸ J)
      (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) :=
  Module.FaithfullyFlat.of_linearEquiv _ _ (pairedNeutralQuotientEquiv K J)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralQuotientBasis
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralQuotientEquiv_mk
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralQuotient_faithfullyFlat
