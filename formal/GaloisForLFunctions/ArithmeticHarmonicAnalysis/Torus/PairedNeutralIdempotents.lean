import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.LaurentIdempotents
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedNeutralNilpotence

/-!
# Paired substitution preserves all idempotents

For every neutral ideal, including nonlinear and nonreduced ones, every
idempotent of the paired quotient comes from a unique idempotent of the
neutral quotient. Each oriented Laurent image is constant. Choosing the
orientation matching a weight therefore forces every nonzero relative
weight coefficient of an idempotent to vanish. The remaining zero-weight
coefficient recovers the unique neutral idempotent.

The equivalence uses the canonical coefficient-ring embedding, so it
preserves the algebraic decompositions represented by idempotents.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
open scoped PairedNeutral
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- Neutral scalars have exactly one relative weight coefficient, at weight zero. -/
theorem pairedNeutralQuotientEquiv_algebraMap (J : Ideal (MvPolynomial ι K))
    (r : MvPolynomial ι K ⧸ J) (q : ι → ℤ) :
    pairedNeutralQuotientEquiv K J
      (algebraMap (MvPolynomial ι K ⧸ J)
        (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) r) q =
      if q = 0 then r else 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
  change pairedNeutralQuotientEquiv K J (Ideal.Quotient.mk _ (invariantSubstitution K f)) q = _
  rw [pairedNeutralQuotientEquiv_mk]
  have he := pairedWeightExtraction_smul_minimal K q 0 f
  rw [minimalPairedMonomial_zero, pairedNeutral_smul, mul_one] at he
  rw [he]
  by_cases hq : q = 0
  · subst q
    simp
  · simp [hq, Ne.symm hq]

/-- Constant Laurent images kill every nonzero relative weight of an idempotent. -/
theorem pairedNeutral_idempotent_nonzero_weight (J : Ideal (MvPolynomial ι K))
    (x : MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))
    (hx : IsIdempotentElem x) (q : ι → ℤ) (hq : q ≠ 0) :
    pairedNeutralQuotientEquiv K J x q = 0 := by
  have he := congrArg (fun f : NeutralLaurent K J => f.coeff q)
    (laurent_idempotent_eq_constantCoeff
      (pairedQuotientChartMap K J (weightOrientation q) x)
      (hx.map (pairedQuotientChartMap K J (weightOrientation q))))
  rw [pairedQuotientChartMap_recovers] at he
  simpa [AddMonoidAlgebra.coeff_single, hq, Ne.symm hq] using he

/-- Every paired idempotent is the image of its zero-weight neutral coefficient. -/
theorem pairedNeutral_idempotent_eq_algebraMap (J : Ideal (MvPolynomial ι K))
    (x : MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))
    (hx : IsIdempotentElem x) :
    x = algebraMap (MvPolynomial ι K ⧸ J)
      (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))
        (pairedNeutralQuotientEquiv K J x 0) := by
  apply (pairedNeutralQuotientEquiv K J).injective
  ext q
  rw [pairedNeutralQuotientEquiv_algebraMap]
  by_cases hq : q = 0
  · simp [hq]
  · rw [if_neg hq]
    exact pairedNeutral_idempotent_nonzero_weight K J x hx q hq

/-- An element is idempotent exactly when it is the image of a neutral idempotent. -/
theorem pairedNeutralQuotient_isIdempotent_iff (J : Ideal (MvPolynomial ι K))
    (x : MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) :
    IsIdempotentElem x ↔ ∃ r : MvPolynomial ι K ⧸ J, IsIdempotentElem r ∧
      algebraMap (MvPolynomial ι K ⧸ J)
        (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) r = x := by
  constructor
  · intro hx
    refine ⟨pairedNeutralQuotientEquiv K J x 0, ?_,
      (pairedNeutral_idempotent_eq_algebraMap K J x hx).symm⟩
    apply pairedNeutralQuotient_algebraMap_injective K J
    rw [map_mul, ← pairedNeutral_idempotent_eq_algebraMap K J x hx]
    exact hx
  · rintro ⟨r, hr, rfl⟩
    exact hr.map (algebraMap (MvPolynomial ι K ⧸ J)
      (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)))

/-- The canonical coefficient embedding gives a bijection on all idempotents. -/
def pairedNeutralIdempotentEquiv (J : Ideal (MvPolynomial ι K)) :
    {r : MvPolynomial ι K ⧸ J // IsIdempotentElem r} ≃
      {x : MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K) // IsIdempotentElem x} :=
  Equiv.ofBijective (fun r => ⟨algebraMap (MvPolynomial ι K ⧸ J)
      (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) r.1,
    r.2.map (algebraMap (MvPolynomial ι K ⧸ J)
      (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)))⟩)
    ⟨fun _ _ h => Subtype.ext (pairedNeutralQuotient_algebraMap_injective K J
        (congrArg Subtype.val h)), by
      intro x
      obtain ⟨r, hr, he⟩ := (pairedNeutralQuotient_isIdempotent_iff K J x.1).mp x.2
      exact ⟨⟨r, hr⟩, Subtype.ext he⟩⟩

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutral_idempotent_eq_algebraMap
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralQuotient_isIdempotent_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralIdempotentEquiv
