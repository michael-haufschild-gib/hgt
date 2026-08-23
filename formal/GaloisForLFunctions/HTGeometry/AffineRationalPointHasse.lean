import GaloisForLFunctions.HTGeometry.AffineRationalPointSeparation

/-!
# Hasse detection on affine rational points

For an affine coordinate ring over an algebraically closed field, quotienting by the radical makes
evaluation on the full zero locus faithful.  Thus global quotient classes are exactly their
realized point-evaluation profiles, and equality or vanishing can be checked pointwise.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

/-- Simultaneous evaluation of a radical affine coordinate-ring class at all rational points. -/
def affineVarietyRadicalPointEvaluationMap
    {C : Type u} [Field C] [IsAlgClosed C]
    {sigma : Type v} [Finite sigma]
    (I : Ideal (MvPolynomial sigma C)) :
    (MvPolynomial sigma C ⧸ I.radical) →ₐ[C]
      (AffineVarietyPoint I.radical → C) where
  toFun z x := affineVarietyPointEvaluation I.radical x z
  map_one' := by funext x; exact map_one _
  map_mul' z w := by funext x; exact map_mul _ _ _
  map_zero' := by funext x; exact map_zero _
  map_add' z w := by funext x; exact map_add _ _ _
  commutes' c := by funext x; exact (affineVarietyPointEvaluation I.radical x).commutes c

/-- Simultaneous evaluation on the complete affine zero locus loses no radical quotient class. -/
theorem affineVarietyRadicalPointEvaluationMap_injective
    {C : Type u} [Field C] [IsAlgClosed C]
    {sigma : Type v} [Finite sigma]
    (I : Ideal (MvPolynomial sigma C)) :
    Function.Injective (affineVarietyRadicalPointEvaluationMap I) := by
  intro z w h
  apply affineVarietyPointEvaluation_jointlyInjective I.radical
    (Ideal.radical_isRadical I)
  exact h

/-- A radical affine coordinate ring is algebra-equivalent to the rational-point profiles it
actually realizes. -/
noncomputable def affineVarietyRadicalPointHasseEquivRange
    {C : Type u} [Field C] [IsAlgClosed C]
    {sigma : Type v} [Finite sigma]
    (I : Ideal (MvPolynomial sigma C)) :
    (MvPolynomial sigma C ⧸ I.radical) ≃ₐ[C]
      AlgHom.range (affineVarietyRadicalPointEvaluationMap I) :=
  AlgEquiv.ofBijective
    (AlgHom.rangeRestrict (affineVarietyRadicalPointEvaluationMap I))
    ⟨fun _ _ h => affineVarietyRadicalPointEvaluationMap_injective I
        (congrArg Subtype.val h),
      AlgHom.rangeRestrict_surjective _⟩

/-- The realized-profile equivalence evaluates by simultaneous rational-point evaluation. -/
@[simp] theorem affineVarietyRadicalPointHasseEquivRange_apply
    {C : Type u} [Field C] [IsAlgClosed C]
    {sigma : Type v} [Finite sigma]
    (I : Ideal (MvPolynomial sigma C))
    (z : MvPolynomial sigma C ⧸ I.radical) :
    (affineVarietyRadicalPointHasseEquivRange I z).1 =
      affineVarietyRadicalPointEvaluationMap I z := by
  rfl

/-- Two radical affine coordinate-ring classes agree exactly when every rational-point evaluation
agrees. -/
theorem affineVarietyRadicalPoint_congr_hasse_iff
    {C : Type u} [Field C] [IsAlgClosed C]
    {sigma : Type v} [Finite sigma]
    (I : Ideal (MvPolynomial sigma C))
    (z w : MvPolynomial sigma C ⧸ I.radical) :
    (∀ x : AffineVarietyPoint I.radical,
      affineVarietyPointEvaluation I.radical x z =
        affineVarietyPointEvaluation I.radical x w) ↔ z = w := by
  constructor
  · intro h
    apply affineVarietyRadicalPointEvaluationMap_injective I
    funext x
    exact h x
  · rintro rfl x
    rfl

/-- A radical affine coordinate-ring class vanishes exactly when it vanishes at every rational
point. -/
theorem affineVarietyRadicalPoint_eq_zero_hasse_iff
    {C : Type u} [Field C] [IsAlgClosed C]
    {sigma : Type v} [Finite sigma]
    (I : Ideal (MvPolynomial sigma C))
    (z : MvPolynomial sigma C ⧸ I.radical) :
    (∀ x : AffineVarietyPoint I.radical,
      affineVarietyPointEvaluation I.radical x z = 0) ↔ z = 0 := by
  rw [← affineVarietyRadicalPoint_congr_hasse_iff I z 0]
  simp

end


end GaloisForLFunctions.HTGeometry
