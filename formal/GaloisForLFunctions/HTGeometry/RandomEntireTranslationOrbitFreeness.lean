import GaloisForLFunctions.HTGeometry.FiniteJetLawDeterministicGauge
import GaloisForLFunctions.HTGeometry.RandomEntireJetLawNondegeneracy

/-!
# A concrete random entire source with an almost surely free translation orbit

The clamped independent-coefficient series has absolutely continuous finite jet laws, so the
almost-sure maximal translation-orbit freeness theorem applies to it: for every countable set of
distinct shifts, almost surely every finite family of distinct translates satisfies no nonzero
polynomial-coefficient differential relation.  Adding any deterministic entire source — a finite
deterministic passport — leaves the conclusion unchanged.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*}

/-- **Almost-sure maximal translation-orbit freeness, realized.** -/
theorem ae_translationOrbit_free_boundedRandomEntire [Countable H]
    (shift : H → ℂ) (hshift : Function.Injective shift) :
    ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => complexSquareProbability)),
      ∀ (n : ℕ) (lab : Fin n → H), Function.Injective lab →
        ∀ P : MvPolynomial (RelationJetVar 1 n) (MvPolynomial (Fin 1) ℂ), P ≠ 0 →
          ∃ z : Fin 1 → ℂ,
            jetRelationValue
              (fun i => oneDimEntireTranslate (shift (lab i)) (boundedRandomEntireSource x)) P z
              ≠ 0 :=
  ae_translationOrbit_no_polynomialDifferentialRelation _ shift hshift _
    (hasAbsolutelyContinuousFiniteAffineJetLaws_boundedRandomEntire shift)

/-- **Deterministic passports do not change the conclusion.** -/
theorem ae_translationOrbit_free_boundedRandomEntire_add_const [Countable H]
    (shift : H → ℂ) (hshift : Function.Injective shift) (g : MultivariateEntire 1) :
    ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => complexSquareProbability)),
      ∀ (n : ℕ) (lab : Fin n → H), Function.Injective lab →
        ∀ P : MvPolynomial (RelationJetVar 1 n) (MvPolynomial (Fin 1) ℂ), P ≠ 0 →
          ∃ z : Fin 1 → ℂ,
            jetRelationValue
              (fun i => oneDimEntireTranslate (shift (lab i))
                (boundedRandomEntireSource x + g)) P z ≠ 0 :=
  ae_translationOrbit_no_polynomialDifferentialRelation_add_const _ shift hshift _
    (hasAbsolutelyContinuousFiniteAffineJetLaws_boundedRandomEntire shift) g

/-- The one-generator specialization: almost surely the source satisfies no nonzero
polynomial-coefficient differential relation. -/
theorem ae_no_polynomialDifferentialRelation_boundedRandomEntire :
    ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => complexSquareProbability)),
      ∀ (n : ℕ) (lab : Fin n → Unit), Function.Injective lab →
        ∀ P : MvPolynomial (RelationJetVar 1 n) (MvPolynomial (Fin 1) ℂ), P ≠ 0 →
          ∃ z : Fin 1 → ℂ,
            jetRelationValue
              (fun _ => oneDimEntireTranslate 0 (boundedRandomEntireSource x)) P z ≠ 0 :=
  ae_translationOrbit_free_boundedRandomEntire (H := Unit) (fun _ => 0)
    (Function.injective_of_subsingleton _)

end

end GaloisForLFunctions.HTGeometry
