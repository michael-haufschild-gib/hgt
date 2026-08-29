import GaloisForLFunctions.HTGeometry.GaussianJetLawNondegeneracy
import GaloisForLFunctions.HTGeometry.RandomEntireConditionedOrbitFreeness

/-!
# The planar Gaussian entire function has an almost surely free translation orbit

The planar Gaussian entire function `∑ₙ ξₙ zⁿ/√(n!)` has absolutely continuous finite jet laws away
from the origin, so for every countable set of distinct shifts almost every realization has a
translation orbit satisfying no nonzero polynomial-coefficient differential relation — and this
survives adding any deterministic entire passport.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*}

/-- **Almost-sure maximal translation-orbit freeness of the planar Gaussian entire function.** -/
theorem ae_translationOrbit_free_gaussianEntireSource [Countable H]
    (shift : H → ℂ) (hshift : Function.Injective shift) :
    ∀ᵐ x ∂gaussianCoefficientLaw,
      ∀ (n : ℕ) (lab : Fin n → H), Function.Injective lab →
        ∀ P : MvPolynomial (RelationJetVar 1 n) (MvPolynomial (Fin 1) ℂ), P ≠ 0 →
          ∃ z : Fin 1 → ℂ,
            jetRelationValue
              (fun i => oneDimEntireTranslate (shift (lab i)) (gaussianEntireSource x)) P z ≠ 0 :=
  ae_translationOrbit_free_of_avoidingJetLaws _ shift hshift _ _
    (hasAvoidingAbsolutelyContinuousFiniteAffineJetLaws_gaussianEntireSource shift)

/-- **Deterministic passports do not change the Gaussian conclusion.** -/
theorem ae_translationOrbit_free_gaussianEntireSource_add_const [Countable H]
    (shift : H → ℂ) (hshift : Function.Injective shift) (g : MultivariateEntire 1) :
    ∀ᵐ x ∂gaussianCoefficientLaw,
      ∀ (n : ℕ) (lab : Fin n → H), Function.Injective lab →
        ∀ P : MvPolynomial (RelationJetVar 1 n) (MvPolynomial (Fin 1) ℂ), P ≠ 0 →
          ∃ z : Fin 1 → ℂ,
            jetRelationValue
              (fun i => oneDimEntireTranslate (shift (lab i)) (gaussianEntireSource x + g)) P z
              ≠ 0 :=
  ae_translationOrbit_free_of_avoidingJetLaws _ shift hshift _ _
    ((hasAvoidingAbsolutelyContinuousFiniteAffineJetLaws_gaussianEntireSource shift).add_const
      _ _ _ _ g)

end

end GaloisForLFunctions.HTGeometry
