import GaloisForLFunctions.HTGeometry.MovingCanonicalUpperEndDifferentialIndependence
import GaloisForLFunctions.HTGeometry.MovingCanonicalFullTranslationFreeness

/-!
# A phase whose whole translation family is differentially independent exists

Canonical freeness of a phase makes the full complex-translation family of its logarithmic derivative
differentially independent over the rational functions, and the canonically free phases form a dense
residual subset of the bounded sequences.  A dense subset of a nonempty space is nonempty, so the
freeness hypothesis is not merely generic — it is inhabited, and the translation family it produces
exists unconditionally.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **A completely free translation family exists.**  Some phase has a differentially independent
full complex-translation family in the upper-end meromorphic field, with no hypothesis: the
canonically free phases are dense, hence inhabited. -/
theorem exists_movingCanonicalTranslation_upperEnd_differentialIndependent :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    ∃ θ : BoundedRealSequence,
      DifferentialIndependent (RatFunc ℂ) (movingCanonicalTranslatedUpperEndMero θ) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  obtain ⟨hdense, -⟩ := movingCanonical_fullTranslationFreeness_denseResidual
  obtain ⟨θ, hθ⟩ := hdense.nonempty
  exact ⟨θ, movingCanonicalTranslation_upperEnd_differentialIndependent θ hθ⟩

/-- **A completely free translation orbit exists, in function form.**  Some phase has a logarithmic
derivative no finite family of whose distinct translates satisfies a differential relation. -/
theorem exists_movingCanonicalLogDerivative_fullTranslation_free :
    ∃ θ : BoundedRealSequence, ∀ (m : ℕ) (shift : InjectiveShiftConfiguration (Fin m)),
      ¬ FamilyDifferentiallyAlgebraicOn
        (fun i z => movingCanonicalLogDerivative θ (z + shift.1 i))
        (commonUpperTranslationDomain shift) := by
  obtain ⟨hdense, -, hfree⟩ := movingCanonical_fullTranslationFreeness_denseResidual
  obtain ⟨θ, hθ⟩ := hdense.nonempty
  exact ⟨θ, hfree θ hθ⟩

end

end GaloisForLFunctions.HTGeometry
