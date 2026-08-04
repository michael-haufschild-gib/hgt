import GaloisForLFunctions.HTGeometry.MovingCanonicalTranslationExistence
import GaloisForLFunctions.HTGeometry.FiniteShadowCapacity

/-!
# Faithfulness on the active quotient is exactly freedom of a pulled-back orbit

A structural lattice acts on a pulled-back observable only through its image in the noncompact
quotient.  For such an observable the active-quotient law needs no analytic input at all: a lattice
direction killed by the quotient makes the orbit literally repeat, which already destroys freedom,
and a faithful lattice picks an injectively indexed subfamily of a completely free translation family.

The freedom of that translation family is not an assumption either -- a phase with a differentially
independent full complex-translation family exists -- so the equivalence has an explicit witness.

For an *arbitrary* observable, rather than a pulled-back one, the forward direction is the
compact-shadow theorem: a killed direction generates a cyclic orbit trapped in the compact kernel,
where capacity is finite.  That passage is
`activeQuotient_injective_of_fullOrbitFree_of_kernelCyclic_not`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The active-quotient law for a pulled-back observable.**  The translation orbit of a free
translation family along a lattice map is differentially independent exactly when that map is
injective: freedom forces a faithful index, and faithfulness selects a free subfamily. -/
theorem differentialIndependent_translationOrbit_iff_injective
    {F K L : Type*} [CommRing F] [Nontrivial F] [CommRing K] [Algebra F K] [Differential K]
    [AddCommGroup L] {T : ℂ → K} (hT : DifferentialIndependent F T) (q : L →+ ℂ) :
    DifferentialIndependent F (fun l : L => T (q l)) ↔ Function.Injective q := by
  constructor
  · intro h a b hab
    exact h.injective (by rw [hab])
  · intro hq
    simpa only [Function.comp_def] using hT.comp (fun l : L => q l) hq

/-- **A faithful lattice carries a completely free orbit.**  Translating by an injective image of the
lattice inside the complex plane picks an injectively indexed subfamily of a completely free
translation family, and such a family exists. -/
theorem exists_differentialIndependent_translationOrbit_of_injective
    {L : Type*} [AddCommGroup L] (q : L →+ ℂ) (hq : Function.Injective q) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    ∃ θ : BoundedRealSequence, DifferentialIndependent (RatFunc ℂ)
      fun l : L => movingCanonicalTranslatedUpperEndMero θ (q l) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  obtain ⟨θ, hθ⟩ := exists_movingCanonicalTranslation_upperEnd_differentialIndependent
  exact ⟨θ, (differentialIndependent_translationOrbit_iff_injective hθ q).2 hq⟩

/-- **The active-quotient law with an explicit carrier.**  Some phase realizes the equivalence: its
translation orbit along a lattice map is free exactly when the map is faithful. -/
theorem exists_translationOrbit_differentialIndependent_iff_injective
    {L : Type*} [AddCommGroup L] (q : L →+ ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    ∃ θ : BoundedRealSequence,
      (DifferentialIndependent (RatFunc ℂ)
        fun l : L => movingCanonicalTranslatedUpperEndMero θ (q l)) ↔ Function.Injective q := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  obtain ⟨θ, hθ⟩ := exists_movingCanonicalTranslation_upperEnd_differentialIndependent
  exact ⟨θ, differentialIndependent_translationOrbit_iff_injective hθ q⟩

end

end GaloisForLFunctions.HTGeometry
