import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FinitePlaceOfAbsoluteValuation

/-! The centres of the same absolute valuation lie over one another
along compatible number-field embeddings. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Reciprocity

theorem liesOver_of_compatible_absolute_centres
    {E M Ω : Type*} [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω]
    [Algebra E M] [Algebra E Ω] [Algebra M Ω]
    {A : ValuationSubring Ω} {u : HeightOneSpectrum (𝓞 E)} {w : HeightOneSpectrum (𝓞 M)}
    (hu : IsPlaceOver A u) (hw : IsPlaceOver A w)
    (h : ∀ x : E, algebraMap M Ω (algebraMap E M x) = algebraMap E Ω x) :
    w.asIdeal.LiesOver u.asIdeal := by
  constructor
  apply Ideal.ext
  intro x
  change x ∈ u.asIdeal ↔ algebraMap (𝓞 E) (𝓞 M) x ∈ w.asIdeal
  rw [← hu x, ← hw (algebraMap (𝓞 E) (𝓞 M) x)]
  change A.valuation (algebraMap E Ω (x : E)) < 1 ↔
    A.valuation (algebraMap M Ω (algebraMap E M (x : E))) < 1
  rw [h]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.liesOver_of_compatible_absolute_centres
