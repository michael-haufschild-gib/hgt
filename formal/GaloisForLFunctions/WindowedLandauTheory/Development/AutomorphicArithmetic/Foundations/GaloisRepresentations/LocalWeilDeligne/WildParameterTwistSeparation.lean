import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneOperations

/-! Every scalar twist of a tame action remains scalar on wild
inertia. A nonscalar wild operator excludes an isomorphism with
any such twist. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TameKummer

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A v}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem WDRep.not_iso_twist_tame_of_nonscalar_wild
    (a : WDRep h V) (t : Ine (F := E) A) (ht : t.val ∈ wildInertia A)
    (ha : ∀ z : ℂ, a.ρ (ineIncl h t) ≠ z • 1)
    (b : WDRep h W) (hb : b.Tame) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) :
    ¬ a.Iso (b.twist χ hχ) := by
  rintro ⟨e, he, -⟩
  let σ := ineIncl h t
  apply ha (χ σ : ℂ)
  apply LinearMap.ext
  intro v
  apply e.injective
  have hEq := he σ v
  change e (a.ρ σ v) = (χ σ : ℂ) • b.ρ σ (e v) at hEq
  rw [hb σ ht, Module.End.one_apply] at hEq
  rw [hEq]
  simp

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.WDRep.not_iso_twist_tame_of_nonscalar_wild
