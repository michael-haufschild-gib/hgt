import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneOperations

/-! Tameness of a Weil–Deligne class is equality of the wild
invariant dimension and the full dimension. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TameKummer

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A v}

/-- The whole space is fixed by wild inertia. -/
def WD.Tame (x : WD h) : Prop :=
  x.lpTame.lpDim = x.lpDim

theorem WD.tame_mk_iff {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) : (WD.mk a).Tame ↔ a.Tame := by
  rw [WD.Tame, WD.lpTame_mk, WD.lpDim_mk, WD.lpDim_mk]
  exact a.tame_iff_finrank_tameSpace.symm

theorem WD.Tame.twist {x : WD h} (hx : x.Tame) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ)
    (hχw : ∀ σ : Weil h, σ.val ∈ wildInertia A → χ σ = 1) :
    (x.lpTwist χ hχ).Tame := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  rw [WD.lpTwist_mk, WD.tame_mk_iff]
  intro σ hσ
  change (χ σ : ℂ) • a.ρ σ = 1
  rw [hχw σ hσ, Units.val_one, one_smul, (WD.tame_mk_iff a).mp hx σ hσ]

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.WD.Tame.twist
