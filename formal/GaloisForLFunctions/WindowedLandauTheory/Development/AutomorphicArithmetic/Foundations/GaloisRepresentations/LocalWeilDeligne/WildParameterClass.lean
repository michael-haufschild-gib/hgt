import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneTameness
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.IrreducibleWeilDeligne
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.NonscalarWildWeilExistence
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WildParameterTwistSeparation
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneCharacterTwists

/-! In ranks at least two there are irreducible Weil–Deligne
classes with unitary determinant outside every twist of a tame class. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A v}

theorem exists_wild_parameter_class (h : IsPlaceOver A v) (n : ℕ) (hn : 2 ≤ n) :
    ∃ x : WD h, x.Irreducible ∧ x.lpDim = n ∧ (∀ s, ‖(x.detChar s : ℂ)‖ = 1) ∧
      ∀ (y : WD h) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ), y.Tame → x ≠ y.lpTwist χ hχ := by
  obtain ⟨a, ha, -, hd, t, ht, hscalar⟩ := exists_irreducible_nonscalarWild E Ω h n hn
  refine ⟨WD.mk a, (WD.irreducible_mk_iff a).mpr ha, ?_, ?_, ?_⟩
  · rw [WD.lpDim_mk, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  · intro s
    rw [WD.detChar_mk]
    exact hd s
  · intro y χ hχ hy
    obtain ⟨m, b, rfl⟩ := y.exists_rep
    rw [WD.lpTwist_mk]
    intro hEq
    exact a.not_iso_twist_tame_of_nonscalar_wild t ht hscalar b ((WD.tame_mk_iff b).mp hy) χ hχ
      (WD.mk_eq_mk.mp hEq)

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.exists_wild_parameter_class
