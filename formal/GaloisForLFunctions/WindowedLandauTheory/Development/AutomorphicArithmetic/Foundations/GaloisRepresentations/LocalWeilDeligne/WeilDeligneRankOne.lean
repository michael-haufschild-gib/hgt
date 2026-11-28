import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneCharacterTwists
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.IrreducibleWeilDeligne

/-! A smooth character gives a rank-one Weil–Deligne parameter.
Its determinant is the original character. Character twisting
on classes composes by multiplication. -/

noncomputable section

open NumberField IsDedekindDomain Module Polynomial
open WindowedLandauTheory.ConjugateSelfDual

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def WDRep.ofChar (χ : Weil h →* ℂˣ) (hs : IsSmooth χ) : WDRep h (Fin 1 → ℂ) :=
  ofChars (fun _ : Fin 1 => χ) (fun _ => hs)

@[simp] theorem WDRep.ofChar_ρ_apply (χ : Weil h →* ℂˣ) (hs : IsSmooth χ)
    (s : Weil h) (x : Fin 1 → ℂ) (i : Fin 1) :
    (ofChar χ hs).ρ s x i = (χ s : ℂ) * x i := rfl

theorem WDRep.ofChar_irreducible (χ : Weil h →* ℂˣ) (hs : IsSmooth χ) :
    (ofChar χ hs).ρ.IsIrreducible := by
  let a := ofChar χ hs
  letI : Nontrivial (Subrepresentation a.ρ) :=
    ⟨⊥, ⊤, fun he => bot_ne_top (congrArg Subrepresentation.toSubmodule he)⟩
  refine ⟨fun U => ?_⟩
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  apply Subrepresentation.toSubmodule_injective
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨v, hv, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := U.toSubmodule)
    (fun h => hU (Subrepresentation.toSubmodule_injective h))
  have hd : Module.finrank ℂ (Fin 1 → ℂ) = 1 := by simp [Module.finrank_fintype_fun_eq_card]
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hd hv₀ x
  exact U.toSubmodule.smul_mem c hv

namespace WD

def lpOfChar (χ : Weil h →* ℂˣ) (hs : IsSmooth χ) : WD h := WD.mk (WDRep.ofChar χ hs)

theorem irreducible_lpOfChar (χ : Weil h →* ℂˣ) (hs : IsSmooth χ) : (lpOfChar χ hs).Irreducible :=
  (irreducible_mk_iff _).mpr (WDRep.ofChar_irreducible χ hs)

@[simp] theorem lpDim_lpOfChar (χ : Weil h →* ℂˣ) (hs : IsSmooth χ) :
    (lpOfChar χ hs).lpDim = 1 := by
  rw [lpOfChar, lpDim_mk, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

theorem charpoly_lpOfChar (χ : Weil h →* ℂˣ) (hs : IsSmooth χ) (s : Weil h) :
    (lpOfChar χ hs).charpoly s = X - C (χ s : ℂ) := by
  rw [lpOfChar, charpoly_mk, WDRep.ofChar, WDRep.charpoly_ofChars, Fin.prod_univ_one]

@[simp] theorem detChar_lpOfChar (χ : Weil h →* ℂˣ) (hs : IsSmooth χ) :
    (lpOfChar χ hs).detChar = χ := by
  apply MonoidHom.ext
  intro s
  apply Units.ext
  rw [lpOfChar, detChar_mk]
  change LinearMap.det ((WDRep.ofChar χ hs).ρ s) = (χ s : ℂ)
  rw [LinearMap.det_eq_sign_charpoly_coeff, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    ← charpoly_mk, ← lpOfChar, charpoly_lpOfChar]
  simp

theorem lpTwist_mul (x : WD h) (χ ξ : Weil h →* ℂˣ) (hχ : IsSmooth χ) (hξ : IsSmooth ξ)
    (hprod : IsSmooth (χ * ξ)) :
    (x.lpTwist χ hχ).lpTwist ξ hξ = x.lpTwist (χ * ξ) hprod := by
  refine WD.ind (fun n a => ?_) x
  simp only [lpTwist_mk]
  apply sound
  refine ⟨LinearEquiv.refl ℂ _, fun s v => ?_, fun v => rfl⟩
  change (ξ s : ℂ) • ((χ s : ℂ) • (a.ρ s) v) = ((χ * ξ) s : ℂ) • (a.ρ s) v
  rw [smul_smul, MonoidHom.mul_apply, Units.val_mul, mul_comm]

@[simp] theorem lpTwist_one (x : WD h) (hs : IsSmooth (1 : Weil h →* ℂˣ)) :
    x.lpTwist 1 hs = x := by
  refine WD.ind (fun n a => ?_) x
  rw [lpTwist_mk]
  refine sound ⟨LinearEquiv.refl ℂ _, fun s v => ?_, fun v => rfl⟩
  change (((1 : Weil h →* ℂˣ) s : ℂˣ) : ℂ) • (a.ρ s) v = _
  simp

end WD
end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.WD.irreducible_lpOfChar
#print axioms GlobalTheory.WeilDeligne.WD.detChar_lpOfChar
#print axioms GlobalTheory.WeilDeligne.WD.lpTwist_mul
