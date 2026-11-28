import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneRankOne
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneTameness
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.TameArtinCharacters

/-! The determinant identifies an irreducible rank-one parameter
with its Weil character. Geometric Artin writes tameness as the
triviality of that character on first principal units. -/

noncomputable section

open NumberField IsDedekindDomain Matrix
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.Reciprocity GlobalTheory.TameKummer

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A v}

theorem WD.eq_lpOfChar_of_lpDim_eq_one (x : WD h) (hx : x.Irreducible) (hd : x.lpDim = 1) :
    x = WD.lpOfChar x.detChar x.smooth_detChar := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  simp only [WD.lpDim_mk, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hd
  subst n
  have hc (ξ η : Weil h →* ℂˣ) (hξ : IsSmooth ξ) (hη : IsSmooth η) (he : ξ = η) :
      WD.lpOfChar ξ hξ = WD.lpOfChar η hη := by
    subst η
    rfl
  refine Eq.trans ?_ (hc a.detChar (WD.mk a).detChar a.smooth_detChar (WD.mk a).smooth_detChar
    (WD.detChar_mk a).symm)
  apply WD.sound
  refine ⟨LinearEquiv.refl ℂ _, ?_, ?_⟩
  · intro s w
    let u : Fin 1 → ℂ := fun _ => 1
    have hu : Pi.single (0 : Fin 1) (1 : ℂ) = u := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simp [u, hi]
    have he : (a.detChar s : ℂ) = a.ρ s u 0 := by
      change LinearMap.det (a.ρ s) = _
      rw [← LinearMap.det_toMatrix', Matrix.det_fin_one, LinearMap.toMatrix'_apply, hu]
    change a.ρ s w = (WDRep.ofChar a.detChar _).ρ s w
    have hw : w = w 0 • u := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simp [u, hi]
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [WDRep.ofChar_ρ_apply, he]
    nth_rw 1 [hw]
    rw [map_smul]
    exact mul_comm _ _
  · intro w
    change a.N w = 0
    simp only [a.monodromy_eq_zero_of_irreducible ((WD.irreducible_mk_iff a).mp hx), LinearMap.zero_apply]

theorem WD.tame_lpOfChar_iff (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) :
    (WD.lpOfChar χ hχ).Tame ↔ ∀ σ : Weil h, σ.val ∈ wildInertia A → χ σ = 1 := by
  rw [WD.lpOfChar, WD.tame_mk_iff]
  constructor
  · intro ht σ hσ
    apply Units.ext
    have he := LinearMap.congr_fun (ht σ hσ) (fun _ : Fin 1 => (1 : ℂ))
    simpa only [WDRep.ofChar_ρ_apply, Module.End.one_apply, mul_one, Units.val_one] using congrFun he 0
  · intro ht σ hσ
    apply LinearMap.ext
    intro x
    funext i
    rw [WDRep.ofChar_ρ_apply, ht σ hσ, Units.val_one, one_mul]
    rfl

theorem WD.tame_lpOfArtinChar_iff {α : Weil h →* (v.adicCompletion E)ˣ} (hα : IsLocalArtin E Ω α)
    (χ : (v.adicCompletion E)ˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set (v.adicCompletion E)ˣ)) :
    (WD.lpOfChar (χ.comp α) (IsLocalArtin.smooth E Ω hα hχ)).Tame ↔
      ∀ u : (v.adicCompletion E)ˣ, u ∈ unitsLevel v 1 → χ u = 1 := by
  rw [tame_lpOfChar_iff]
  exact localArtin_char_kills_wild_iff (h := h) hα χ

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.WD.eq_lpOfChar_of_lpDim_eq_one
#print axioms GlobalTheory.WeilDeligne.WD.tame_lpOfArtinChar_iff
