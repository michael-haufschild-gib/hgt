import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGenericBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.IntegralPELObjectPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.IntegralPELObjectFactorization

/-! The universal properties identify integral and generic representing schemes once the
polarization kernel and geometric Tate conditions agree. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.UPel.HT.GenCmp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R']
  {b : Base D R} {gb : GBase D.toG R'} {N : ℕ} {φ : R →+* R'}

/-- Compatibility of the geometric objects induces the comparison isomorphism by representability. -/
theorem cmp_of (hρ : gb.ρ = φ b.ρ) (ht : ∀ i, gb.t i = φ.comp (b.t i))
    (hA : ∀ (S : Scheme.{0}) (t : S ⟶ Sp R') (o : Obj (Base.ofGeneric (D := D) gb) N t), GeomFull o t)
    (hB : ∀ (S : Scheme.{0}) (t : S ⟶ Sp R') (o : GObj gb N t), KerP o)
    (M : RepFam b N) (X : GenModel gb N) :
    ∃ j : X.X ⟶ pullback M.s (spMap φ), IsIso j ∧ j ≫ pullback.snd _ _ = X.s ∧
      IsGPull X.univ M.univ (j ≫ pullback.fst _ _) := by
  let p₁ : pullback M.s (spMap φ) ⟶ M.X := pullback.fst _ _
  let p₂ : pullback M.s (spMap φ) ⟶ Sp R' := pullback.snd _ _
  obtain ⟨oS, ⟨m₀⟩⟩ := HTPull.exists_objMap_pull p₁ M.univ
  have hs : p₁ ≫ M.s = p₂ ≫ spMap φ := pullback.condition
  let rS := rebase hρ ht hs oS
  let gS : GObj gb N p₂ := toGObj rS (hA _ _ rS)
  let oX : Obj b N (X.s ≫ spMap φ) := toObj hρ ht X.univ (hB _ _ _)
  obtain ⟨f, ⟨hf, ⟨mf⟩⟩, -⟩ := X.rep _ _ gS
  obtain ⟨g, ⟨hg, ⟨mg⟩⟩, -⟩ := M.rep _ _ oX
  let j : X.X ⟶ pullback M.s (spMap φ) := pullback.lift g X.s hg
  have j₁ : j ≫ p₁ = g := pullback.lift_fst _ _ _
  have j₂ : j ≫ p₂ = X.s := pullback.lift_snd _ _ _
  have mf' : ObjMap oS oX f := ⟨mf.φ, mf.φ₂, mf.cart, mf.sq, mf.act, mf.pol, mf.eta⟩
  have e₁ : f ≫ g = p₁ := (M.rep _ _ oS).unique
    ⟨by rw [Category.assoc, hg, ← Category.assoc, hf, hs], ⟨mf'.comp mg⟩⟩
    ⟨rfl, ⟨m₀⟩⟩
  obtain ⟨mj⟩ := ObjMap.factor (j₁.symm ▸ mg) m₀
  let me := mj.comp mf'
  let mi := ObjMap.refl oX
  have e₂ : j ≫ f = 𝟙 _ := (X.rep _ _ X.univ).unique
    ⟨by rw [Category.assoc, hf, j₂], ⟨⟨me.φ, me.φ₂, me.cart, me.sq, me.act, me.pol, me.eta⟩⟩⟩
    ⟨Category.id_comp _, ⟨⟨mi.φ, mi.φ₂, mi.cart, mi.sq, mi.act, mi.pol, mi.eta⟩⟩⟩
  have e₃ : f ≫ j = 𝟙 _ := by
    apply pullback.hom_ext
    · change (f ≫ j) ≫ p₁ = 𝟙 _ ≫ p₁
      rw [Category.assoc, j₁, e₁, Category.id_comp]
    · change (f ≫ j) ≫ p₂ = 𝟙 _ ≫ p₂
      rw [Category.assoc, j₂, hf, Category.id_comp]
  refine ⟨j, ⟨f, e₂, e₃⟩, j₂, ?_⟩
  change IsGPull X.univ M.univ (j ≫ p₁)
  rw [j₁]
  exact ⟨mg.φ, mg.φ₂, mg.cart, mg.sq, mg.act, mg.pol, mg.eta⟩

end GlobalTheory.UPel.HT.GenCmp
