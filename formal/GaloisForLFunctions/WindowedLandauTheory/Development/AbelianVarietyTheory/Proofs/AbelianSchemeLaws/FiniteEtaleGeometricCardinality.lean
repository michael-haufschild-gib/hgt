import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TotallySplit

/-! Finite étale geometric fibres have cardinality equal to their rank. -/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace GlobalTheory.FinEt

private theorem card_spec_sections {k : Type u} [Field k] [IsSepClosed k]
    {A : CommRingCat.{u}} (a : CommRingCat.of k ⟶ A)
    [IsFinite (Spec.map a)] [Etale (Spec.map a)] (z : Spec (CommRingCat.of k)) :
    Finite {f : Spec (CommRingCat.of k) ⟶ Spec A // f ≫ Spec.map a = 𝟙 _} ∧
      Nat.card {f : Spec (CommRingCat.of k) ⟶ Spec A // f ≫ Spec.map a = 𝟙 _} =
        (Spec.map a).finrank z := by
  classical
  letI : Algebra k A := a.hom.toAlgebra
  haveI : Algebra.Etale k A :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := a)).mp inferInstance
  haveI : Module.Finite k A := (IsFinite.SpecMap_iff a).mp inferInstance
  haveI : IsArtinianRing A := .of_finite k A
  letI : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  let e := Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum k A
  have hR : Module.finrank k A = Nat.card (PrimeSpectrum A) := by
    rw [(Algebra.FormallyEtale.equivPiOfIsSepClosed k A).toLinearEquiv.finrank_eq,
      Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
  let g (f : A →ₐ[k] k) : {f : Spec (CommRingCat.of k) ⟶ Spec A // f ≫ Spec.map a = 𝟙 _} :=
    ⟨Spec.map (CommRingCat.ofHom f.toRingHom), by
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext v
      exact f.commutes v⟩
  have hg : Function.Bijective g := by
    constructor
    · intro f₁ f₂ h
      have h' := Spec.map_injective (congrArg Subtype.val h)
      exact AlgHom.ext fun x => congrArg (fun f : A ⟶ CommRingCat.of k => f.hom x) h'
    · intro y
      obtain ⟨b, hb⟩ := Spec.map_surjective y.1
      have h : a ≫ b = 𝟙 _ := Spec.map_injective (by
        rw [Spec.map_comp, Spec.map_id, hb]
        exact y.2)
      let f : A →ₐ[k] k :=
        { toRingHom := b.hom
          commutes' := fun v => congrArg (fun u : CommRingCat.of k ⟶ CommRingCat.of k => u.hom v) h }
      exact ⟨f, Subtype.ext hb⟩
  haveI : Finite (A →ₐ[k] k) := Finite.of_equiv _ e.symm
  refine ⟨Finite.of_surjective g hg.2, ?_⟩
  rw [← Nat.card_eq_of_bijective g hg, Nat.card_congr e, ← hR]
  change Module.finrank k A = (Spec.map (CommRingCat.ofHom (algebraMap k A))).finrank z
  rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free] <;> rfl

private theorem card_etale_sections {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [IsFinite p] [Etale p] (z : Spec (CommRingCat.of k)) :
    Finite {f : Spec (CommRingCat.of k) ⟶ X // f ≫ p = 𝟙 _} ∧
      Nat.card {f : Spec (CommRingCat.of k) ⟶ X // f ≫ p = 𝟙 _} = p.finrank z := by
  haveI : IsAffine X := isAffine_of_isAffineHom p
  let e := X.isoSpec
  let q := e.inv ≫ p
  let a := Spec.preimage q
  have ha : Spec.map a = q := by simp [a]
  haveI : IsFinite (Spec.map a) := ha.symm ▸ (inferInstanceAs (IsFinite (e.inv ≫ p)))
  haveI : Etale (Spec.map a) := ha.symm ▸ (inferInstanceAs (Etale (e.inv ≫ p)))
  obtain ⟨hfinite, hr⟩ := card_spec_sections a z
  have hq : (Spec.map a).finrank z = p.finrank z := by
    rw [ha, show q = e.inv ≫ p from rfl, Scheme.Hom.finrank_comp_left_of_isIso]
  let E : {f : Spec (CommRingCat.of k) ⟶ X // f ≫ p = 𝟙 _} ≃
      {f : Spec (CommRingCat.of k) ⟶ Spec Γ(X, ⊤) // f ≫ Spec.map a = 𝟙 _} :=
    { toFun := fun f => ⟨f.1 ≫ e.hom, by rw [ha, show q = e.inv ≫ p from rfl]; simpa using f.2⟩
      invFun := fun f => ⟨f.1 ≫ e.inv, by rw [Category.assoc, ← show q = e.inv ≫ p from rfl, ← ha]; exact f.2⟩
      left_inv := fun f => Subtype.ext (by simp)
      right_inv := fun f => Subtype.ext (by simp) }
  haveI := hfinite
  exact ⟨Finite.of_equiv _ E.symm, (Nat.card_congr E).trans (hr.trans hq)⟩

/-- Geometric points of a finite étale fibre are counted by the local rank. -/
theorem card_points_eq_finrank {X S : Scheme.{u}} (p : X ⟶ S) [IsFinite p] [Etale p]
    {k : Type u} [Field k] [IsSepClosed k] (t : Spec (CommRingCat.of k) ⟶ S)
    (z : Spec (CommRingCat.of k)) :
    Finite {x : Spec (CommRingCat.of k) ⟶ X // x ≫ p = t} ∧
      Nat.card {x : Spec (CommRingCat.of k) ⟶ X // x ≫ p = t} = p.finrank (t z) := by
  obtain ⟨hfinite, hr⟩ := card_etale_sections (pullback.snd p t) z
  rw [Scheme.Hom.finrank_pullback_snd] at hr
  let g (x : {x : Spec (CommRingCat.of k) ⟶ X // x ≫ p = t}) :
      Spec (CommRingCat.of k) ⟶ pullback p t :=
    pullback.lift x.1 (𝟙 _) (x.2.trans (Category.id_comp t).symm)
  have hg₁ (x) : g x ≫ pullback.fst p t = x.1 := pullback.lift_fst _ _ _
  have hg₂ (x) : g x ≫ pullback.snd p t = 𝟙 _ := pullback.lift_snd _ _ _
  let E : {x : Spec (CommRingCat.of k) ⟶ X // x ≫ p = t} ≃
      {s : Spec (CommRingCat.of k) ⟶ pullback p t // s ≫ pullback.snd p t = 𝟙 _} :=
    { toFun := fun x => ⟨g x, hg₂ x⟩
      invFun := fun s => ⟨s.1 ≫ pullback.fst p t, by
        rw [Category.assoc, pullback.condition, ← Category.assoc, s.2, Category.id_comp]⟩
      left_inv := fun x => Subtype.ext (hg₁ x)
      right_inv := fun s => Subtype.ext (pullback.hom_ext (hg₁ _) ((hg₂ _).trans s.2.symm)) }
  haveI := hfinite
  exact ⟨Finite.of_equiv _ E.symm, (Nat.card_congr E).trans hr⟩

end GlobalTheory.FinEt
