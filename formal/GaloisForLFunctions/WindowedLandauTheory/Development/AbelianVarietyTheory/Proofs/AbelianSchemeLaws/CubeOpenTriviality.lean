import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.SeesawOpenTriviality
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.SmallExtensionGroupSquare

/-! For an abelian square normalized on the two axes, a trivial fibre has an
open neighborhood of triviality. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
open GlobalTheory.LineBundleSections

namespace GlobalTheory.AbLaw.Cube

attribute [local instance] Over.cartesianMonoidalCategory

private abbrev Trivial {X : Scheme.{0}} (L : LB X) : Prop := ∃ t : L.Gen, t.IsGen

private theorem pull_trivial {X Y Z : Scheme.{0}} {L : LB X} {a : Y ⟶ X}
    {b : Z ⟶ Y} {c : Z ⟶ X} (h : b ≫ a = c) (ht : Trivial (L.pull a)) :
    Trivial (L.pull c) := by
  rw [← h]
  obtain ⟨t, ht⟩ := ht
  exact ⟨_, ht.pullGen (fun _ : PUnit => a) (fun _ => 1) b⟩

variable {R : Type} [CommRing R] {A : Over (Spec (CommRingCat.of R))} [GrpObj A]
  {L : LB (A ⊗ A).left}

private theorem lifts_trivialization
    (hA : IsAbelianScheme A) (hL : L.IsLB)
    (h₁ : Trivial (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left))
    (h₂ : Trivial (L.pull (lift (1 : A ⟶ A) (𝟙 A)).left))
    {T : Type} [CommRing T] [IsLocalRing T] (α : R →+* T) (ε : T)
    (hann : ∀ a ∈ IsLocalRing.maximalIdeal T, a * ε = 0)
    (hε : ε ∈ IsLocalRing.maximalIdeal T) :
    let f := (A ⊗ A).hom
    let q := Spec.map (CommRingCat.ofHom α)
    let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))
    Trivial (L.pull (pullback.fst (pullback.snd f q) i ≫ pullback.fst f q)) →
      Trivial (L.pull (pullback.fst f q)) := by
  dsimp only
  intro ht
  let f := (A ⊗ A).hom
  let q := Spec.map (CommRingCat.ofHom α)
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))
  let B := (Over.pullback q).obj A
  letI : GrpObj B := inferInstanceAs (GrpObj ((Over.pullback q).obj A))
  have hB : IsAbelianScheme B := hA.pullback q
  letI : IsCommMonObj B := hB.comm
  let b := pφ₂ q A
  let g := (B ⊗ B).hom
  have H : IsPullback b g f q := pφ₂_isPullback q A
  let e := H.isoPullback
  let F := pullback.fst g i
  let j := pullback.lift (f := pullback.snd f q) (g := i) (F ≫ e.hom) (pullback.snd g i)
    (by rw [Category.assoc, H.isoPullback_hom_snd]; exact pullback.condition)
  have hj : j ≫ (pullback.fst (pullback.snd f q) i ≫ pullback.fst f q) = F ≫ b := by
    dsimp only [j]
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, H.isoPullback_hom_fst]
  obtain ⟨v, hv⟩ := pull_trivial hj ht
  obtain ⟨t, ht⟩ := exists_gen_nested_pull hL b F hv
  have hid : (Over.pullback q).map (𝟙 A) = 𝟙 B := (Over.pullback q).map_id A
  have hone : (Over.pullback q).map (1 : A ⟶ A) = (1 : B ⟶ B) := (Over.pullback q).map_one
  have haxis₁ : Trivial ((L.pull b).pull (lift (𝟙 B) (1 : B ⟶ B)).left) := by
    have h : (lift (𝟙 B) (1 : B ⟶ B)).left ≫ b =
        pφ q A ≫ (lift (𝟙 A) (1 : A ⟶ A)).left := by
      have e := congrArg₂ (fun u v : B ⟶ B => (lift u v).left ≫ b) hid hone
      exact e.symm.trans (lift_pφ₂ q A (𝟙 A) (1 : A ⟶ A))
    obtain ⟨w, hw⟩ := pull_trivial h.symm h₁
    exact exists_gen_nested_pull hL b _ hw
  have haxis₂ : Trivial ((L.pull b).pull (lift (1 : B ⟶ B) (𝟙 B)).left) := by
    have h : (lift (1 : B ⟶ B) (𝟙 B)).left ≫ b =
        pφ q A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
      have e := congrArg₂ (fun u v : B ⟶ B => (lift u v).left ≫ b) hone hid
      exact e.symm.trans (lift_pφ₂ q A (1 : A ⟶ A) (𝟙 A))
    obtain ⟨w, hw⟩ := pull_trivial h.symm h₂
    exact exists_gen_nested_pull hL b _ hw
  have htB : Trivial (L.pull b) :=
    SmallExtension.exists_gen_of_small_extension hB (hL.pull b) hann hε
      (IsPullback.of_hasPullback g i) t ht haxis₁ haxis₂
  exact pull_trivial H.isoPullback_inv_fst htB

/-- A trivial fibre of a normalized line bundle on an abelian square extends to a
principal neighborhood of the base point. -/
theorem trivial_on_basicOpen_of_trivial_fibre
    (hA : IsAbelianScheme A) (hL : L.IsLB) (P : PerfectSections (A ⊗ A).hom L)
    (h₁ : Trivial (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left))
    (h₂ : Trivial (L.pull (lift (1 : A ⟶ A) (𝟙 A)).left))
    {K : Type} [Field K] (α : R →+* K)
    {Y : Scheme.{0}} {π : Y ⟶ (A ⊗ A).left} {g : Y ⟶ Spec (CommRingCat.of K)}
    (H : IsPullback π g (A ⊗ A).hom (Spec.map (CommRingCat.ofHom α))) (ht : Trivial (L.pull π)) :
    ∃ r : R, α r ≠ 0 ∧ Trivial (L.pull ((A ⊗ A).hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι) := by
  have h := hA.tensor hA
  haveI := h.proper
  haveI := h.geomConnected
  haveI : Smooth g := MorphismProperty.of_isPullback H h.smooth
  haveI : IsProper g := MorphismProperty.of_isPullback H h.proper
  haveI : GeometricallyConnected g := MorphismProperty.of_isPullback H h.geomConnected
  haveI : IsIso g.appTop := GlobalTheory.GlobalFunctions.isIso_app_of_geometricallyConnected g ⊤
  exact Seesaw.trivial_on_basicOpen_of_small_extension_lifting hL P α H
    (ConcreteCategory.bijective_of_isIso g.appTop).2 ht
    (fun T _ _ α e hann he => lifts_trivialization hA hL h₁ h₂ α e hann he)

end GlobalTheory.AbLaw.Cube
