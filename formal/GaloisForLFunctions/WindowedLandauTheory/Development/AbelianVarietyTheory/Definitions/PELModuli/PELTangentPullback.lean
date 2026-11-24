import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGroupPullbacks

/-! Lie eigenspaces and their multiplicities are preserved by cartesian maps of group schemes. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback)
open GlobalTheory.GrpTangent GlobalTheory.UPel.HT

namespace GlobalTheory.LiePull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {f : S' ⟶ S} {φ : A'.left ⟶ A.left} {R : Type} [CommRing R]

/-- Pullback points commute with precomposition by a scalar map of the dual numbers. -/
theorem pushEquiv_epsScale (x : Sp R ⟶ S')
    (e : (epsPtR x ⟶ A') ≃* (epsPtR (x ≫ f) ⟶ A))
    (he : ∀ v, (e v).left = v.left ≫ φ) (c : R) (v : epsPtR x ⟶ A') :
    e ((Over.map x).map (epsScale c) ≫ v) =
      (Over.map (x ≫ f)).map (epsScale c) ≫ e v := by
  apply Over.OverMorphism.ext
  simp only [he, Over.comp_left, Category.assoc]
  rfl

/-- A tangent vector is a scalar eigenvector exactly when its image is. -/
theorem isTanScal_iff_of_pushEquiv (h : IsGrpPullback A' A f φ)
    {O : Type} [Ring O] (a : OActN O A) (a' : OActN O A')
    (hact : ∀ b, (a'.act b).left ≫ φ = φ ≫ (a.act b).left)
    (x : Sp R ⟶ S') (e : (epsPtR x ⟶ A') ≃* (epsPtR (x ≫ f) ⟶ A))
    (he : ∀ v, (e v).left = v.left ≫ φ) (b : O) (c : R) (v : epsPtR x ⟶ A') :
    IsTanScal a' x b c v ↔ IsTanScal a (x ≫ f) b c (e v) := by
  obtain ⟨e₀, he₀⟩ := exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have hz : e₀ (epsZeroAt x ≫ v) = epsZeroAt (x ≫ f) ≫ e v := by
    apply Over.OverMorphism.ext
    simp only [he₀, he, Over.comp_left, Category.assoc]
    rfl
  have ha : e (v ≫ a'.act b) = e v ≫ a.act b := by
    apply Over.OverMorphism.ext
    simp only [he, Over.comp_left, Category.assoc, hact]
  change ((epsZeroAt x ≫ v).left = (1 : Over.mk x ⟶ A').left ∧ _) ↔
    ((epsZeroAt (x ≫ f) ≫ e v).left = (1 : Over.mk (x ≫ f) ⟶ A).left ∧ _)
  refine and_congr ⟨?_, ?_⟩ ?_
  · intro hl
    have hl' : epsZeroAt x ≫ v = 1 := Over.OverMorphism.ext hl
    exact congrArg Over.Hom.left (hz.symm.trans
      ((congrArg e₀ hl').trans (map_one e₀)))
  · intro hr
    have hr' : epsZeroAt (x ≫ f) ≫ e v = 1 := Over.OverMorphism.ext hr
    exact congrArg Over.Hom.left (e₀.injective (hz.trans (hr'.trans (map_one e₀).symm)))
  · rw [← ha, ← pushEquiv_epsScale x e he]
    exact e.injective.eq_iff.symm

private theorem transport_basis {M N k : Type} [Monoid M] [Monoid N] (e : M ≃* N)
    {P : M → Prop} {Q : N → Prop} {σ : k → M → M} {τ : k → N → N}
    (hp : ∀ v, P v ↔ Q (e v)) (hs : ∀ c v, e (σ c v) = τ c (e v)) (d : ℕ)
    (H : ∃ v : Fin d → M, (∀ i, P (v i)) ∧ ∀ w, P w →
      ∃! c : Fin d → k, w = (List.ofFn fun i => σ (c i) (v i)).prod) :
    ∃ v : Fin d → N, (∀ i, Q (v i)) ∧ ∀ w, Q w →
      ∃! c : Fin d → k, w = (List.ofFn fun i => τ (c i) (v i)).prod := by
  obtain ⟨v, hv, hw⟩ := H
  refine ⟨fun i => e (v i), fun i => (hp _).mp (hv i), fun w hqw => ?_⟩
  obtain ⟨w, rfl⟩ := e.surjective w
  have hcoeff := hw w ((hp _).mpr hqw)
  refine (existsUnique_congr fun c => ?_).mp hcoeff
  rw [← e.injective.eq_iff]
  simp only [map_list_prod, List.map_ofFn, Function.comp_def, hs]

/-- The eigenspace multiplicity is invariant under the geometric pullback. -/
theorem lieMult_pull (h : IsGrpPullback A' A f φ) {O k : Type} [Ring O] [Field k]
    (a : OActN O A) (a' : OActN O A')
    (hact : ∀ b, (a'.act b).left ≫ φ = φ ≫ (a.act b).left) (x : Sp k ⟶ S')
    (τ : O →+* k) (d : ℕ) : LieMult a' x τ d ↔ LieMult a (x ≫ f) τ d := by
  obtain ⟨e, he⟩ := exists_pushEquiv h (epsPtR x) (epsPtR (x ≫ f)).hom (Category.assoc _ _ _).symm
  have hp v : (∀ b, IsTanScal a' x b (τ b) v) ↔
      (∀ b, IsTanScal a (x ≫ f) b (τ b) (e v)) :=
    forall_congr' fun b => isTanScal_iff_of_pushEquiv h a a' hact x e he b (τ b) v
  have hs := pushEquiv_epsScale x e he
  exact ⟨transport_basis e hp hs d,
    transport_basis e.symm
      (fun v => (hp (e.symm v)).symm.trans (by rw [e.apply_symm_apply]))
      (fun c v => e.injective (by rw [e.apply_symm_apply, hs, e.apply_symm_apply])) d⟩

end GlobalTheory.LiePull
