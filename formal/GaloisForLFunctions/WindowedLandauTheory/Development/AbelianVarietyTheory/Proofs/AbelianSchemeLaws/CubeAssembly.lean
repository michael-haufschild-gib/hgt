import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeClopenTriviality
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeFaces
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeNormalizedGluing
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FibreTrivialityCharts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProjectiveProducts
import Mathlib.AlgebraicGeometry.Noetherian

/-! The theorem of the cube for projective abelian schemes over a Noetherian affine base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LineBundleSections GlobalTheory.ProjectiveSections GlobalTheory.AbLaw.Seesaw UpperTheory.Cb
open scoped CategoryTheory.Obj

namespace GlobalTheory.AbLaw.Cube

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] [IsNoetherianRing R]
  {A : Over (Spec (CommRingCat.of R))} [GrpObj A]

/-- On a projective abelian scheme over a Noetherian affine base, the alternating
product trivializes globally. -/
theorem cube_gen_of_projective (hA : IsAbelianScheme A) (hproj : IsProjOver A.hom)
    {L : LB A.left} (hL : L.IsLB) :
    letI := hA.comm
    ∃ u : (cubeBundle A L).Gen, u.IsGen := by
  letI := hA.comm
  letI := hA.smooth
  letI := hA.proper
  letI := hA.geomConnected
  let M := cubeBundle A L
  have hM : M.IsLB := hL.linComb _ _
  let p := (cubeProjection A 2).left
  have h₂ : IsPullback (fst A A).left (snd A A).left A.hom A.hom :=
    IsPullback.of_hasPullback _ _
  have h₃ : IsPullback (fst A (A ⊗ A)).left (snd A (A ⊗ A)).left A.hom (A ⊗ A).hom :=
    IsPullback.of_hasPullback _ _
  haveI : Smooth (snd A A).left := MorphismProperty.of_isPullback h₂ hA.smooth
  haveI : IsProper (snd A A).left := MorphismProperty.of_isPullback h₂ hA.proper
  haveI : GeometricallyConnected (snd A A).left := MorphismProperty.of_isPullback h₂ hA.geomConnected
  haveI : Smooth (snd A (A ⊗ A)).left := MorphismProperty.of_isPullback h₃ hA.smooth
  haveI : IsProper (snd A (A ⊗ A)).left := MorphismProperty.of_isPullback h₃ hA.proper
  haveI : GeometricallyConnected (snd A (A ⊗ A)).left := MorphismProperty.of_isPullback h₃ hA.geomConnected
  haveI : Smooth p := by
    change Smooth ((snd A (A ⊗ A)).left ≫ (snd A A).left)
    infer_instance
  haveI : IsProper p := by
    change IsProper ((snd A (A ⊗ A)).left ≫ (snd A A).left)
    infer_instance
  haveI : GeometricallyConnected p :=
    GeometricallyConnected.comp (snd A (A ⊗ A)).left (snd A A).left
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨hClosed, hLocal⟩ := closed_and_locally_trivial_of_affine_charts hM p (fun t => by
    obtain ⟨_, ⟨V, hV, rfl⟩, ht, -⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ t) isOpen_univ
    obtain ⟨x, hx⟩ := hV.range_fromSpec.ge ht
    let T := Γ(A.left, V)
    haveI : IsNoetherianRing T := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    let j := hV.fromSpec
    let b := j ≫ A.hom
    let B := (Over.pullback b).obj A
    letI : GrpObj B := inferInstanceAs (GrpObj ((Over.pullback b).obj A))
    let f := (B ⊗ B).hom
    obtain ⟨q, H, hq₁, hq₂⟩ := exists_cube_chart A j
    haveI : IsOpenImmersion j := hV.isOpenImmersion_fromSpec
    have hB : IsAbelianScheme B := hA.pullback b
    letI : IsCommMonObj B := hB.comm
    have hBproj : IsProjOver B.hom := by
      obtain ⟨α, hα⟩ := Spec.map_surjective b
      apply isProjOver_baseChange α.hom (π := pullback.fst A.hom b) (f := A.hom)
      · rw [show Spec.map (CommRingCat.ofHom α.hom) = b from hα]
        exact IsPullback.of_hasPullback _ _
      · exact hproj
    have hprod : IsPullback (fst B B).left (snd B B).left B.hom B.hom :=
      IsPullback.of_hasPullback _ _
    have hproj' : IsProjOver f := isProjOver_product hprod hBproj hBproj
    let N := M.pull q
    have hN : N.IsLB := hM.pull q
    haveI := (hB.tensor hB).smooth
    obtain ⟨P⟩ := nonempty_perfectSections_of_projective f hN hproj'
    obtain ⟨Q⟩ := nonempty_perfectSections_of_projective f (dual_isLB hN) hproj'
    have hone : (1 : B ⟶ B).left ≫ pullback.fst A.hom b = (B.hom ≫ b) ≫ η[A].left :=
      (Category.assoc _ _ _).trans
        ((congrArg (B.hom ≫ ·) (GlobalTheory.GrpTangent.one_pullback_left_fst b A)).trans
          (Category.assoc _ _ _).symm)
    have h₁ : ∃ u : (N.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen := by
      apply (trivial_pull_linComb M hM (fun _ : PUnit => q) (fun _ => 1) _).2
      apply trivial_cube_face A hL _ 1 (B.hom ≫ b)
      rw [Category.assoc, hq₂, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact hone
    have h₂ : ∃ u : (N.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen := by
      apply (trivial_pull_linComb M hM (fun _ : PUnit => q) (fun _ => 1) _).2
      apply trivial_cube_face A hL _ 0 (B.hom ≫ b)
      rw [Category.assoc, hq₁, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact hone
    refine ⟨T, inferInstance, j, inferInstance, x, _, q, f, hx, H,
      (isClopen_fieldFibreTriviality hB hN P Q h₁ h₂).1, ?_⟩
    rintro y ⟨K, _, α, Y, π, g, hker, H₀, ht₀⟩
    obtain ⟨r, hr, u, hu⟩ := trivial_on_basicOpen_of_trivial_fibre hB hN P h₁ h₂ α H₀ ht₀
    exact ⟨r, by rw [← hker]; exact hr, u, hu⟩)
  have hclopen : IsClopen (fibreTriviality p M) := ⟨hClosed, isOpen_iff_forall_mem_open.mpr (fun t ht => by
    obtain ⟨U, hU, u, hu⟩ := hLocal t ht
    exact ⟨U, fun _ hy => mem_fibreTriviality_of_trivial_on_open p hy hu, U.isOpen, hU⟩)⟩
  have hall (t : A.left) : t ∈ fibreTriviality p M := by
    let b := (Spec (CommRingCat.of R)).fromSpecResidueField (A.hom t)
    let g := b ≫ η[A].left
    have hb : Set.range b = {A.hom t} := Scheme.range_fromSpecResidueField _
    obtain ⟨y, hy⟩ := hb.ge rfl
    have hg : g ≫ A.hom = b := by
      rw [Category.assoc, Over.w, Category.comp_id]
    refine (A.hom.isConnected_preimage_singleton (A.hom t)).isPreconnected.subset_isClopen hclopen
      ⟨g y, (congrArg (fun f => f y) hg).trans hy, ?_⟩ rfl
    refine ⟨_, inferInstance, g, _, _, _, ⟨y, rfl⟩, IsPullback.of_hasPullback p g, ?_⟩
    apply trivial_cube_face A hL (pullback.fst p g) 2 (pullback.snd p g ≫ b)
    exact pullback.condition.trans (Category.assoc _ _ _).symm
  let e : A ⟶ A ⊗ (A ⊗ A) := lift 1 (lift 1 (𝟙 A))
  have e₀ : e ≫ cubeProjection A 0 = 1 := by simp [e, cubeProjection]
  have e₂ : e ≫ cubeProjection A 2 = 𝟙 A := by simp [e, cubeProjection]
  apply exists_gen_of_local_triviality hL (cubeMorphism A) cubeExponent p e.left (congrArg Over.Hom.left e₂)
  · intro Z b U _ k
    apply cube_face_cancels A (b ≫ e.left) 0 (b ≫ A.hom) _ U k
    rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · intro t
    obtain ⟨U, hU, u, hu⟩ := hLocal t (hall t)
    exact ⟨U, hU, (trivial_pull_linComb L hL (cubeMorphism A) cubeExponent _).1 ⟨u, hu⟩⟩

end GlobalTheory.AbLaw.Cube
