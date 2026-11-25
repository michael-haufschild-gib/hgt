import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProperAffineGlobalSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothGeometricIntegrality

/-! Proper smooth morphisms with geometrically connected fibres preserve the structure sheaf. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace GlobalTheory.ProperFunctions

variable {X S : Scheme.{0}}

theorem isIso_app_of_isBasis (p : X ⟶ S) {ι : Type*} (B : ι → S.Opens)
    (hB : TopologicalSpace.Opens.IsBasis (Set.range B))
    (h : ∀ i, IsIso (p ∣_ B i).appTop) (U : S.Opens) : IsIso (p.app U) := by
  have h1 : ∀ i, IsIso (p.app (B i)) := by
    intro i
    have := h i
    rw [morphismRestrict_appTop] at this
    have := (@isIso_comp_right_iff _ _ _ _ _ (p.app ((B i).ι ''ᵁ ⊤)) _
      (by rw [eqToHom_op]; exact Functor.map_isIso _ _)).mp this
    rwa [(B i).ι_image_top] at this
  let φ : S.sheaf ⟶ (TopCat.Sheaf.pushforward _ p.base).obj X.sheaf := ⟨p.c⟩
  letI : IsIso φ := TopCat.Sheaf.isIso_iff_isIso_basis hB h1
  letI : IsIso φ.hom := (TopCat.Sheaf.forget _ _).map_isIso φ
  exact NatIso.isIso_app_of_isIso φ.hom (op U)

theorem isIso_app_of_forall_affineOpens (p : X ⟶ S)
    (h : ∀ U : S.affineOpens, IsIso (p ∣_ U.1).appTop) (U : S.Opens) : IsIso (p.app U) :=
  isIso_app_of_isBasis p (fun U : S.affineOpens ↦ U.1) (by simpa using S.isBasis_affineOpens) h U

end GlobalTheory.ProperFunctions

namespace GlobalTheory.GlobalFunctions

section Main

variable {X S T : Scheme.{0}}

private theorem isIso_appTop_of_section (p : X ⟶ S)
    [IsAffine S] [Smooth p] [IsProper p] [GeometricallyIntegral p] (i : T ⟶ X) [IsAffine T]
    [Smooth i] [Surjective i] (s : S ⟶ T) (hs : s ≫ i ≫ p = 𝟙 S) : IsIso p.appTop := by
  have : IsAffineHom i := IsAffineHom.of_comp i p
  let Z := pullback i i
  have : IsAffine Z := isAffine_of_isAffineHom (pullback.fst i i)
  have h1 : (i ≫ p).appTop.hom.Smooth := by
    rw [← ProperFunctions.appLE_top_top _ le_top]
    exact (i ≫ p).smooth_appLE (isAffineOpen_top _) (isAffineOpen_top _) _
  have h2 : (pullback.fst i i ≫ i ≫ p).appTop.hom.Smooth := by
    rw [← ProperFunctions.appLE_top_top _ le_top]
    exact (pullback.fst i i ≫ i ≫ p).smooth_appLE (isAffineOpen_top _) (isAffineOpen_top _) _
  algebraize [(i ≫ p).appTop.hom, (pullback.fst i i ≫ i ≫ p).appTop.hom]
  let f : Γ(T, ⊤) →ₐ[Γ(S, ⊤)] Γ(Z, ⊤) :=
    { (pullback.fst i i).appTop.hom with
      commutes' := fun c ↦ congr($(Scheme.Hom.comp_appTop (pullback.fst i i) (i ≫ p)) c).symm }
  let g : Γ(T, ⊤) →ₐ[Γ(S, ⊤)] Γ(Z, ⊤) :=
    { (pullback.snd i i).appTop.hom with
      commutes' := fun c ↦ by
        have h := Scheme.Hom.comp_appTop (pullback.snd i i) (i ≫ p)
        rw [← pullback.condition_assoc] at h
        exact congr($h c).symm }
  let r : Γ(T, ⊤) →ₐ[Γ(S, ⊤)] Γ(S, ⊤) :=
    { s.appTop.hom with
      commutes' := fun c ↦ by
        have h := Scheme.Hom.comp_appTop s (i ≫ p)
        rw [hs, Scheme.Hom.id_appTop] at h
        exact congr($h c).symm }
  have : GeometricallyIntegral (p ≫ S.isoSpec.hom) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
      (IsPullback.of_horiz_isIso (fst := 𝟙 X) (f := p) (g := S.isoSpec.inv) ⟨by simp⟩) ‹_›
  have H : IsPullback (Spec.map (pullback.fst i i).appTop) (Spec.map (pullback.snd i i).appTop)
      (T.isoSpec.inv ≫ i) (T.isoSpec.inv ≫ i) :=
    (IsPullback.of_hasPullback i i).of_iso Z.isoSpec T.isoSpec T.isoSpec (.refl _)
      (Scheme.isoSpec_hom_naturality _).symm (Scheme.isoSpec_hom_naturality _).symm
      (by simp) (by simp)
  have hφ : (T.isoSpec.inv ≫ i) ≫ p ≫ S.isoSpec.hom = Spec.map (i ≫ p).appTop := by
    rw [Category.assoc, Iso.inv_comp_eq, Scheme.isoSpec_hom_naturality, Category.assoc]
  have := isIso_appTop_of_cover (R := Γ(S, ⊤)) (p ≫ S.isoSpec.hom) (T.isoSpec.inv ≫ i)
    f g H hφ r
  rw [Scheme.Hom.comp_appTop] at this
  have : IsIso S.isoSpec.hom.appTop := inferInstanceAs (IsIso (S.isoSpec.hom.app ⊤))
  exact IsIso.of_isIso_comp_left S.isoSpec.hom.appTop p.appTop

/-- Pulling back to a smooth affine cover provides a lift of the diagonal section. -/
theorem isIso_appTop_of_isAffine (p : X ⟶ S)
    [IsAffine S] [Smooth p] [IsProper p] [GeometricallyIntegral p] : IsIso p.appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth)
  have : MorphismProperty.ContainsIdentities @Smooth.{0} := ⟨fun _ ↦ inferInstance⟩
  obtain ⟨T, i, _, hi, _⟩ := X.exists_hom_isAffine_of_isZariskiLocalAtSource @Smooth
  let j : pullback (i ≫ p) (i ≫ p) ⟶ pullback p (i ≫ p) :=
    pullback.lift (pullback.fst _ _ ≫ i) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition)
  have hj2 : j ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hj : IsPullback (pullback.fst _ _) j i (pullback.fst p (i ≫ p)) :=
    IsPullback.of_bot (by rw [hj2]; exact .of_hasPullback _ _) (pullback.lift_fst _ _ _).symm
      (.of_hasPullback _ _)
  have : Smooth j := MorphismProperty.of_isPullback hj ‹_›
  have : Surjective j := MorphismProperty.of_isPullback hj ‹_›
  have := isIso_appTop_of_section (pullback.snd p (i ≫ p)) j (pullback.diagonal (i ≫ p))
    (by rw [hj2, pullback.diagonal_snd])
  exact ProperFunctions.isIso_appTop_of_isPullback_of_surjective (.of_hasPullback p (i ≫ p))

/-- Every function on the preimage of an open set is a unique pullback from that open set. -/
theorem isIso_app (p : X ⟶ S)
    [Smooth p] [IsProper p] [GeometricallyIntegral p] (U : S.Opens) : IsIso (p.app U) :=
  ProperFunctions.isIso_app_of_forall_affineOpens p (fun V ↦
    have : IsAffine V.1 := V.2
    isIso_appTop_of_isAffine (p ∣_ V.1)) U

end Main

/-- A proper smooth morphism with geometrically connected fibres induces a ring isomorphism on sections. -/
theorem isIso_app_of_geometricallyConnected {X S : Scheme.{0}} (p : X ⟶ S)
    [Smooth p] [IsProper p] [GeometricallyConnected p] (U : S.Opens) : IsIso (p.app U) := by
  letI := geometricallyIntegral_of_quasiCompact_of_smooth_of_geometricallyConnected p
  exact isIso_app p U

end GlobalTheory.GlobalFunctions
