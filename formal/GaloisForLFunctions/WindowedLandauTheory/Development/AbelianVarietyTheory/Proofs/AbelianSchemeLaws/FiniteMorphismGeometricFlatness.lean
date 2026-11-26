import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FiniteFlatFibreCriterion
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.GroupMultiplicationEtale
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Tactic.WLOG

/-! A finite morphism with source flat over a locally Noetherian base is flat
if its geometric fibres over the base are flat. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace GlobalTheory.FiniteFibreFlat

open GrpTangent (isPullback_baseChange)

private theorem flat_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@Flat : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat (by
    refine RingHom.CodescendsAlong.mk _ RingHom.Flat.respectsIso fun R C B _ _ _ _ _ h h' => ?_
    rw [RingHom.flat_algebraMap_iff] at h' ⊢
    rw [RingHom.faithfullyFlat_algebraMap_iff] at h
    exact Module.Flat.of_flat_tensorProduct R B C)

variable {X Y S T : Scheme.{0}}

/-- Every pullback of a morphism to a scheme over the given change of base is flat. -/
private def FlatOver (f : X ⟶ Y) (g : Y ⟶ S) (t : T ⟶ S) : Prop :=
  ∀ ⦃W Z : Scheme.{0}⦄ (a : W ⟶ X) (b : W ⟶ Z) (j : Z ⟶ Y) (h : Z ⟶ T),
    IsPullback a b f j → j ≫ g = h ≫ t → Flat b

private theorem FlatOver.target {f : X ⟶ Y} {g : Y ⟶ S} {t : T ⟶ S}
    (H : FlatOver f g t) {X' Y' : Scheme.{0}} {a' : X' ⟶ X} {f' : X' ⟶ Y'}
    {u : Y' ⟶ Y} (sq : IsPullback a' f' f u) : FlatOver f' (u ≫ g) t :=
  fun _ _ a b j h sq' e => H (a ≫ a') b (j ≫ u) h (sq'.paste_horiz sq) (by simpa using e)

private theorem FlatOver.source {f : X ⟶ Y} {g : Y ⟶ S} {t : T ⟶ S}
    (H : FlatOver f g t) {X' : Scheme.{0}} (i : X' ⟶ X) [Flat i] :
    FlatOver (i ≫ f) g t := by
  intro W Z a b j h sq e
  letI : Flat (pullback.snd f j) := H _ _ j h (IsPullback.of_hasPullback f j) e
  let c : W ⟶ pullback f j := pullback.lift (a ≫ i) b (by simpa using sq.w)
  have hc : c ≫ pullback.snd f j = b := pullback.lift_snd _ _ _
  have sq₂ : IsPullback a c i (pullback.fst f j) :=
    IsPullback.of_bot (by rw [hc]; exact sq) (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback f j)
  letI : Flat c := MorphismProperty.of_isPullback sq₂ ‹Flat i›
  rw [← hc]
  infer_instance

private theorem flatOver_of_pullback {X Y : Over S} (f : X ⟶ Y) (t : T ⟶ S)
    (H : Flat ((Over.pullback t).map f).left) : FlatOver f.left Y.hom t := by
  intro W Z a b j h sq e
  let j' : Z ⟶ pullback Y.hom t := pullback.lift j h e
  have hj : j' ≫ pullback.fst Y.hom t = j := pullback.lift_fst _ _ _
  let m : pullback X.hom t ⟶ pullback Y.hom t := ((Over.pullback t).map f).left
  have sq₀ : IsPullback (pullback.fst X.hom t) m f.left (pullback.fst Y.hom t) :=
    isPullback_baseChange t f
  let a' : W ⟶ pullback X.hom t :=
    sq₀.lift a (b ≫ j') (by rw [Category.assoc, hj]; exact sq.w)
  have sq₁ : IsPullback a' b m j' :=
    IsPullback.of_right (by rw [hj, sq₀.lift_fst]; exact sq) (sq₀.lift_snd _ _ _) sq₀
  exact MorphismProperty.of_isPullback sq₁ H

private theorem flatOver_descend {T' : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ S} {t : T ⟶ S}
    (σ : T' ⟶ T) [Surjective σ] [Flat σ] [QuasiCompact σ]
    (H : FlatOver f g (σ ≫ t)) : FlatOver f g t := by
  intro W Z a b j h sq e
  letI := flat_descendsAlong_fpqc
  have sq₁ := IsPullback.of_hasPullback b (pullback.fst h σ)
  have hflat : Flat (pullback.snd b (pullback.fst h σ)) :=
    H _ _ _ (pullback.snd h σ) (sq₁.paste_horiz sq)
      (by rw [Category.assoc, e, ← Category.assoc, pullback.condition, Category.assoc])
  let Q : MorphismProperty Scheme.{0} := @Surjective ⊓ @Flat ⊓ @QuasiCompact
  have hbase : Q (pullback.fst h σ) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat) (Q := Q) sq₁.flip hbase hflat

private theorem flat_of_flatOver_fields (f : X ⟶ Y) (g : Y ⟶ S) (hY : IsLocallyNoetherian Y)
    (hSource : Flat (f ≫ g)) (hf : IsFinite f)
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) :
    Flat f := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  · letI hNoether : IsLocallyNoetherian Y := hY
    letI hFinite : IsFinite f := hf
    refine IsZariskiLocalAtTarget.of_openCover (S.affineCover.pullback₁ g) fun i => ?_
    let u := S.affineCover.f i
    let v := pullback.fst g u
    let q := pullback.snd g u
    let f' := pullback.snd f v
    have sq := IsPullback.of_hasPullback f v
    have sq' := IsPullback.of_hasPullback g u
    change Flat f'
    refine this f' q (LocallyOfFiniteType.isLocallyNoetherian v)
      (MorphismProperty.of_isPullback (P := @Flat) (sq.paste_vert sq') hSource) inferInstance
      (fun k _ t => ?_) ⟨_, rfl⟩
    intro W Z a b j h sq₀ e
    refine (H k (t ≫ u)).target sq a b j h sq₀ ?_
    have hv : v ≫ g = q ≫ u := sq'.w
    calc
      j ≫ v ≫ g = j ≫ q ≫ u := congrArg (j ≫ ·) hv
      _ = (j ≫ q) ≫ u := (Category.assoc j q u).symm
      _ = (h ≫ t) ≫ u := congrArg (· ≫ u) e
      _ = h ≫ t ≫ u := Category.assoc h t u
  obtain ⟨R, rfl⟩ := hS
  wlog hA : ∃ A, Y = Spec A generalizing X Y
  · letI hNoether : IsLocallyNoetherian Y := hY
    letI hFinite : IsFinite f := hf
    refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    let u := Y.affineCover.f i
    let f' := pullback.snd f u
    have sq := IsPullback.of_hasPullback f u
    have e : f' ≫ u ≫ g = pullback.fst f u ≫ f ≫ g :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ g) sq.w.symm).trans (Category.assoc _ _ _))
    letI hFlat : Flat (f ≫ g) := hSource
    change Flat f'
    exact this f' (LocallyOfFiniteType.isLocallyNoetherian u) inferInstance (u ≫ g)
      (e.symm ▸ (inferInstance : Flat (pullback.fst f u ≫ f ≫ g)))
      (fun k _ t => (H k t).target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hA
  wlog hX : ∃ B, X = Spec B generalizing X
  · letI hFinite : IsFinite f := hf
    letI hAffine : IsAffine X := isAffine_of_isAffineHom f
    letI hFlat : Flat (f ≫ g) := hSource
    let i : Spec Γ(X, ⊤) ⟶ X := X.isoSpec.inv
    letI hIso : IsIso i := inferInstanceAs (IsIso X.isoSpec.inv)
    have hi : Flat ((i ≫ f) ≫ g) := (Category.assoc i f g).symm ▸
      (inferInstance : Flat (i ≫ (f ≫ g)))
    rw [← MorphismProperty.cancel_left_of_respectsIso @Flat i]
    exact this (i ≫ f) inferInstance hi (fun k _ t => (H k t).source i) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp, Flat.SpecMap_iff] at hSource
  rw [Flat.SpecMap_iff]
  rw [IsFinite.SpecMap_iff] at hf
  rw [isLocallyNoetherian_Spec] at hY
  letI : Algebra R A := g.hom.toAlgebra
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra R B := (g ≫ f).hom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsNoetherianRing A := hY
  letI : Module.Flat R B := hSource
  letI : Module.Finite A B := hf
  apply RingHom.flat_algebraMap_iff.mpr
  refine flat_of_flat_fibres (R := R) (A := A) (B := B) fun k C _ _ _ t h e => ?_
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)
  have hflat := H k (Spec.map (CommRingCat.ofHom t)) _ _ _ (Spec.map (CommRingCat.ofHom h)) sq.flip
    (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      exact e)
  rw [Flat.SpecMap_iff] at hflat
  change (algebraMap C (C ⊗[A] B)).Flat at hflat
  exact RingHom.flat_algebraMap_iff.mp hflat

/-- A finite morphism from a flat scheme to a locally finite type scheme over a locally
Noetherian base is flat if every geometric fibre over the base is flat. -/
theorem flat_of_isFinite_of_flat_geometric_fibres [IsLocallyNoetherian S]
    (X Y : Over S) (f : X ⟶ Y) (hX : Flat X.hom) [LocallyOfFiniteType Y.hom] (hf : IsFinite f.left)
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      Flat ((Over.pullback t).map f).left) : Flat f.left := by
  refine flat_of_flatOver_fields f.left Y.hom (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
    (by rwa [Over.w]) hf fun k _ t => ?_
  let σ := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  letI : Surjective σ := ⟨fun y => ⟨IsLocalRing.closedPoint (AlgebraicClosure k), Subsingleton.elim _ y⟩⟩
  haveI : Flat σ := by
    change Flat (Spec.map _)
    rw [Flat.SpecMap_iff]
    exact (RingHom.flat_algebraMap_iff (R := k) (S := AlgebraicClosure k)).mpr inferInstance
  exact flatOver_descend σ (flatOver_of_pullback f _ (H _ _))

end GlobalTheory.FiniteFibreFlat
