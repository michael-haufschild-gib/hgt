import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Tactic.Algebraize

/-! Finiteness and étaleness can be detected after suitable surjective
precomposition. -/

open AlgebraicGeometry CategoryTheory TensorProduct

namespace GlobalTheory

private theorem ringHom_flat_of_comp_faithfullyFlat
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    {f : A →+* B} {g : B →+* C} (hg : g.FaithfullyFlat) (h : (g.comp f).Flat) :
    f.Flat := by
  algebraize [f, g, g.comp f]
  rw [RingHom.Flat, Module.Flat.iff_lTensor_injective']
  intro J
  change Function.Injective (AlgebraTensorModule.lTensor B B J.subtype)
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective B C]
  have hcomp : LinearMap.lTensor C (AlgebraTensorModule.lTensor B B J.subtype) =
      (AlgebraTensorModule.cancelBaseChange A B B C A).symm.toLinearMap ∘ₗ
        AlgebraTensorModule.lTensor B C J.subtype ∘ₗ
          (AlgebraTensorModule.cancelBaseChange A B B C J).toLinearMap := by
    ext
    simp
  rw [hcomp]
  simpa using Module.Flat.lTensor_preserves_injective_linearMap (M := C) J.subtype
    J.injective_subtype

private theorem ringHom_formallyUnramified_of_comp_faithfullyFlat
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    {f : A →+* B} {g : B →+* C} (hg : g.FaithfullyFlat) (hs : g.FormallySmooth)
    (hu : g.FormallyUnramified) (h : (g.comp f).FormallyUnramified) :
    f.FormallyUnramified := by
  algebraize [f, g, g.comp f]
  have : Algebra.FormallyEtale B C :=
    Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  have hsub : Subsingleton (C ⊗[B] Ω[B⁄A]) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A B C).subsingleton
  exact ⟨(Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right B C).mp hsub⟩

private theorem faithfullyFlat_stalkMap_of_flat {W X : Scheme} (g : W ⟶ X) [Flat g] (w : W) :
    (g.stalkMap w).hom.FaithfullyFlat := by
  have h := Flat.stalkMap g w
  algebraize [(g.stalkMap w).hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk (g w)) (W.presheaf.stalk w)) :=
    inferInstanceAs <| IsLocalHom (g.stalkMap w).hom
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- A morphism locally of finite presentation is étale if its
precomposition with a surjective étale morphism is étale. -/
theorem etale_of_comp_of_etale_of_surjective {W X Y : Scheme} (g : W ⟶ X) (f : X ⟶ Y)
    [Etale g] [Surjective g] [Etale (g ≫ f)] [LocallyOfFinitePresentation f] :
    Etale f := by
  have : Flat g := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1
  have : Flat (g ≫ f) := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale (g ≫ f)›).1
  have hstalk (x : X) : (f.stalkMap x).hom.Flat ∧ (f.stalkMap x).hom.FormallyUnramified := by
    obtain ⟨w, rfl⟩ := g.surjective x
    have hflat := Flat.stalkMap (g ≫ f) w
    have hunram := FormallyUnramified.stalkMap (g ≫ f) w
    rw [Scheme.Hom.stalkMap_comp] at hflat hunram
    have hg := faithfullyFlat_stalkMap_of_flat g w
    have hs : (g.stalkMap w).hom.FormallySmooth :=
      Scheme.Hom.mem_smoothLocus.mp (g.smoothLocus_eq_top.ge (Set.mem_univ w))
    exact ⟨ringHom_flat_of_comp_faithfullyFlat hg hflat,
      ringHom_formallyUnramified_of_comp_faithfullyFlat hg hs
        (FormallyUnramified.stalkMap g w) hunram⟩
  have : Flat f := Flat.of_stalkMap f fun x => (hstalk x).1
  have : FormallyUnramified f := HasRingHomProperty.of_stalkMap
    RingHom.FormallyUnramified.ofLocalizationPrime fun x => (hstalk x).2
  exact Etale.of_formallyUnramified_of_flat f

/-- For separated morphisms locally of finite type, finiteness descends
through a surjective source map. -/
theorem finite_of_comp_surjective {W X Y : Scheme} (g : W ⟶ X) (f : X ⟶ Y)
    [Surjective g] [IsFinite (g ≫ f)] [IsSeparated f] [LocallyOfFiniteType f] : IsFinite f := by
  have : UniversallyClosed f := UniversallyClosed.of_comp_surjective g f
  have : IsProper f := {}
  have : LocallyQuasiFinite f := by
    apply LocallyQuasiFinite.of_finite_preimage_singleton
    intro y
    refine (((g ≫ f).finite_preimage_singleton y).image g).subset ?_
    intro x hx
    obtain ⟨w, rfl⟩ := g.surjective x
    exact ⟨w, hx, rfl⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

/-- If successive pairs in a chain are finite étale, the first
morphism is finite étale provided the middle map is locally of finite type. -/
theorem finiteEtale_of_consecutive_composites {V W X Y : Scheme}
    (f : V ⟶ W) (g : W ⟶ X) (h : X ⟶ Y) [LocallyOfFiniteType g]
    [IsFinite (f ≫ g)] [Etale (f ≫ g)] [IsFinite (g ≫ h)] [Etale (g ≫ h)] :
    IsFinite f ∧ Etale f := by
  have : IsSeparated g := IsSeparated.of_comp g h
  have : FormallyUnramified g := FormallyUnramified.of_comp g h
  exact ⟨IsFinite.of_comp f g, Etale.of_comp f g⟩

/-- Two finite étale composites with a reverse map give finite étaleness
of a translation after descending along the source level map. -/
theorem finiteEtale_of_level_change {A B A' B' : Scheme}
    (f : A ⟶ B) (f' : A' ⟶ B') (r : B' ⟶ A) (j : A' ⟶ A) (k : B' ⟶ B)
    (h : j ≫ f = f' ≫ k)
    [Etale j] [Surjective j] [IsFinite k] [Etale k] [LocallyOfFiniteType r]
    [IsFinite (f' ≫ r)] [Etale (f' ≫ r)] [IsFinite (r ≫ f)] [Etale (r ≫ f)]
    [IsSeparated f] [LocallyOfFinitePresentation f] :
    IsFinite f ∧ Etale f := by
  obtain ⟨hf, he⟩ := finiteEtale_of_consecutive_composites f' r f
  letI : IsFinite f' := hf
  letI : Etale f' := he
  haveI : IsFinite (j ≫ f) := h.symm ▸ inferInstanceAs (IsFinite (f' ≫ k))
  haveI : Etale (j ≫ f) := h.symm ▸ inferInstanceAs (Etale (f' ≫ k))
  exact ⟨finite_of_comp_surjective j f, etale_of_comp_of_etale_of_surjective j f⟩

end GlobalTheory
