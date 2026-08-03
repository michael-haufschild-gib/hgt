import GaloisForLFunctions.RHTower.DeningerTreeMatrix
import GaloisForLFunctions.RHTower.DeningerHomologyAdditive

/-!
# The boundary is injective on homology

The three entries of the boundary matrix pass through the homology functor unchanged, since the
functor is additive and takes biproducts to biproducts.  So the sheared triangular criterion applies
and the boundary of the tree is injective on homology, as soon as the coset projection to the first
factor is.

* `deningerTreeBoundary_mono_of_projMono` : the criterion for the tree.
* `deningerAmalgam_isZero_of_mono` : vanishing for an amalgam from an injective comparison map.
-/

namespace RHTower

open Monoid Monoid.PushoutI CategoryTheory CategoryTheory.Limits

universe u

variable {G : ULift.{u} Bool → Type u} {H : Type u} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} (k : Type u) [CommRing k]

theorem deningerMono_neg {C : Type*} [Category C] [Preadditive C] {X Y : C} (f : X ⟶ Y)
    [Mono f] : Mono (-f) := by
  have hiso : IsIso (-𝟙 Y) := ⟨-𝟙 Y, by simp, by simp⟩
  have hf : -f = f ≫ (-𝟙 Y) := by simp
  rw [hf]
  exact mono_comp _ _

/-- **The boundary of the tree is injective on homology** once the coset projection to the first
factor is. -/
theorem deningerTreeBoundary_mono_of_projMono (n : ℕ)
    (hproj : Mono ((groupHomology.functor k (PushoutI φ) n).map
      (deningerCosetProj k (deningerBaseRange_le φ (ULift.up false))))) :
    Mono ((groupHomology.functor k (PushoutI φ) n).map (deningerTreeMatrix (φ := φ) k)) := by
  set F := groupHomology.functor k (PushoutI φ) n with hF
  set eE := deningerHomologyBiprodIso
    (Rep.ofMulAction k (PushoutI φ) (PushoutI φ ⧸ (PushoutI.base φ).range))
    (Rep.ofMulAction k (PushoutI φ) (PushoutI φ ⧸ (PushoutI.base φ).range)) n with heE
  set eV := (deningerHomologyBiprodIso
      (Rep.ofMulAction k (PushoutI φ) (PushoutI φ ⧸ (PushoutI.base φ).range))
      (Rep.ofMulAction k (PushoutI φ)
          (PushoutI φ ⧸ (PushoutI.of (φ := φ) (ULift.up true)).range) ⊞
        Rep.ofMulAction k (PushoutI φ)
          (PushoutI φ ⧸ (PushoutI.of (φ := φ) (ULift.up false)).range)) n) ≪≫
    biprod.mapIso (Iso.refl _) (deningerHomologyBiprodIso _ _ n) with heV
  have hinl : (biprod.inl : F.obj _ ⟶ _) ≫ eE.inv = F.map biprod.inl := biprod.inl_desc _ _
  have hinr : (biprod.inr : F.obj _ ⟶ _) ≫ eE.inv = F.map biprod.inr := biprod.inr_desc _ _
  have hbfst : ∀ A B : Rep k (PushoutI φ),
      (deningerHomologyBiprodIso A B n).hom ≫ biprod.fst = F.map biprod.fst :=
    fun _ _ => biprod.lift_fst _ _
  have hbsnd : ∀ A B : Rep k (PushoutI φ),
      (deningerHomologyBiprodIso A B n).hom ≫ biprod.snd = F.map biprod.snd :=
    fun _ _ => biprod.lift_snd _ _
  have hfst : eV.hom ≫ biprod.fst = F.map biprod.fst := by
    rw [heV, Iso.trans_hom, Category.assoc, biprod.mapIso_hom, biprod.map_fst, Iso.refl_hom,
      Category.comp_id, hbfst]
  have hsndsnd : eV.hom ≫ biprod.snd ≫ biprod.snd = F.map (biprod.snd ≫ biprod.snd) := by
    rw [heV, Iso.trans_hom, Category.assoc, biprod.mapIso_hom, ← Category.assoc (biprod.map _ _),
      biprod.map_snd, Category.assoc, hbsnd, ← Category.assoc, hbsnd, ← F.map_comp]
  set Ψ := eE.inv ≫ F.map (deningerTreeMatrix (φ := φ) k) ≫ eV.hom with hΨ
  have hΨmono : Mono Ψ := by
    refine deningerMono_of_shear_triangular Ψ ?_ ?_ ?_
    · have hcol : biprod.inl ≫ Ψ ≫ biprod.fst = -𝟙 _ := by
        rw [hΨ]
        simp only [Category.assoc]
        rw [← Category.assoc biprod.inl, hinl]
        simp only [hfst]
        simp only [← F.map_comp]
        rw [deningerTreeMatrix_inl_fst, Functor.map_neg, CategoryTheory.Functor.map_id]
      rw [hcol]
      exact deningerMono_neg _
    · have hcol : (biprod.inr - biprod.inl) ≫ Ψ ≫ biprod.snd ≫ biprod.snd =
          F.map (deningerCosetProj k (deningerBaseRange_le φ (ULift.up false))) := by
        rw [hΨ]
        simp only [Preadditive.sub_comp, Category.assoc]
        rw [← Category.assoc biprod.inr, hinr, ← Category.assoc biprod.inl, hinl]
        simp only [hsndsnd]
        simp only [← F.map_comp]
        rw [← Functor.map_sub, ← Preadditive.sub_comp, deningerTreeMatrix_sub_snd_snd]
      haveI := hproj
      have hmono2 : Mono ((biprod.inr - biprod.inl) ≫ Ψ ≫ biprod.snd ≫ biprod.snd) := by
        rw [hcol]
        exact hproj
      haveI : Mono (((biprod.inr - biprod.inl) ≫ Ψ ≫ biprod.snd) ≫ biprod.snd) := by
        rw [Category.assoc]
        exact hmono2
      exact mono_of_mono _ biprod.snd
    · rw [hΨ]
      simp only [Preadditive.sub_comp, Category.assoc]
      rw [← Category.assoc biprod.inr, hinr, ← Category.assoc biprod.inl, hinl]
      simp only [hfst]
      simp only [← F.map_comp]
      rw [← Functor.map_sub, ← Preadditive.sub_comp, deningerTreeMatrix_sub_fst,
        Functor.map_zero]
  have hfac : F.map (deningerTreeMatrix (φ := φ) k) = eE.hom ≫ Ψ ≫ eV.inv := by
    rw [hΨ]
    simp only [← Category.assoc]
    rw [Iso.hom_inv_id, Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hfac]
  haveI := hΨmono
  exact mono_comp _ _

/-- The boundary itself is injective on homology. -/
theorem deningerTreeBoundaryHom_mono (n : ℕ)
    (hproj : Mono ((groupHomology.functor k (PushoutI φ) n).map
      (deningerCosetProj k (deningerBaseRange_le φ (ULift.up false))))) :
    Mono ((groupHomology.functor k (PushoutI φ) n).map (deningerTreeBoundaryHom (φ := φ) k)) := by
  set F := groupHomology.functor k (PushoutI φ) n with hF
  haveI : IsIso (F.map (deningerTreeEdgeRepIso (φ := φ) k).inv) := inferInstance
  haveI : IsIso (F.map (deningerTreeVertexRepIso (φ := φ) k).hom) := inferInstance
  haveI := deningerTreeBoundary_mono_of_projMono k n hproj
  have hb : F.map (deningerTreeBoundaryHom (φ := φ) k) =
      inv (F.map (deningerTreeEdgeRepIso (φ := φ) k).inv) ≫
        F.map (deningerTreeMatrix (φ := φ) k) ≫
          inv (F.map (deningerTreeVertexRepIso (φ := φ) k).hom) := by
    rw [deningerTreeMatrix, F.map_comp, F.map_comp]
    simp
  rw [hb]
  exact mono_comp _ _

/-- **Vanishing for an amalgam from an injective comparison map.**  In a degree where the vertex
homology vanishes and the boundary is injective one degree down, the homology of the amalgam
vanishes. -/
theorem deningerAmalgam_isZero_of_mono (hφ : ∀ i, Function.Injective (φ i)) (i j : ℕ)
    (hij : j + 1 = i)
    (hV : IsZero (groupHomology (deningerTreeVertexRep φ k) i))
    (hproj : Mono ((groupHomology.functor k (PushoutI φ) j).map
      (deningerCosetProj k (deningerBaseRange_le φ (ULift.up false))))) :
    IsZero (groupHomology (Rep.trivial k (PushoutI φ) k) i) :=
  deningerGroupHomology_isZero_X₃_of_mono (deningerTreeShortComplex_shortExact k hφ) i j hij hV
    (deningerTreeBoundaryHom_mono k j hproj)

end RHTower
