import GaloisForLFunctions.HTGeometry.StokesClosedSupportSheaf
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Open extension by zero for ordinary additive sheaves

For an open embedding `j`, construct `j_!` by sheafifying the presheaf left Kan extension along
the image-of-open functor.  The construction is proved left adjoint to both naive open restriction
and the standard sheaf pullback.  Combining `j_!` with closed direct image gives ordinary sheaves
on locally closed supports.

This file is intentionally universe-0 for the same `AddCommGrpCat` sheafification reason as
`StokesClosedSupportSheaf`.  It contains no derived, proper-support, ind-sheaf, or enhanced
construction.
-/

namespace GaloisForLFunctions.IrregularStokes.OpenExtensionByZero

open CategoryTheory TopologicalSpace TopCat Topology
open GaloisForLFunctions.IrregularStokes.ClosedSupportSheaf
open GaloisForLFunctions.IrregularStokes.EnhancedEpigraph

/-- Presheaf left Kan extension along the image-of-open functor of an open embedding. -/
noncomputable def openExtensionPresheaf {X Y : TopCat} {j : X ⟶ Y}
    (hj : IsOpenEmbedding j) :
    TopCat.Presheaf AddCommGrpCat X ⥤ TopCat.Presheaf AddCommGrpCat Y :=
  hj.functor.op.lan

/-- Underlying presheaf restriction along an open embedding. -/
def openRestrictionPresheaf {X Y : TopCat} {j : X ⟶ Y}
    (hj : IsOpenEmbedding j) :
    TopCat.Presheaf AddCommGrpCat Y ⥤ TopCat.Presheaf AddCommGrpCat X :=
  (Functor.whiskeringLeft (Opens X)ᵒᵖ (Opens Y)ᵒᵖ AddCommGrpCat).obj hj.functor.op

/-- Ordinary additive-sheaf extension by zero along an open embedding. -/
noncomputable def openExtensionByZero {X Y : TopCat} {j : X ⟶ Y}
    (hj : IsOpenEmbedding j) :
    TopCat.Sheaf AddCommGrpCat X ⥤ TopCat.Sheaf AddCommGrpCat Y :=
  ((TopCat.Sheaf.forget AddCommGrpCat X).comp (openExtensionPresheaf hj)).comp
    (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat)

/-- Presheaf Kan extension followed by sheafification is left adjoint to underlying open
restriction. -/
noncomputable def extensionAdjunctionUpstairs {X Y : TopCat} {j : X ⟶ Y}
    (hj : IsOpenEmbedding j) :
    (openExtensionPresheaf hj).comp
        (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat) ⊣
      (TopCat.Sheaf.forget AddCommGrpCat Y).comp (openRestrictionPresheaf hj) :=
  (hj.functor.op.lanAdjunction AddCommGrpCat).comp
    (CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat)

/-- `j_!` is left adjoint to naive restriction along an open embedding. -/
noncomputable def openExtensionByZeroAdjunction {X Y : TopCat} {j : X ⟶ Y}
    (hj : IsOpenEmbedding j) :
    openExtensionByZero hj ⊣ hj.sheafPullback AddCommGrpCat :=
  (extensionAdjunctionUpstairs hj).restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful (TopCat.Sheaf.forget AddCommGrpCat X))
    (Functor.FullyFaithful.id (TopCat.Sheaf AddCommGrpCat Y))
    (Iso.refl _)
    (Iso.refl _)

/-- `j_!` is left adjoint to mathlib's standard sheaf pullback `j^*`. -/
noncomputable def openExtensionByZeroPullbackAdjunction {X Y : TopCat} {j : X ⟶ Y}
    (hj : IsOpenEmbedding j) :
    openExtensionByZero hj ⊣ TopCat.Sheaf.pullback AddCommGrpCat j :=
  (openExtensionByZeroAdjunction hj).ofNatIsoRight
    (hj.sheafPullbackIso AddCommGrpCat).symm

/-- Inclusion from a relatively open subtype into its ambient subtype is an open embedding. -/
theorem nestedSubtypeInclusion_isOpenEmbedding {X : Type} [TopologicalSpace X]
    {S T : Set X} (hST : S ⊆ T)
    (hS : IsOpen ((Subtype.val : T → X) ⁻¹' S)) :
    IsOpenEmbedding (nestedSubtypeInclusion hST).hom := by
  let i : S → T := fun p => ⟨p.1, hST p.2⟩
  refine ⟨?_, ?_⟩
  · apply IsEmbedding.subtypeVal.of_comp_iff.mp
    change IsEmbedding (Subtype.val : S → X)
    exact IsEmbedding.subtypeVal
  · have hrange : Set.range i = (Subtype.val : T → X) ⁻¹' S := by
      ext q
      constructor
      · rintro ⟨p, rfl⟩
        exact p.2
      · intro hq
        exact ⟨⟨q.1, hq⟩, Subtype.ext rfl⟩
    change IsOpen (Set.range i)
    rw [hrange]
    exact hS

/-- Constant ordinary sheaf on a locally closed support, factored as open extension inside a
closed subspace followed by closed direct image. -/
noncomputable def constantLocallyClosedSupportSheaf {X : Type} [TopologicalSpace X]
    (S C : Set X) (_hC : IsClosed C) (hSC : S ⊆ C)
    (hS : IsOpen ((Subtype.val : C → X) ⁻¹' S)) (A : AddCommGrpCat) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of X) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat (subtypeInclusion C)).obj
    ((openExtensionByZero (nestedSubtypeInclusion_isOpenEmbedding hSC hS)).obj
      (constantAddCommGrpSheaf (TopCat.of S) A))

/-- Ordinary constant sheaf on an open-domain continuous exponential epigraph, using its explicit
open-inside-closed factorization. -/
noncomputable def exponentialEpigraphOnSheaf {X : Type} [TopologicalSpace X]
    (U : Set X) (hU : IsOpen U) (φ : X → ℝ) (hφ : Continuous φ)
    (A : AddCommGrpCat) : TopCat.Sheaf AddCommGrpCat (TopCat.of (X × ℝ)) := by
  let C := exponentialEpigraph φ
  let S := exponentialEpigraphOn U φ
  have hC : IsClosed C := isClosed_exponentialEpigraph hφ
  have hSC : S ⊆ C := by
    intro p hp
    exact hp.2
  have hS : IsOpen ((Subtype.val : C → X × ℝ) ⁻¹' S) := by
    change IsOpen ((Subtype.val : C → X × ℝ) ⁻¹'
      ((Prod.fst ⁻¹' U) ∩ C))
    rw [Set.preimage_inter]
    have hpre : IsOpen ((Subtype.val : C → X × ℝ) ⁻¹' (Prod.fst ⁻¹' U)) :=
      (hU.preimage continuous_fst).preimage continuous_subtype_val
    have hcarrier : (Subtype.val : C → X × ℝ) ⁻¹' C = Set.univ := by
      ext p
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      exact p.2
    rw [hcarrier, Set.inter_univ]
    exact hpre
  exact constantLocallyClosedSupportSheaf S C hC hSC hS A

end GaloisForLFunctions.IrregularStokes.OpenExtensionByZero
