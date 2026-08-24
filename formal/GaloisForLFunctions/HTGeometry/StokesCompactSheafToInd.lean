import GaloisForLFunctions.HTGeometry.StokesCompactIndSheaf

/-!
# Compactly supported sheaves embed into ind-sheaves

The universe-small equivalence followed by ind-Yoneda gives the canonical fully faithful exact
embedding of compactly supported integer-module sheaves into integer-coefficient ind-sheaves.

This does not yet extend the embedding to all ordinary sheaves; that step needs a locally compact
exhaustion by compactly supported pieces.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.IrregularStokes.CompactIndEmbedding

open CompactIndSheaf

/-- Canonical embedding of compactly supported sheaves into ind-sheaves. -/
noncomputable def compactSheafToIndSheaf (Y : TopCat.{0}) :
    CompactlySupportedSheaf Y ⥤ IndSheaf Y :=
  (AsSmall.equiv : CompactlySupportedSheaf Y ≌
    SmallCompactlySupportedSheaf Y).functor ⋙ Ind.yoneda

noncomputable instance compactSheafToIndSheaf_full (Y : TopCat.{0}) :
    (compactSheafToIndSheaf Y).Full := by
  dsimp [compactSheafToIndSheaf]
  exact (AsSmall.equiv.fullyFaithfulFunctor.comp Ind.yoneda.fullyFaithful).full

noncomputable instance compactSheafToIndSheaf_faithful (Y : TopCat.{0}) :
    (compactSheafToIndSheaf Y).Faithful := by
  dsimp [compactSheafToIndSheaf]
  exact (AsSmall.equiv.fullyFaithfulFunctor.comp Ind.yoneda.fullyFaithful).faithful

noncomputable instance compactSheafToIndSheaf_preservesFiniteLimits
    (Y : TopCat.{0}) :
    PreservesFiniteLimits (compactSheafToIndSheaf Y) := by
  dsimp [compactSheafToIndSheaf]
  infer_instance

noncomputable instance compactSheafToIndSheaf_preservesFiniteColimits
    (Y : TopCat.{0}) :
    PreservesFiniteColimits (compactSheafToIndSheaf Y) := by
  dsimp [compactSheafToIndSheaf]
  infer_instance

noncomputable instance compactSheafToIndSheaf_additive (Y : TopCat.{0}) :
    (compactSheafToIndSheaf Y).Additive := by
  let F := compactSheafToIndSheaf Y
  letI : F.PreservesZeroMorphisms := inferInstance
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  exact Functor.additive_of_preservesBinaryBiproducts F

noncomputable instance compactSheafToIndSheaf_preservesHomology
    (Y : TopCat.{0}) :
    (compactSheafToIndSheaf Y).PreservesHomology := by
  exact ((Functor.exact_tfae (compactSheafToIndSheaf Y)).out 3 2 rfl rfl).mp
    ⟨inferInstance, inferInstance⟩

/-- The compact-sheaf embedding maps exact short complexes to exact short complexes. -/
theorem compactSheafToIndSheaf_map_exact (Y : TopCat.{0})
    (S : ShortComplex (CompactlySupportedSheaf Y)) (hS : S.Exact) :
    (S.map (compactSheafToIndSheaf Y)).Exact := by
  exact (((Functor.exact_tfae (compactSheafToIndSheaf Y)).out 2 1 rfl rfl).mp
    inferInstance) S hS

end GaloisForLFunctions.IrregularStokes.CompactIndEmbedding
