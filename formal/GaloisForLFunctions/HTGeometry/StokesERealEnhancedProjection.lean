import GaloisForLFunctions.HTGeometry.StokesProperPullbackCompactSupport
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Extended-real enhanced projection

The compact extended real line supplies the proper ambient projection needed by enhanced
ind-sheaves. Its properness restricts ordinary sheaf inverse image to compactly supported sheaves.

This is the compact ambient space only; the bordered pair `(Real, EReal)` remains separate.
-/

namespace GaloisForLFunctions.IrregularStokes.CompactIndSheaf

open CategoryTheory TopCat

/-- Compact ambient space for the enhanced real variable. -/
noncomputable abbrev EnhancedCompactification (X : TopCat.{0}) : TopCat.{0} :=
  TopCat.of (X × EReal)

/-- Projection from the compactified enhanced real direction. -/
noncomputable def enhancedProjection (X : TopCat.{0}) : EnhancedCompactification X ⟶ X :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- Compactness of `EReal` makes the enhanced projection proper. -/
theorem enhancedProjection_isProper (X : TopCat.{0}) :
    IsProperMap (enhancedProjection X) := by
  change IsProperMap (Prod.fst : X × EReal → X)
  exact isProperMap_fst_of_compactSpace

/-- Compact-support pullback along the enhanced projection. -/
noncomputable def enhancedProjectionPullback (X : TopCat.{0}) :
    CompactlySupportedSheaf X ⥤ CompactlySupportedSheaf (EnhancedCompactification X) :=
  properPullback (enhancedProjection X) (enhancedProjection_isProper X)

end GaloisForLFunctions.IrregularStokes.CompactIndSheaf
