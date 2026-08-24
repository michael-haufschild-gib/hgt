import GaloisForLFunctions.HTGeometry.StokesERealEnhancedProjection

/-!
# Bordered extended real line

The physical enhanced variable is `Real`; `EReal` is its compact ambient space. This module records
the open bordered inclusion and its product with an arbitrary topological space, including the
exact two-point boundary.

No sheaf quotient or bordered-space six-operation formalism is asserted here.
-/

namespace GaloisForLFunctions.IrregularStokes.Bordered

open CategoryTheory TopCat Topology

/-- Topological bordered space: open interior inside an ambient space. -/
structure BorderedSpace where
  interior : TopCat.{0}
  ambient : TopCat.{0}
  inclusion : interior ⟶ ambient
  isOpenEmbedding_inclusion : IsOpenEmbedding inclusion

/-- Boundary of a bordered space inside its ambient space. -/
def BorderedSpace.boundary (B : BorderedSpace) : Set B.ambient :=
  (Set.range (ConcreteCategory.hom B.inclusion))ᶜ

/-- Finite-real inclusion into the compact extended real line. -/
noncomputable def realToEReal : TopCat.of ℝ ⟶ TopCat.of EReal :=
  TopCat.ofHom ⟨Real.toEReal, continuous_coe_real_ereal⟩

/-- Bordered extended real line `(Real, EReal)`. -/
noncomputable def extendedRealLine : BorderedSpace where
  interior := TopCat.of ℝ
  ambient := TopCat.of EReal
  inclusion := realToEReal
  isOpenEmbedding_inclusion := EReal.isOpenEmbedding_coe

/-- Boundary of the bordered extended real line consists exactly of the two infinities. -/
theorem extendedRealLine_boundary :
    extendedRealLine.boundary = ({⊥, ⊤} : Set EReal) := by
  change (Set.range Real.toEReal)ᶜ = ({⊥, ⊤} : Set EReal)
  rw [EReal.range_coe]
  simp

/-- Physical enhanced space before compactification. -/
noncomputable abbrev EnhancedInterior (X : TopCat.{0}) : TopCat.{0} :=
  TopCat.of (X × ℝ)

/-- Product inclusion `X × Real → X × EReal`. -/
noncomputable def enhancedFiniteInclusion (X : TopCat.{0}) :
    EnhancedInterior X ⟶ CompactIndSheaf.EnhancedCompactification X :=
  TopCat.ofHom ⟨Prod.map id Real.toEReal,
    (IsOpenEmbedding.id.prodMap EReal.isOpenEmbedding_coe).continuous⟩

/-- Bordered enhanced-variable space over `X`. -/
noncomputable def enhancedBorderedSpace (X : TopCat.{0}) : BorderedSpace where
  interior := EnhancedInterior X
  ambient := CompactIndSheaf.EnhancedCompactification X
  inclusion := enhancedFiniteInclusion X
  isOpenEmbedding_inclusion := IsOpenEmbedding.id.prodMap EReal.isOpenEmbedding_coe

/-- Product bordered boundary is exactly `X` times the two points at infinity. -/
theorem enhancedBorderedSpace_boundary (X : TopCat.{0}) :
    (enhancedBorderedSpace X).boundary =
      (Set.univ ×ˢ ({⊥, ⊤} : Set EReal) : Set (X × EReal)) := by
  change (Set.range (Prod.map id Real.toEReal))ᶜ =
    (Set.univ ×ˢ ({⊥, ⊤} : Set EReal) : Set (X × EReal))
  rw [Set.range_prodMap, EReal.range_coe]
  ext p
  by_cases hbot : p.2 = (⊥ : EReal)
  · simp [hbot]
  by_cases htop : p.2 = (⊤ : EReal)
  · simp [htop]
  · simp [hbot, htop]

end GaloisForLFunctions.IrregularStokes.Bordered
