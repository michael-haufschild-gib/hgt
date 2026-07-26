import GaloisForLFunctions.RHTower.DeningerArithmeticLocalQuotientOpenness
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Compact-open arithmetic cohomology is the full Xi-jet product

The descended all-jets observation is already a dense topological embedding.  The compact-open
entire source is complete and first countable; its additive quotient is therefore complete for
the quotient left uniformity.  A uniform embedding of that complete quotient into the Hausdorff
jet product has closed range.  Density then forces the range to be the whole product.

This proves the full compact-open reconstruction theorem without invoking an infinite
Mittag--Leffler interpolation axiom.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-- The descended all-jets observation is onto the full multiplicity-bounded Xi-jet product. -/
theorem deningerCompactOpenH1AllJets_surjective :
    Function.Surjective deningerCompactOpenH1AllJets := by
  letI :
      UniformSpace DeningerArithmeticCompactOpenH1 :=
    IsTopologicalAddGroup.leftUniformSpace
      DeningerArithmeticCompactOpenH1
  letI : CompleteSpace DeningerArithmeticCompactOpenH1 :=
    QuotientAddGroup.completeSpace_left
      DeningerCompactOpenEntire
      deningerCompactOpenXiRange.toAddSubgroup
  have huniform :
      IsUniformEmbedding
        (deningerCompactOpenH1AllJets :
          DeningerArithmeticCompactOpenH1 →
            DeningerArithmeticJetProduct) :=
    AddMonoidHom.isUniformEmbedding_of_isEmbedding
      isEmbedding_deningerCompactOpenH1AllJets
  have hclosed :
      IsClosed
        (Set.range
          (deningerCompactOpenH1AllJets :
            DeningerArithmeticCompactOpenH1 →
              DeningerArithmeticJetProduct)) :=
    huniform.isClosedEmbedding.isClosed_range
  apply Set.range_eq_univ.mp
  calc
    Set.range
          (deningerCompactOpenH1AllJets :
            DeningerArithmeticCompactOpenH1 →
              DeningerArithmeticJetProduct) =
        closure
          (Set.range
            (deningerCompactOpenH1AllJets :
              DeningerArithmeticCompactOpenH1 →
                DeningerArithmeticJetProduct)) :=
      hclosed.closure_eq.symm
    _ = Set.univ :=
      denseRange_deningerCompactOpenH1AllJets.closure_eq

/-- The all-jets observation is a homeomorphism onto the full jet product. -/
theorem isHomeomorph_deningerCompactOpenH1AllJets :
    IsHomeomorph
      (deningerCompactOpenH1AllJets :
        DeningerArithmeticCompactOpenH1 →
          DeningerArithmeticJetProduct) :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨isEmbedding_deningerCompactOpenH1AllJets,
      deningerCompactOpenH1AllJets_surjective⟩

/-- Canonical topological equivalence between compact-open middle cohomology and all local jets. -/
def deningerCompactOpenH1JetHomeomorph :
    DeningerArithmeticCompactOpenH1 ≃ₜ
      DeningerArithmeticJetProduct :=
  isHomeomorph_deningerCompactOpenH1AllJets.homeomorph
    deningerCompactOpenH1AllJets

@[simp]
theorem deningerCompactOpenH1JetHomeomorph_apply
    (x : DeningerArithmeticCompactOpenH1) :
    deningerCompactOpenH1JetHomeomorph x =
      deningerCompactOpenH1AllJets x :=
  rfl

end

end RHTower
