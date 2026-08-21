import GaloisForLFunctions.HTGeometry.MilnorPolynomialTotalResidue

/-!
# Quotient form of finite-place Milnor residue realization

The finite-place residue map for `F(t)` is surjective, and its kernel consists exactly of constant
classes.  Consequently, arbitrary finite-support finite-place residue data are represented by a
unique Milnor class modulo constants.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {F : Type*} [Field F]

local instance : DecidableEq (MonicIrred F) := Classical.decEq _

/-- **Finite-place local-to-global quotient.** Milnor classes of `F(t)` modulo constants are
equivalent to arbitrary finite-support residue data at finite polynomial places. -/
noncomputable def milnorPolynomialFiniteResidueQuotientEquiv (n : ℕ) :
    MilnorKDeg (RatFunc F) n.succ ⧸
        AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) n.succ) ≃+
      MilnorPolynomialTotalResidueTarget (F := F) n :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (milnorPolynomialTotalResidue_ker_eq_constRange (F := F) n).symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (milnorPolynomialTotalResidue (F := F) n)
        (milnorPolynomialTotalResidue_surjective (F := F) n))

/-- The finite-place quotient equivalence sends a global class to its total finite residue. -/
theorem milnorPolynomialFiniteResidueQuotientEquiv_mk (n : ℕ)
    (y : MilnorKDeg (RatFunc F) n.succ) :
    milnorPolynomialFiniteResidueQuotientEquiv (F := F) n (QuotientAddGroup.mk y) =
      milnorPolynomialTotalResidue (F := F) n y := by
  simp [milnorPolynomialFiniteResidueQuotientEquiv]
  change QuotientAddGroup.kerLift (milnorPolynomialTotalResidue (F := F) n)
    (QuotientAddGroup.mk y) = milnorPolynomialTotalResidue (F := F) n y
  rfl

end

end GaloisForLFunctions.HTGeometry
