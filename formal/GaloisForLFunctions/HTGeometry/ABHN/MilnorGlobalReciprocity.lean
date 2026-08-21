/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.MilnorPolynomialGlobalReciprocityQuotient
import GaloisForLFunctions.HTGeometry.MilnorPolynomialGlobalProfileEquiv

/-!
# Projective-line global reciprocity in the ABHN interface

For `F(t)`, all finite Milnor residues and the residue at infinity satisfy one global norm-sum
relation.  Conversely, every compatible family occurs, uniquely modulo constants.  Degree one is
the principal-divisor layer; degree two is the Milnor-symbol layer adjacent to Brauer theory.

No identification of Milnor `K₂` with a Brauer group is assumed here.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

variable {F : Type*} [Field F]

/-- Degree-one projective-line local-global equivalence: units modulo constants are the compatible
finite-and-infinite residue profiles. -/
noncomputable def rationalFunctionMilnorKOneGlobalResidueQuotientEquiv :
    MilnorKDeg (RatFunc F) 1 ⧸
        AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) 1) ≃+
      (milnorPolynomialGlobalSum (F := F) 0).ker :=
  milnorPolynomialGlobalResidueQuotientEquiv (F := F) 0

/-- Degree-two projective-line local-global equivalence: symbols modulo constants are the
compatible finite-and-infinite residue profiles. -/
noncomputable def rationalFunctionMilnorKTwoGlobalResidueQuotientEquiv :
    MilnorKDeg (RatFunc F) 2 ⧸
        AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) 2) ≃+
      (milnorPolynomialGlobalSum (F := F) 1).ker :=
  milnorPolynomialGlobalResidueQuotientEquiv (F := F) 1

/-- Degree-one finite residue profiles determine the unique infinity residue compatible with
global reciprocity. -/
noncomputable def rationalFunctionMilnorKOneFiniteGlobalProfileEquiv :
    MilnorPolynomialTotalResidueTarget (F := F) 0 ≃+
      (milnorPolynomialGlobalSum (F := F) 0).ker :=
  milnorPolynomialFiniteGlobalProfileEquiv (F := F) 0

/-- Degree-two finite residue profiles determine the unique infinity residue compatible with
global reciprocity.  This is the `K₂` profile underlying the local-invariant shape of ABHN. -/
noncomputable def rationalFunctionMilnorKTwoFiniteGlobalProfileEquiv :
    MilnorPolynomialTotalResidueTarget (F := F) 1 ≃+
      (milnorPolynomialGlobalSum (F := F) 1).ker :=
  milnorPolynomialFiniteGlobalProfileEquiv (F := F) 1

/-- The degree-two profile equivalence leaves finite data unchanged and supplies exactly the
negative total norm as its forced infinite component. -/
theorem rationalFunctionMilnorKTwoFiniteGlobalProfileEquiv_apply
    (z : MilnorPolynomialTotalResidueTarget (F := F) 1) :
    (rationalFunctionMilnorKTwoFiniteGlobalProfileEquiv (F := F) z).1 =
      (z, -milnorPolynomialTotalNorm (F := F) 1 z) :=
  milnorPolynomialFiniteGlobalProfileEquiv_apply (F := F) 1 z

/-- The degree-two projective-line Hasse sequence: global symbol classes map to all local residue
data, whose sole compatibility condition is vanishing of the global norm-sum. -/
theorem rationalFunctionMilnorKTwo_projectiveLine_exact :
    Function.Injective (milnorKDegMap (ratFuncConstHom (F := F)) 2) ∧
      Function.Exact (milnorKDegMap (ratFuncConstHom (F := F)) 2)
        (milnorPolynomialAllResidue (F := F) 1) ∧
      Function.Exact (milnorPolynomialAllResidue (F := F) 1)
        (milnorPolynomialGlobalSum (F := F) 1) ∧
      Function.Surjective (milnorPolynomialGlobalSum (F := F) 1) :=
  milnorPolynomialProjectiveLine_exact (F := F) 1

end

end GaloisForLFunctions.HTGeometry.ABHN
