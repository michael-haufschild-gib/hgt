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

/-- The degree-two Hasse principle in difference form: two global Milnor classes have identical
residue profiles exactly when their difference comes from the constant field. -/
theorem rationalFunctionMilnorKTwo_allResidue_eq_iff_sub_eq_constant
    (x y : MilnorKDeg (RatFunc F) 2) :
    milnorPolynomialAllResidue (F := F) 1 x =
      milnorPolynomialAllResidue (F := F) 1 y ↔
      ∃ c : MilnorKDeg F 2,
        x - y = milnorKDegMap (ratFuncConstHom (F := F)) 2 c := by
  have hExact := (rationalFunctionMilnorKTwo_projectiveLine_exact (F := F)).2.1
  constructor
  · intro hxy
    have hzero : milnorPolynomialAllResidue (F := F) 1 (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨c, hc⟩ := hExact _ |>.mp hzero
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    have hzero : milnorPolynomialAllResidue (F := F) 1 (x - y) = 0 :=
      hExact _ |>.mpr ⟨c, hc.symm⟩
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero

/-- A global degree-two Milnor class is locally trivial at every projective-line place exactly
when it is a constant-field class. -/
theorem rationalFunctionMilnorKTwo_allResidue_eq_zero_iff_constant
    (x : MilnorKDeg (RatFunc F) 2) :
    milnorPolynomialAllResidue (F := F) 1 x = 0 ↔
      ∃ c : MilnorKDeg F 2, x = milnorKDegMap (ratFuncConstHom (F := F)) 2 c := by
  have hExact := (rationalFunctionMilnorKTwo_projectiveLine_exact (F := F)).2.1
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := hExact _ |>.mp hx
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    exact hExact _ |>.mpr ⟨c, rfl⟩

/-- Equality of projective-line degree-two residue profiles is equality modulo a constant
Milnor class. -/
theorem rationalFunctionMilnorKTwo_allResidue_eq_iff_eq_constant_add
    (x y : MilnorKDeg (RatFunc F) 2) :
    milnorPolynomialAllResidue (F := F) 1 x =
      milnorPolynomialAllResidue (F := F) 1 y ↔
      ∃ c : MilnorKDeg F 2,
        x = milnorKDegMap (ratFuncConstHom (F := F)) 2 c + y := by
  rw [rationalFunctionMilnorKTwo_allResidue_eq_iff_sub_eq_constant]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, sub_eq_iff_eq_add.mp hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, sub_eq_iff_eq_add.mpr hc⟩

end

end GaloisForLFunctions.HTGeometry.ABHN
