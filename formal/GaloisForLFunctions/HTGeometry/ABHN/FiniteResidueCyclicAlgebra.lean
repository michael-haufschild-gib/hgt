/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.LocalFrobenius
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldCyclicGaloisAlgebra
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldQuadraticCyclicBrauer
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousQuadraticGaloisH2Brauer
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldCubicCyclicBrauer
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousCubicGaloisH2Brauer

/-!
# Cyclic algebras at finite residue extensions

At a finite residue extension, every cyclic degree-two parameter is a norm.  The corresponding
raw cyclic quotient is therefore a central simple algebra representing the split Brauer class.
This is the algebra-level residue component of local reciprocity; it deliberately does not lift
the residue algebra through a valuation ring to a local-field Brauer class.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

attribute [local instance] Ideal.Quotient.field

variable {A B G : Type}
  [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G]
  (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
  [Finite (B ⧸ Q)]

/-- Every degree-two cyclic parameter at a finite residue extension vanishes in cohomology. -/
theorem residue_cyclicGaloisH2BaseProjection_eq_zero (a : Additive (A ⧸ P)ˣ) :
    cyclicGaloisH2BaseProjection (A ⧸ P) (B ⧸ Q) a = 0 :=
  finiteField_cyclicGaloisH2BaseProjection_eq_zero (A ⧸ P) (B ⧸ Q) a

/-- Every degree-two cyclic parameter at a finite residue extension is an actual norm. -/
theorem residue_cyclicGaloisH2BaseParameter_exists_norm (a : Additive (A ⧸ P)ˣ) :
    ∃ c : (B ⧸ Q)ˣ, (a.toMul : A ⧸ P) = Algebra.norm (A ⧸ P) (c : B ⧸ Q) :=
  finiteField_cyclicGaloisH2BaseParameter_exists_norm (A ⧸ P) (B ⧸ Q) a

/-- The raw cyclic algebra attached to a finite residue-field parameter is central simple. -/
noncomputable def residueCyclicGaloisAlgebraCSA (a : Additive (A ⧸ P)ˣ) : CSA (A ⧸ P) :=
  finiteField_cyclicGaloisAlgebraCSA (A ⧸ P) (B ⧸ Q) a

/-- Every residue cyclic algebra at a finite residue extension has split Brauer class. -/
theorem residue_brauerClass_cyclicGaloisAlgebraCSA_eq_split (a : Additive (A ⧸ P)ˣ) :
    brauerClass (residueCyclicGaloisAlgebraCSA P Q a) = brauerSplitClass (A ⧸ P) :=
  finiteField_brauerClass_cyclicGaloisAlgebraCSA_eq_split (A ⧸ P) (B ⧸ Q) a

/-- Every quadratic cyclic degree-two class at a finite residue extension selects the split
Brauer class. -/
theorem residue_quadraticCyclicGaloisH2BrauerMap_eq_split
    (hdeg : Module.finrank (A ⧸ P) (B ⧸ Q) = 2)
    (z : cyclicGaloisH2 (A ⧸ P) (B ⧸ Q)) :
    quadraticCyclicGaloisH2BrauerMap (A ⧸ P) (B ⧸ Q) hdeg z = brauerSplitClass (A ⧸ P) :=
  finiteField_quadraticCyclicGaloisH2BrauerMap_eq_split (A ⧸ P) (B ⧸ Q) hdeg z

/-- Every continuous quadratic cyclic degree-two class at a finite residue extension selects the
split residue Brauer class.  This applies the finite continuous-to-ordinary cohomology comparison
before the existing cyclic-algebra construction. -/
theorem residue_finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_split
    (hdeg : Module.finrank (A ⧸ P) (B ⧸ Q) = 2)
    (z : continuousGaloisUnitCohomology 2 (A ⧸ P) (B ⧸ Q)) :
    finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap (A ⧸ P) (B ⧸ Q) hdeg z =
      brauerSplitClass (A ⧸ P) :=
  finiteField_finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_split
    (A ⧸ P) (B ⧸ Q) hdeg z

/-- Every cubic cyclic degree-two class at a finite residue extension selects the split residue
Brauer class. -/
theorem residue_cubicCyclicGaloisH2BrauerMap_eq_split
    (hdeg : Module.finrank (A ⧸ P) (B ⧸ Q) = 3)
    (z : cyclicGaloisH2 (A ⧸ P) (B ⧸ Q)) :
    cubicCyclicGaloisH2BrauerMap (A ⧸ P) (B ⧸ Q) hdeg z = brauerSplitClass (A ⧸ P) :=
  finiteField_cubicCyclicGaloisH2BrauerMap_eq_split (A ⧸ P) (B ⧸ Q) hdeg z

/-- Every continuous cubic cyclic degree-two class at a finite residue extension selects the
split residue Brauer class. -/
theorem residue_finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap_eq_split
    (hdeg : Module.finrank (A ⧸ P) (B ⧸ Q) = 3)
    (z : continuousGaloisUnitCohomology 2 (A ⧸ P) (B ⧸ Q)) :
    finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap (A ⧸ P) (B ⧸ Q) hdeg z =
      brauerSplitClass (A ⧸ P) :=
  finiteField_finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap_eq_split
    (A ⧸ P) (B ⧸ Q) hdeg z

end GaloisForLFunctions.HTGeometry.ABHN
