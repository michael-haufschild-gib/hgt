/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousQuadraticGaloisH2Brauer
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousCubicGaloisH2Brauer
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldQuadraticCyclicBrauer
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldCubicCyclicBrauer

/-!
# Additive finite-field cyclic cohomology-to-Brauer maps

Finite residue fields have trivial Brauer group.  Hence the selected quadratic and cubic cyclic
degree-two cohomology representatives are both the zero additive map.  This supplies closed
finite-residue local factors, while also showing that nontrivial ABHN local invariants cannot be
recovered from residue-field Brauer data alone.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
  [Finite L] [FiniteDimensional K L] [IsGalois K L]

/-- The sole additive cyclic `H²`-to-Brauer map at a finite field: every class is split. -/
noncomputable def finiteFieldCyclicGaloisH2BrauerZeroAddHom :
    cyclicGaloisH2 K L →+ BrauerGroup K := 0

/-- At a finite field, the selected cyclic `H²` Brauer map in every cyclic degree is its zero
additive refinement. -/
theorem finiteField_cyclicGaloisH2BrauerMap_eq_addHom
    (z : cyclicGaloisH2 K L) :
    cyclicGaloisH2BrauerMap K L z =
      finiteFieldCyclicGaloisH2BrauerZeroAddHom K L z := by
  rw [finiteFieldCyclicGaloisH2BrauerZeroAddHom]
  change cyclicGaloisH2BrauerMap K L z = brauerSplitClass K
  exact finiteField_cyclicGaloisH2BrauerMap_eq_split K L z

/-- At a finite field, the selected cyclic `H²` Brauer map preserves addition in every cyclic
degree. -/
theorem finiteField_cyclicGaloisH2BrauerMap_add
    (x y : cyclicGaloisH2 K L) :
    cyclicGaloisH2BrauerMap K L (x + y) =
      cyclicGaloisH2BrauerMap K L x + cyclicGaloisH2BrauerMap K L y := by
  rw [finiteField_cyclicGaloisH2BrauerMap_eq_addHom,
    finiteField_cyclicGaloisH2BrauerMap_eq_addHom,
    finiteField_cyclicGaloisH2BrauerMap_eq_addHom]
  exact (finiteFieldCyclicGaloisH2BrauerZeroAddHom K L).map_add x y

/-- The finite-field additive refinement of a cyclic `H²` invariant parameter map. -/
noncomputable def finiteFieldCyclicGaloisH2InvariantBrauerZeroAddHom
    (n : ℕ) : ZMod n →+ BrauerGroup K := 0

/-- At a finite field, every selected cyclic `H²` invariant parameter map is its zero additive
refinement. -/
theorem finiteField_cyclicGaloisH2InvariantBrauerMap_eq_addHom
    (n : ℕ) (e : cyclicGaloisH2 K L ≃+ ZMod n) (z : ZMod n) :
    cyclicGaloisH2InvariantBrauerMap K L n e z =
      finiteFieldCyclicGaloisH2InvariantBrauerZeroAddHom K n z := by
  rw [finiteFieldCyclicGaloisH2InvariantBrauerZeroAddHom]
  change cyclicGaloisH2InvariantBrauerMap K L n e z = brauerSplitClass K
  exact finiteField_cyclicGaloisH2InvariantBrauerMap_eq_split K L n e z

/-- At a finite field, selected cyclic `H²` invariant parameter maps preserve addition. -/
theorem finiteField_cyclicGaloisH2InvariantBrauerMap_add
    (n : ℕ) (e : cyclicGaloisH2 K L ≃+ ZMod n) (x y : ZMod n) :
    cyclicGaloisH2InvariantBrauerMap K L n e (x + y) =
      cyclicGaloisH2InvariantBrauerMap K L n e x +
        cyclicGaloisH2InvariantBrauerMap K L n e y := by
  rw [finiteField_cyclicGaloisH2InvariantBrauerMap_eq_addHom,
    finiteField_cyclicGaloisH2InvariantBrauerMap_eq_addHom,
    finiteField_cyclicGaloisH2InvariantBrauerMap_eq_addHom]
  exact (finiteFieldCyclicGaloisH2InvariantBrauerZeroAddHom K n).map_add x y

/-- The sole additive continuous cyclic `H²`-to-Brauer map at a finite field. -/
noncomputable def finiteFieldContinuousCyclicGaloisH2BrauerZeroAddHom :
    continuousGaloisUnitCohomology 2 K L →+ BrauerGroup K := 0

/-- At a finite field, the selected finite continuous cyclic `H²` Brauer map is its zero
additive refinement. -/
theorem finiteField_finiteGaloisContinuousCyclicH2BrauerMap_eq_addHom
    (z : continuousGaloisUnitCohomology 2 K L) :
    finiteGaloisContinuousCyclicH2BrauerMap K L z =
      finiteFieldContinuousCyclicGaloisH2BrauerZeroAddHom K L z := by
  rw [finiteFieldContinuousCyclicGaloisH2BrauerZeroAddHom]
  change finiteGaloisContinuousCyclicH2BrauerMap K L z = brauerSplitClass K
  exact finiteField_finiteGaloisContinuousCyclicH2BrauerMap_eq_split K L z

/-- At a finite field, selected finite continuous cyclic `H²` Brauer maps preserve addition. -/
theorem finiteField_finiteGaloisContinuousCyclicH2BrauerMap_add
    (x y : continuousGaloisUnitCohomology 2 K L) :
    finiteGaloisContinuousCyclicH2BrauerMap K L (x + y) =
      finiteGaloisContinuousCyclicH2BrauerMap K L x +
        finiteGaloisContinuousCyclicH2BrauerMap K L y := by
  rw [finiteField_finiteGaloisContinuousCyclicH2BrauerMap_eq_addHom,
    finiteField_finiteGaloisContinuousCyclicH2BrauerMap_eq_addHom,
    finiteField_finiteGaloisContinuousCyclicH2BrauerMap_eq_addHom]
  exact (finiteFieldContinuousCyclicGaloisH2BrauerZeroAddHom K L).map_add x y

/-- At a finite field, the selected continuous quadratic cyclic `H²` Brauer map is the shared
zero additive refinement. -/
theorem finiteField_finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_addHom
    (hdeg : Module.finrank K L = 2) (z : continuousGaloisUnitCohomology 2 K L) :
    finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap K L hdeg z =
      finiteFieldContinuousCyclicGaloisH2BrauerZeroAddHom K L z := by
  rw [finiteFieldContinuousCyclicGaloisH2BrauerZeroAddHom]
  change finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap K L hdeg z = brauerSplitClass K
  exact finiteField_finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_split K L hdeg z

/-- At a finite field, the selected continuous quadratic cyclic `H²` Brauer map preserves
addition. -/
theorem finiteField_finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_add
    (hdeg : Module.finrank K L = 2) (x y : continuousGaloisUnitCohomology 2 K L) :
    finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap K L hdeg (x + y) =
      finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap K L hdeg x +
        finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap K L hdeg y := by
  rw [finiteField_finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_addHom,
    finiteField_finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_addHom,
    finiteField_finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_addHom]
  exact (finiteFieldContinuousCyclicGaloisH2BrauerZeroAddHom K L).map_add x y

/-- At a finite field, the selected continuous cubic cyclic `H²` Brauer map is the shared zero
additive refinement. -/
theorem finiteField_finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap_eq_addHom
    (hdeg : Module.finrank K L = 3) (z : continuousGaloisUnitCohomology 2 K L) :
    finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap K L hdeg z =
      finiteFieldContinuousCyclicGaloisH2BrauerZeroAddHom K L z := by
  rw [finiteFieldContinuousCyclicGaloisH2BrauerZeroAddHom]
  change finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap K L hdeg z = brauerSplitClass K
  exact finiteField_finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap_eq_split K L hdeg z

/-- At a finite field, the selected continuous cubic cyclic `H²` Brauer map preserves
addition. -/
theorem finiteField_finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap_add
    (hdeg : Module.finrank K L = 3) (x y : continuousGaloisUnitCohomology 2 K L) :
    finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap K L hdeg (x + y) =
      finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap K L hdeg x +
        finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap K L hdeg y := by
  rw [finiteField_finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap_eq_addHom,
    finiteField_finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap_eq_addHom,
    finiteField_finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap_eq_addHom]
  exact (finiteFieldContinuousCyclicGaloisH2BrauerZeroAddHom K L).map_add x y

/-- The finite-field additive refinement of a continuous cyclic `H²` invariant parameter map. -/
noncomputable def finiteFieldContinuousCyclicGaloisH2InvariantBrauerZeroAddHom
    (n : ℕ) : ZMod n →+ BrauerGroup K := 0

/-- At a finite field, every selected finite continuous cyclic `H²` invariant parameter map is
its zero additive refinement. -/
theorem finiteField_finiteGaloisContinuousCyclicH2InvariantBrauerMap_eq_addHom
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ZMod n) (z : ZMod n) :
    finiteGaloisContinuousCyclicH2InvariantBrauerMap K L n e z =
      finiteFieldContinuousCyclicGaloisH2InvariantBrauerZeroAddHom K n z := by
  rw [finiteFieldContinuousCyclicGaloisH2InvariantBrauerZeroAddHom]
  change finiteGaloisContinuousCyclicH2InvariantBrauerMap K L n e z = brauerSplitClass K
  exact finiteField_finiteGaloisContinuousCyclicH2InvariantBrauerMap_eq_split K L n e z

/-- At a finite field, selected finite continuous cyclic `H²` invariant parameter maps preserve
addition. -/
theorem finiteField_finiteGaloisContinuousCyclicH2InvariantBrauerMap_add
    (n : ℕ) (e : continuousGaloisUnitCohomology 2 K L ≃+ ZMod n) (x y : ZMod n) :
    finiteGaloisContinuousCyclicH2InvariantBrauerMap K L n e (x + y) =
      finiteGaloisContinuousCyclicH2InvariantBrauerMap K L n e x +
        finiteGaloisContinuousCyclicH2InvariantBrauerMap K L n e y := by
  rw [finiteField_finiteGaloisContinuousCyclicH2InvariantBrauerMap_eq_addHom,
    finiteField_finiteGaloisContinuousCyclicH2InvariantBrauerMap_eq_addHom,
    finiteField_finiteGaloisContinuousCyclicH2InvariantBrauerMap_eq_addHom]
  exact (finiteFieldContinuousCyclicGaloisH2InvariantBrauerZeroAddHom K n).map_add x y

/-- Over a finite field, the selected quadratic cyclic `H²` Brauer map is its zero additive
refinement. -/
theorem finiteField_quadraticCyclicGaloisH2BrauerMap_eq_addHom
    (hdeg : Module.finrank K L = 2) (z : cyclicGaloisH2 K L) :
    quadraticCyclicGaloisH2BrauerMap K L hdeg z =
      finiteFieldCyclicGaloisH2BrauerZeroAddHom K L z := by
  rw [finiteFieldCyclicGaloisH2BrauerZeroAddHom]
  change quadraticCyclicGaloisH2BrauerMap K L hdeg z = brauerSplitClass K
  exact finiteField_quadraticCyclicGaloisH2BrauerMap_eq_split K L hdeg z

/-- The selected quadratic cyclic `H²` Brauer map preserves addition at a finite field. -/
theorem finiteField_quadraticCyclicGaloisH2BrauerMap_add
    (hdeg : Module.finrank K L = 2) (x y : cyclicGaloisH2 K L) :
    quadraticCyclicGaloisH2BrauerMap K L hdeg (x + y) =
      quadraticCyclicGaloisH2BrauerMap K L hdeg x +
        quadraticCyclicGaloisH2BrauerMap K L hdeg y := by
  rw [finiteField_quadraticCyclicGaloisH2BrauerMap_eq_addHom,
    finiteField_quadraticCyclicGaloisH2BrauerMap_eq_addHom,
    finiteField_quadraticCyclicGaloisH2BrauerMap_eq_addHom]
  exact (finiteFieldCyclicGaloisH2BrauerZeroAddHom K L).map_add x y

/-- Over a finite field, the selected cubic cyclic `H²` Brauer map is its zero additive
refinement. -/
theorem finiteField_cubicCyclicGaloisH2BrauerMap_eq_addHom
    (hdeg : Module.finrank K L = 3) (z : cyclicGaloisH2 K L) :
    cubicCyclicGaloisH2BrauerMap K L hdeg z =
      finiteFieldCyclicGaloisH2BrauerZeroAddHom K L z := by
  rw [finiteFieldCyclicGaloisH2BrauerZeroAddHom]
  change cubicCyclicGaloisH2BrauerMap K L hdeg z = brauerSplitClass K
  exact finiteField_cubicCyclicGaloisH2BrauerMap_eq_split K L hdeg z

/-- The selected cubic cyclic `H²` Brauer map preserves addition at a finite field. -/
theorem finiteField_cubicCyclicGaloisH2BrauerMap_add
    (hdeg : Module.finrank K L = 3) (x y : cyclicGaloisH2 K L) :
    cubicCyclicGaloisH2BrauerMap K L hdeg (x + y) =
      cubicCyclicGaloisH2BrauerMap K L hdeg x +
        cubicCyclicGaloisH2BrauerMap K L hdeg y := by
  rw [finiteField_cubicCyclicGaloisH2BrauerMap_eq_addHom,
    finiteField_cubicCyclicGaloisH2BrauerMap_eq_addHom,
    finiteField_cubicCyclicGaloisH2BrauerMap_eq_addHom]
  exact (finiteFieldCyclicGaloisH2BrauerZeroAddHom K L).map_add x y

end GaloisForLFunctions.HTGeometry.ABHN
