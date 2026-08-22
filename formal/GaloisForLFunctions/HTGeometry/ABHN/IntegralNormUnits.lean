/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Integral norm on units

For a finite integral extension of integrally closed domains, the integral norm restricts to
units.  After passage to fraction fields, this is the ordinary field norm.  This is the
integral-unit part of the norm bridge needed before comparing local-field norms with residue
norms; no residue compatibility or local reciprocity statement is claimed here.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- The integral norm restricted to units of a finite integral extension. -/
noncomputable def integralNormUnits
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsIntegrallyClosed A] [IsDomain A] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] [Module.Finite A B] :
    Additive Bˣ →+ Additive Aˣ :=
  (Units.map (Algebra.intNorm A B)).toAdditive

/-- On a unit, `integralNormUnits` is the unit map induced by the integral norm. -/
theorem integralNormUnits_toMul_apply
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsIntegrallyClosed A] [IsDomain A] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] [Module.Finite A B] (u : Bˣ) :
    (integralNormUnits A B (Additive.ofMul u)).toMul =
      Units.map (Algebra.intNorm A B) u := rfl

/-- The integral norm on units agrees, after embedding into fraction fields, with the field norm.
This is the precise bridge from an integral unramified model to its fraction-field norm. -/
theorem algebraMap_integralNormUnit_eq_fractionField_norm
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsIntegrallyClosed A] [IsDomain A] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra.IsIntegral A B] [Module.IsTorsionFree A B] [Module.Finite A B] (u : Bˣ) :
    algebraMap A (FractionRing A)
        (((integralNormUnits A B (Additive.ofMul u)).toMul : Aˣ) : A) =
      Algebra.norm (FractionRing A)
        (algebraMap B (FractionRing B) ((u : Bˣ) : B)) := by
  change algebraMap A (FractionRing A) (Algebra.intNorm A B (u : B)) =
    Algebra.norm (FractionRing A) (algebraMap B (FractionRing B) (u : B))
  exact Algebra.algebraMap_intNorm_fractionRing (A := A) (B := B) (u : B)

/-- Integral unit norms compose in towers.  This is the tower law needed to assemble the norm
part of finite unramified local extensions before comparing reductions. -/
theorem integralNormUnits_trans
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsIntegrallyClosed A] [IsIntegrallyClosed B] [IsIntegrallyClosed C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [Algebra.IsIntegral A B] [Algebra.IsIntegral B C] [Algebra.IsIntegral A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree B C] [Module.IsTorsionFree A C]
    [Module.Finite A B] [Module.Finite B C] [Module.Finite A C] :
    integralNormUnits A C =
      (integralNormUnits A B).comp (integralNormUnits B C) := by
  ext u
  apply Additive.toMul.injective
  apply Units.ext
  change Algebra.intNorm A C (u.toMul : C) =
    Algebra.intNorm A B (Algebra.intNorm B C (u.toMul : C))
  rw [Algebra.intNorm_intNorm]

end GaloisForLFunctions.HTGeometry.ABHN
