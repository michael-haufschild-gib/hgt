/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseFiniteness

/-!
# Hasse detection for finite ideal generation

Extending scalars from a field to a field extension is faithfully flat, including after base
change along a commutative algebra.  A fixed ideal is finitely generated exactly when its extended
ideal is finitely generated.  This is the relation-ideal counterpart of finite presentation.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Finite generation of an ideal is reflected by field scalar extension. -/
theorem ideal_fg_iff_tensorProduct_map_fg {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A] (I : Ideal A) :
    I.FG ↔ (I.map (algebraMap A (L ⊗[K] A))).FG := by
  letI : Module.FaithfullyFlat A (A ⊗[K] L) := inferInstance
  letI : Module.FaithfullyFlat A (L ⊗[K] A) :=
    Module.FaithfullyFlat.of_linearEquiv A (A ⊗[K] L)
      (Algebra.TensorProduct.commRight K A L).symm.toLinearEquiv
  constructor
  · intro h
    exact h.map (algebraMap A (L ⊗[K] A))
  · intro h
    exact Ideal.FG.of_FG_map_of_faithfullyFlat h

/-- An ideal in a commutative number-field algebra is finitely generated exactly when its extension
at every completed place is finitely generated. -/
theorem numberField_ideal_fg_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) :
    I.FG ↔ ∀ p : NumberFieldPlace K,
      (I.map (algebraMap A (completion K p ⊗[K] A))).FG := by
  constructor
  · intro h p
    exact (ideal_fg_iff_tensorProduct_map_fg (L := completion K p) I).mp h
  · intro h
    exact (ideal_fg_iff_tensorProduct_map_fg
      (L := completion K (witnessPlace K)) I).mpr (h (witnessPlace K))

/-- An ideal in a commutative `F(t)`-algebra is finitely generated exactly when its extension at
every finite and infinite completed place is finitely generated. -/
theorem rationalFunction_ideal_fg_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) :
    I.FG ↔ ∀ p : RationalFunctionPlace F,
      (I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A))).FG := by
  constructor
  · intro h p
    exact (ideal_fg_iff_tensorProduct_map_fg
      (L := rationalFunctionCompletion F p) I).mp h
  · intro h
    exact (ideal_fg_iff_tensorProduct_map_fg
      (L := rationalFunctionCompletion F .infinite) I).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
