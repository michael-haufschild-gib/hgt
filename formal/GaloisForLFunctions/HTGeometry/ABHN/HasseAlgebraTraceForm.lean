/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraDiscriminant
import GaloisForLFunctions.HTGeometry.SplitFiniteAlgebraDiscriminant

/-!
# Hasse detection of algebra trace pairings

The trace pairing of a finite free algebra transports coefficientwise under scalar extension.
Consequently, a prescribed trace-pairing value can be checked after every completion.  This is
the bilinear layer behind discriminants and separability criteria.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- The algebra trace pairing on pure tensors is the scalar extension of the original pairing. -/
theorem algebra_traceForm_tensor_one {K : Type u} {L : Type v} {B : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    [Module.Free K B] [Module.Finite K B] (x y : B) :
    Algebra.traceForm L (L ⊗[K] B) (1 ⊗ₜ[K] x) (1 ⊗ₜ[K] y) =
      algebraMap K L (Algebra.traceForm K B x y) := by
  simpa only [Algebra.traceForm_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul] using
    GaloisForLFunctions.HTGeometry.trace_tensor_one K L B (x * y)

/-- Equality of a trace-pairing value with a specified scalar is reflected by field scalar
extension. -/
theorem algebra_traceForm_eq_iff_baseChange_eq {K : Type u} {L : Type v} {B : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    [Module.Free K B] [Module.Finite K B] (x y : B) (c : K) :
    Algebra.traceForm K B x y = c ↔
      Algebra.traceForm L (L ⊗[K] B) (1 ⊗ₜ[K] x) (1 ⊗ₜ[K] y) = algebraMap K L c := by
  constructor
  · intro h
    calc
      Algebra.traceForm L (L ⊗[K] B) (1 ⊗ₜ[K] x) (1 ⊗ₜ[K] y) =
          algebraMap K L (Algebra.traceForm K B x y) := algebra_traceForm_tensor_one x y
      _ = algebraMap K L c := congrArg (algebraMap K L) h
  · intro h
    apply FaithfulSMul.algebraMap_injective K L
    calc
      algebraMap K L (Algebra.traceForm K B x y) =
          Algebra.traceForm L (L ⊗[K] B) (1 ⊗ₜ[K] x) (1 ⊗ₜ[K] y) :=
        (algebra_traceForm_tensor_one x y).symm
      _ = algebraMap K L c := h

/-- Nondegeneracy of the trace pairing is reflected by field scalar extension for a finite free
algebra. -/
theorem algebra_traceForm_nondegenerate_iff_baseChange {K : Type u} {L : Type v} {B : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    [Module.Free K B] [Module.Finite K B] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι K B) :
    (Algebra.traceForm K B).Nondegenerate ↔
      (Algebra.traceForm L (L ⊗[K] B)).Nondegenerate := by
  constructor
  · intro h
    apply GaloisForLFunctions.HTGeometry.discr_ne_zero_iff_traceForm_nondegenerate
      (e.baseChange L : Module.Basis ι L (L ⊗[K] B)) |>.mp
    apply (algebra_discr_ne_zero_iff_baseChange_ne_zero (L := L) e).mp
    exact GaloisForLFunctions.HTGeometry.discr_ne_zero_iff_traceForm_nondegenerate e |>.mpr h
  · intro h
    apply GaloisForLFunctions.HTGeometry.discr_ne_zero_iff_traceForm_nondegenerate e |>.mp
    apply (algebra_discr_ne_zero_iff_baseChange_ne_zero (L := L) e).mpr
    exact GaloisForLFunctions.HTGeometry.discr_ne_zero_iff_traceForm_nondegenerate
      (e.baseChange L : Module.Basis ι L (L ⊗[K] B)) |>.mpr h

/-- A number-field algebra has trace-pairing value `c` exactly when every completed scalar
extension has the image of `c` as the pairing of the corresponding pure tensors. -/
theorem numberField_algebra_traceForm_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {B : Type w} [CommRing B] [Algebra K B]
    [Module.Free K B] [Module.Finite K B] (x y : B) (c : K) :
    Algebra.traceForm K B x y = c ↔ ∀ p : NumberFieldPlace K,
      Algebra.traceForm (completion K p) (completion K p ⊗[K] B)
        (1 ⊗ₜ[K] x) (1 ⊗ₜ[K] y) = algebraMap K (completion K p) c := by
  constructor
  · intro h p
    exact (algebra_traceForm_eq_iff_baseChange_eq (L := completion K p) x y c).mp h
  · intro h
    exact (algebra_traceForm_eq_iff_baseChange_eq
      (L := completion K (witnessPlace K)) x y c).mpr (h (witnessPlace K))

/-- A rational-function-field algebra has trace-pairing value `c` exactly when every finite and
infinite completed scalar extension has the image of `c` as the corresponding pairing. -/
theorem rationalFunction_algebra_traceForm_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] {B : Type w} [CommRing B] [Algebra (RatFunc F) B]
    [Module.Free (RatFunc F) B] [Module.Finite (RatFunc F) B] (x y : B) (c : RatFunc F) :
    Algebra.traceForm (RatFunc F) B x y = c ↔ ∀ p : RationalFunctionPlace F,
      Algebra.traceForm (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] B)
        (1 ⊗ₜ[RatFunc F] x) (1 ⊗ₜ[RatFunc F] y) =
          algebraMap (RatFunc F) (rationalFunctionCompletion F p) c := by
  constructor
  · intro h p
    exact (algebra_traceForm_eq_iff_baseChange_eq
      (L := rationalFunctionCompletion F p) x y c).mp h
  · intro h
    exact (algebra_traceForm_eq_iff_baseChange_eq
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) x y c).mpr
      (h RationalFunctionPlace.infinite)

/-- The trace pairing of a finite free number-field algebra is nondegenerate exactly when every
completed trace pairing is nondegenerate. -/
theorem numberField_algebra_traceForm_nondegenerate_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {B : Type w} [CommRing B] [Algebra K B]
    [Module.Free K B] [Module.Finite K B] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι K B) :
    (Algebra.traceForm K B).Nondegenerate ↔ ∀ p : NumberFieldPlace K,
      (Algebra.traceForm (completion K p) (completion K p ⊗[K] B)).Nondegenerate := by
  constructor
  · intro h p
    exact (algebra_traceForm_nondegenerate_iff_baseChange (L := completion K p) e).mp h
  · intro h
    exact (algebra_traceForm_nondegenerate_iff_baseChange
      (L := completion K (witnessPlace K)) e).mpr (h (witnessPlace K))

/-- The trace pairing of a finite free rational-function-field algebra is nondegenerate exactly
when every finite and infinite completed trace pairing is nondegenerate. -/
theorem rationalFunction_algebra_traceForm_nondegenerate_iff_forall_place
    (F : Type u) [Field F] [Finite F] {B : Type w} [CommRing B] [Algebra (RatFunc F) B]
    [Module.Free (RatFunc F) B] [Module.Finite (RatFunc F) B]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι (RatFunc F) B) :
    (Algebra.traceForm (RatFunc F) B).Nondegenerate ↔ ∀ p : RationalFunctionPlace F,
      (Algebra.traceForm (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] B)).Nondegenerate := by
  constructor
  · intro h p
    exact (algebra_traceForm_nondegenerate_iff_baseChange
      (L := rationalFunctionCompletion F p) e).mp h
  · intro h
    exact (algebra_traceForm_nondegenerate_iff_baseChange
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) e).mpr
      (h RationalFunctionPlace.infinite)

end GaloisForLFunctions.HTGeometry.ABHN
