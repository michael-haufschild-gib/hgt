/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.Places
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionPlaces
import GaloisForLFunctions.HTGeometry.AlgebraDiscriminantBaseChange

/-!
# Hasse detection of algebra discriminants

For a finite free algebra and a fixed basis, base change transports its discriminant
coefficientwise.  Thus both a prescribed discriminant value and nonvanishing of the discriminant
are detected at every completion.  The latter is the scalar obstruction underlying many
finite-étale and ramification arguments.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w x

open scoped TensorProduct

/-- Equality of an algebra discriminant with a specified scalar is reflected by field scalar
extension. -/
theorem algebra_discr_eq_iff_baseChange_eq {K : Type u} {L : Type v} {B : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    [Module.Free K B] [Module.Finite K B] {ι : Type x} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι K B) (c : K) :
    Algebra.discr K e = c ↔ Algebra.discr L (e.baseChange L : Module.Basis ι L (L ⊗[K] B)) =
      algebraMap K L c := by
  constructor
  · intro h
    calc
      Algebra.discr L (e.baseChange L : Module.Basis ι L (L ⊗[K] B)) =
          algebraMap K L (Algebra.discr K e) :=
        GaloisForLFunctions.HTGeometry.discr_baseChange K L B e
      _ = algebraMap K L c := congrArg (algebraMap K L) h
  · intro h
    apply FaithfulSMul.algebraMap_injective K L
    calc
      algebraMap K L (Algebra.discr K e) =
          Algebra.discr L (e.baseChange L : Module.Basis ι L (L ⊗[K] B)) :=
        (GaloisForLFunctions.HTGeometry.discr_baseChange K L B e).symm
      _ = algebraMap K L c := h

/-- Nonvanishing of an algebra discriminant is reflected by field scalar extension. -/
theorem algebra_discr_ne_zero_iff_baseChange_ne_zero {K : Type u} {L : Type v} {B : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    [Module.Free K B] [Module.Finite K B] {ι : Type x} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι K B) :
    Algebra.discr K e ≠ 0 ↔
      Algebra.discr L (e.baseChange L : Module.Basis ι L (L ⊗[K] B)) ≠ 0 := by
  constructor
  · intro h hzero
    apply h
    apply FaithfulSMul.algebraMap_injective K L
    rw [map_zero, ← GaloisForLFunctions.HTGeometry.discr_baseChange K L B e]
    exact hzero
  · intro h hzero
    apply h
    rw [GaloisForLFunctions.HTGeometry.discr_baseChange K L B e, hzero, map_zero]

/-- Equality of an algebra trace value with a specified scalar is reflected by field scalar
extension. -/
theorem algebra_trace_eq_iff_baseChange_eq {K : Type u} {L : Type v} {B : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    [Module.Free K B] [Module.Finite K B] (x : B) (c : K) :
    Algebra.trace K B x = c ↔ Algebra.trace L (L ⊗[K] B) (1 ⊗ₜ[K] x) = algebraMap K L c := by
  constructor
  · intro h
    calc
      Algebra.trace L (L ⊗[K] B) (1 ⊗ₜ[K] x) = algebraMap K L (Algebra.trace K B x) :=
        GaloisForLFunctions.HTGeometry.trace_tensor_one K L B x
      _ = algebraMap K L c := congrArg (algebraMap K L) h
  · intro h
    apply FaithfulSMul.algebraMap_injective K L
    calc
      algebraMap K L (Algebra.trace K B x) = Algebra.trace L (L ⊗[K] B) (1 ⊗ₜ[K] x) :=
        (GaloisForLFunctions.HTGeometry.trace_tensor_one K L B x).symm
      _ = algebraMap K L c := h

/-- A number-field algebra has discriminant `c` exactly when every completed scalar extension has
the image of `c` as discriminant. -/
theorem numberField_algebra_discr_eq_iff_forall_place (K : Type u) [Field K] [NumberField K]
    {B : Type w} [CommRing B] [Algebra K B] [Module.Free K B] [Module.Finite K B]
    {ι : Type x} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι K B) (c : K) :
    Algebra.discr K e = c ↔ ∀ p : NumberFieldPlace K,
      Algebra.discr (completion K p)
        (e.baseChange (completion K p) : Module.Basis ι (completion K p) (completion K p ⊗[K] B)) =
          algebraMap K (completion K p) c := by
  constructor
  · intro h p
    exact (algebra_discr_eq_iff_baseChange_eq (L := completion K p) e c).mp h
  · intro h
    exact (algebra_discr_eq_iff_baseChange_eq (L := completion K (witnessPlace K)) e c).mpr
      (h (witnessPlace K))

/-- Nonvanishing of a number-field algebra discriminant is detected at every completed place. -/
theorem numberField_algebra_discr_ne_zero_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {B : Type w} [CommRing B] [Algebra K B]
    [Module.Free K B] [Module.Finite K B] {ι : Type x} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι K B) :
    Algebra.discr K e ≠ 0 ↔ ∀ p : NumberFieldPlace K,
      Algebra.discr (completion K p)
        (e.baseChange (completion K p) : Module.Basis ι (completion K p) (completion K p ⊗[K] B)) ≠ 0 := by
  constructor
  · intro h p
    exact (algebra_discr_ne_zero_iff_baseChange_ne_zero (L := completion K p) e).mp h
  · intro h
    exact (algebra_discr_ne_zero_iff_baseChange_ne_zero
      (L := completion K (witnessPlace K)) e).mpr (h (witnessPlace K))

/-- A rational-function-field algebra has discriminant `c` exactly when every finite and infinite
completed scalar extension has the image of `c` as discriminant. -/
theorem rationalFunction_algebra_discr_eq_iff_forall_place (F : Type u) [Field F] [Finite F]
    {B : Type w} [CommRing B] [Algebra (RatFunc F) B]
    [Module.Free (RatFunc F) B] [Module.Finite (RatFunc F) B]
    {ι : Type x} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι (RatFunc F) B) (c : RatFunc F) :
    Algebra.discr (RatFunc F) e = c ↔ ∀ p : RationalFunctionPlace F,
      Algebra.discr (rationalFunctionCompletion F p)
        (e.baseChange (rationalFunctionCompletion F p) :
          Module.Basis ι (rationalFunctionCompletion F p) (rationalFunctionCompletion F p ⊗[RatFunc F] B)) =
            algebraMap (RatFunc F) (rationalFunctionCompletion F p) c := by
  constructor
  · intro h p
    exact (algebra_discr_eq_iff_baseChange_eq (L := rationalFunctionCompletion F p) e c).mp h
  · intro h
    exact (algebra_discr_eq_iff_baseChange_eq
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) e c).mpr
      (h RationalFunctionPlace.infinite)

/-- Nonvanishing of a rational-function-field algebra discriminant is detected at every finite and
infinite completed place. -/
theorem rationalFunction_algebra_discr_ne_zero_iff_forall_place (F : Type u)
    [Field F] [Finite F] {B : Type w} [CommRing B] [Algebra (RatFunc F) B]
    [Module.Free (RatFunc F) B] [Module.Finite (RatFunc F) B]
    {ι : Type x} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι (RatFunc F) B) :
    Algebra.discr (RatFunc F) e ≠ 0 ↔ ∀ p : RationalFunctionPlace F,
      Algebra.discr (rationalFunctionCompletion F p)
        (e.baseChange (rationalFunctionCompletion F p) :
          Module.Basis ι (rationalFunctionCompletion F p) (rationalFunctionCompletion F p ⊗[RatFunc F] B)) ≠ 0 := by
  constructor
  · intro h p
    exact (algebra_discr_ne_zero_iff_baseChange_ne_zero
      (L := rationalFunctionCompletion F p) e).mp h
  · intro h
    exact (algebra_discr_ne_zero_iff_baseChange_ne_zero
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) e).mpr
      (h RationalFunctionPlace.infinite)

/-- A number-field algebra has trace value `c` on `x` exactly when every completed scalar
extension has the image of `c` as the trace of `1 ⊗ x`. -/
theorem numberField_algebra_trace_eq_iff_forall_place (K : Type u) [Field K] [NumberField K]
    {B : Type w} [CommRing B] [Algebra K B] [Module.Free K B] [Module.Finite K B]
    (x : B) (c : K) :
    Algebra.trace K B x = c ↔ ∀ p : NumberFieldPlace K,
      Algebra.trace (completion K p) (completion K p ⊗[K] B) (1 ⊗ₜ[K] x) =
        algebraMap K (completion K p) c := by
  constructor
  · intro h p
    exact (algebra_trace_eq_iff_baseChange_eq (L := completion K p) x c).mp h
  · intro h
    exact (algebra_trace_eq_iff_baseChange_eq (L := completion K (witnessPlace K)) x c).mpr
      (h (witnessPlace K))

/-- A rational-function-field algebra has trace value `c` on `x` exactly when every finite and
infinite completed scalar extension has the image of `c` as the trace of `1 ⊗ x`. -/
theorem rationalFunction_algebra_trace_eq_iff_forall_place (F : Type u) [Field F] [Finite F]
    {B : Type w} [CommRing B] [Algebra (RatFunc F) B]
    [Module.Free (RatFunc F) B] [Module.Finite (RatFunc F) B]
    (x : B) (c : RatFunc F) :
    Algebra.trace (RatFunc F) B x = c ↔ ∀ p : RationalFunctionPlace F,
      Algebra.trace (rationalFunctionCompletion F p) (rationalFunctionCompletion F p ⊗[RatFunc F] B)
        (1 ⊗ₜ[RatFunc F] x) = algebraMap (RatFunc F) (rationalFunctionCompletion F p) c := by
  constructor
  · intro h p
    exact (algebra_trace_eq_iff_baseChange_eq (L := rationalFunctionCompletion F p) x c).mp h
  · intro h
    exact (algebra_trace_eq_iff_baseChange_eq
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) x c).mpr
      (h RationalFunctionPlace.infinite)

end GaloisForLFunctions.HTGeometry.ABHN
