/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicAlgebra

/-!
# Generator criterion for cyclic-algebra lifts

The universal lift of a cyclic algebra asks for a compatibility equation at every nonnegative
power of the twisting automorphism.  This file shows that the one-generator equation implies the
full family, so concrete companion representations need verify only their generator matrix
identity.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Multiplicative

/-- A coefficient map that commutes with the image of the twisting generator satisfies the full
powerwise compatibility required by `cyclicAlgebraLift`. -/
theorem cyclicAlgebraLift_comm_of_generator
    {L B : Type*} [CommRing L] [Ring B] (σ : L ≃+* L) (f : L →+* B) (y : B)
    (hone : ∀ x : L, f (σ x) * y = y * f x) :
    ∀ (m : Multiplicative ℕ) (x : L),
      f ((cyclicPowerRingAut σ m) x) * cyclicPowerMonoidHom y m =
        cyclicPowerMonoidHom y m * f x := by
  intro m
  induction m using Multiplicative.rec with
  | ofAdd m =>
    intro x
    change f ((σ ^ m) x) * y ^ m = y ^ m * f x
    induction m generalizing x with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, pow_succ]
      change f ((σ ^ m) (σ x)) * (y ^ m * y) = (y ^ m * y) * f x
      rw [← mul_assoc, ih, mul_assoc, hone, ← mul_assoc]

end GaloisForLFunctions.HTGeometry.ABHN
