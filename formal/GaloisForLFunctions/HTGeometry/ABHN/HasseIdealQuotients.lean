/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealRelations
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Quotients under Hasse scalar extension

Scalar extension commutes with quotienting by a fixed ideal. This identifies the completed
extension of `A ⧸ I` with the quotient of the completed extension of `A` by the extended ideal.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Extending scalars commutes with quotienting by an ideal. -/
noncomputable def tensorProductQuotientBaseChangeEquiv {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A] (I : Ideal A) :
    L ⊗[K] (A ⧸ I) ≃ₐ[K] (L ⊗[K] A) ⧸ I.map (algebraMap A (L ⊗[K] A)) :=
  Algebra.TensorProduct.tensorQuotientEquiv (R := K) K A L I

end GaloisForLFunctions.HTGeometry.ABHN
