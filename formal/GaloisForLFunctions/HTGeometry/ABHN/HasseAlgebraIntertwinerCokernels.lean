/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwiners
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapCokernels

/-!
# Hasse detection of intertwiner obstructions in central simple algebras

The cokernel of the Sylvester map `x ↦ a * x - x * b` measures independent obstructions to an
inhomogeneous intertwining equation. Its dimension is unchanged by field scalar extension and is
therefore detectable at every completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- The dimension of the cokernel of the Sylvester map is unchanged by field scalar extension. -/
theorem scalarExtensionMap_intertwiner_cokernel_finrank {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K) (a b : A.carrier) :
    Module.finrank L ((L ⊗[K] A.carrier) ⧸ LinearMap.range
      (LinearMap.mulLeft L (scalarExtensionMap (L := L) A a) -
        LinearMap.mulRight L (scalarExtensionMap (L := L) A b))) =
      Module.finrank K (A.carrier ⧸ LinearMap.range
        (LinearMap.mulLeft K a - LinearMap.mulRight K b)) := by
  rw [scalarExtensionMap_intertwiner_eq_linearMapBaseChange]
  exact linearMap_cokernel_finrank_baseChange (L := L)
    (LinearMap.mulLeft K a - LinearMap.mulRight K b)

/-- The dimension of the Sylvester cokernel is unchanged at every completed place of a number
field. -/
theorem numberFieldLocalScalarExtensionMap_intertwiner_cokernel_finrank_completion
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier)
    (p : NumberFieldPlace K) :
    Module.finrank (completion K p) ((completion K p ⊗[K] A.carrier) ⧸ LinearMap.range
      (LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A a) -
        LinearMap.mulRight (completion K p) (numberFieldLocalScalarExtensionMap K p A b))) =
      Module.finrank K (A.carrier ⧸ LinearMap.range
        (LinearMap.mulLeft K a - LinearMap.mulRight K b)) :=
  scalarExtensionMap_intertwiner_cokernel_finrank (L := completion K p) A a b

/-- The Sylvester cokernel dimension equals `d` exactly when this holds at every completed place
of a number field. -/
theorem numberFieldLocalScalarExtensionMap_intertwiner_cokernel_finrank_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) (d : ℕ) :
    Module.finrank K (A.carrier ⧸ LinearMap.range
      (LinearMap.mulLeft K a - LinearMap.mulRight K b)) = d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p) ((completion K p ⊗[K] A.carrier) ⧸ LinearMap.range
          (LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A a) -
            LinearMap.mulRight (completion K p) (numberFieldLocalScalarExtensionMap K p A b))) = d := by
  constructor
  · intro h p
    rw [numberFieldLocalScalarExtensionMap_intertwiner_cokernel_finrank_completion K A a b p, h]
  · intro h
    rw [← numberFieldLocalScalarExtensionMap_intertwiner_cokernel_finrank_completion K A a b
      (witnessPlace K)]
    exact h (witnessPlace K)

/-- The dimension of the Sylvester cokernel is unchanged at every finite and infinite completed
place of `F(t)`. -/
theorem rationalFunctionLocalScalarExtensionMap_intertwiner_cokernel_finrank_completion
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier)
    (p : RationalFunctionPlace F) :
    Module.finrank (rationalFunctionCompletion F p)
      ((rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier) ⧸ LinearMap.range
        (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A a) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A b))) =
      Module.finrank (RatFunc F) (A.carrier ⧸ LinearMap.range
        (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b)) :=
  scalarExtensionMap_intertwiner_cokernel_finrank (L := rationalFunctionCompletion F p) A a b

/-- The Sylvester cokernel dimension equals `d` exactly when this holds at every finite and
infinite completed place of `F(t)`. -/
theorem rationalFunctionLocalScalarExtensionMap_intertwiner_cokernel_finrank_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a b : A.carrier) (d : ℕ) :
    Module.finrank (RatFunc F) (A.carrier ⧸ LinearMap.range
      (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b)) = d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          ((rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier) ⧸ LinearMap.range
            (LinearMap.mulLeft (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p A a) -
              LinearMap.mulRight (rationalFunctionCompletion F p)
                (rationalFunctionLocalScalarExtensionMap F p A b))) = d := by
  constructor
  · intro h p
    rw [rationalFunctionLocalScalarExtensionMap_intertwiner_cokernel_finrank_completion F A a b p,
      h]
  · intro h
    rw [← rationalFunctionLocalScalarExtensionMap_intertwiner_cokernel_finrank_completion F A a b
      .infinite]
    exact h .infinite

end GaloisForLFunctions.HTGeometry.ABHN
