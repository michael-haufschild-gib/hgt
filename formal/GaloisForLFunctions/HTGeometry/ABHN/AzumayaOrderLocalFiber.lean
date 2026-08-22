/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaGenericFiber
import GaloisForLFunctions.HTGeometry.ABHN.LocalScalarExtension

/-!
# Local fibers of Azumaya orders

An Azumaya algebra over the ring of integers of a number field, or over the polynomial ring of a
global function field, has a central simple generic fiber. This module proves that localizing that
generic Brauer class at any packaged completion is the same as taking the completion's field fiber
directly from the Azumaya algebra.

This is the integral-model interface needed for ABHN finite ramification. It does not prove that
the resulting finite-place class is split: that requires the unformalized comparison from Azumaya
algebras over a complete DVR to the Brauer group of its finite residue field.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped NumberField

universe u

noncomputable section

/-- The polynomial-ring algebra structure on a rational-function completion induced through its
global rational-function field. It is local to this integral-model comparison, avoiding a global
instance diamond. -/
noncomputable local instance rationalFunctionCompletionPolynomialAlgebra
    (F : Type u) [Field F] [Finite F] (p : RationalFunctionPlace F) :
    Algebra (Polynomial F) (rationalFunctionCompletion F p) :=
  RingHom.toAlgebra <|
    (algebraMap (RatFunc F) (rationalFunctionCompletion F p)).comp
      (algebraMap (Polynomial F) (RatFunc F))

local instance rationalFunctionCompletionPolynomialIsScalarTower
    (F : Type u) [Field F] [Finite F] (p : RationalFunctionPlace F) :
    IsScalarTower (Polynomial F) (RatFunc F) (rationalFunctionCompletion F p) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Localizing the generic fiber of an Azumaya algebra over `𝓞 K` agrees with taking its direct
field fiber at every number-field completion. -/
theorem numberFieldLocalBrauerMap_azumayaScalarExtensionBrauerClass
    (K : Type u) [Field K] [NumberField K] (p : NumberFieldPlace K)
    (A : Type u) [Ring A] [Algebra (𝓞 K) A] [IsAzumaya (𝓞 K) A] :
    numberFieldLocalBrauerMap K (azumayaScalarExtensionBrauerClass (𝓞 K) K A) p =
      azumayaScalarExtensionBrauerClass (𝓞 K) (completion K p) A := by
  exact azumayaScalarExtensionBrauerClass_trans_eq (𝓞 K) K (completion K p) A

/-- Localizing the generic fiber of an Azumaya algebra over `F[X]` agrees with taking its direct
field fiber at every finite or infinite rational-function-field completion. -/
theorem rationalFunctionLocalBrauerMap_azumayaScalarExtensionBrauerClass
    (F : Type u) [Field F] [Finite F] (p : RationalFunctionPlace F)
    (A : Type u) [Ring A] [Algebra (Polynomial F) A] [IsAzumaya (Polynomial F) A] :
    rationalFunctionLocalBrauerMap F
      (azumayaScalarExtensionBrauerClass (Polynomial F) (RatFunc F) A) p =
      azumayaScalarExtensionBrauerClass (Polynomial F) (rationalFunctionCompletion F p) A := by
  exact azumayaScalarExtensionBrauerClass_trans_eq (Polynomial F) (RatFunc F)
    (rationalFunctionCompletion F p) A

end

end GaloisForLFunctions.HTGeometry.ABHN
