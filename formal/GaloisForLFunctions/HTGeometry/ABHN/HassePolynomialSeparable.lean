/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HassePolynomialIdentity
import Mathlib.FieldTheory.Separable

/-!
# Hasse detection of polynomial separability

Separability of a polynomial is reflected by every field scalar extension.  For global fields,
this gives completion-wise certificates that finite root algebras are reduced and that the
polynomial has no repeated geometric roots.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v

/-- A polynomial over a field is separable exactly when its coefficientwise scalar extension is
separable. -/
theorem polynomial_separable_iff_map {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (p : Polynomial K) :
    p.Separable ↔ (p.map (algebraMap K L)).Separable := by
  exact (Polynomial.separable_map (algebraMap K L)).symm

/-- A polynomial over a number field is separable exactly when its scalar extension is separable
at every completed place. -/
theorem numberFieldPolynomial_separable_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (p : Polynomial K) :
    p.Separable ↔ ∀ v : NumberFieldPlace K,
      (p.map (algebraMap K (completion K v))).Separable := by
  constructor
  · intro h v
    exact (polynomial_separable_iff_map (L := completion K v) p).mp h
  · intro h
    exact (polynomial_separable_iff_map (L := completion K (witnessPlace K)) p).mpr
      (h (witnessPlace K))

/-- A polynomial over `F(t)` is separable exactly when its scalar extension is separable at every
finite and infinite completed place. -/
theorem rationalFunctionPolynomial_separable_iff_forall_place
    (F : Type u) [Field F] [Finite F] (p : Polynomial (RatFunc F)) :
    p.Separable ↔ ∀ v : RationalFunctionPlace F,
      (p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v))).Separable := by
  constructor
  · intro h v
    exact (polynomial_separable_iff_map (L := rationalFunctionCompletion F v) p).mp h
  · intro h
    exact (polynomial_separable_iff_map
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) p).mpr
      (h RationalFunctionPlace.infinite)

end GaloisForLFunctions.HTGeometry.ABHN
