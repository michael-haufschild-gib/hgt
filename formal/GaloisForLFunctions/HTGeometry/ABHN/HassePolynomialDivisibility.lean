/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HassePolynomialCoprime
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Hasse detection for prescribed polynomial factors

Divisibility by a fixed monic polynomial is reflected by field scalar extension. For global
fields, a prescribed monic factor can therefore be certified at every completion. This is useful
for local checks of quotient algebras and factorisations with global coefficients.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v

/-- Divisibility by a monic polynomial is reflected by coefficientwise field scalar extension. -/
theorem polynomial_dvd_iff_map_of_monic {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (p q : Polynomial K) (hp : p.Monic) :
    p ∣ q ↔ p.map (algebraMap K L) ∣ q.map (algebraMap K L) := by
  exact (Polynomial.map_dvd_map (algebraMap K L)
    (FaithfulSMul.algebraMap_injective K L) hp).symm

/-- A monic polynomial over a number field divides another exactly when its completed image does
at every place. -/
theorem numberFieldPolynomial_dvd_iff_forall_place_of_monic
    (K : Type u) [Field K] [NumberField K] (p q : Polynomial K) (hp : p.Monic) :
    p ∣ q ↔ ∀ v : NumberFieldPlace K,
      p.map (algebraMap K (completion K v)) ∣ q.map (algebraMap K (completion K v)) := by
  constructor
  · intro h v
    exact (polynomial_dvd_iff_map_of_monic (L := completion K v) p q hp).mp h
  · intro h
    exact (polynomial_dvd_iff_map_of_monic
      (L := completion K (witnessPlace K)) p q hp).mpr (h (witnessPlace K))

/-- A monic polynomial over `F(t)` divides another exactly when its completed image does at every
finite and infinite place. -/
theorem rationalFunctionPolynomial_dvd_iff_forall_place_of_monic
    (F : Type u) [Field F] [Finite F] (p q : Polynomial (RatFunc F)) (hp : p.Monic) :
    p ∣ q ↔ ∀ v : RationalFunctionPlace F,
      p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v)) ∣
        q.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v)) := by
  constructor
  · intro h v
    exact (polynomial_dvd_iff_map_of_monic (L := rationalFunctionCompletion F v) p q hp).mp h
  · intro h
    exact (polynomial_dvd_iff_map_of_monic
      (L := rationalFunctionCompletion F .infinite) p q hp).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
