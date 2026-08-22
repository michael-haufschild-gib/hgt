/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HassePolynomialSeparable
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Hasse detection for coprime polynomials

Polynomial coprimality is reflected by field scalar extension. For global fields this makes
coprime factorisations, and thus Chinese-remainder decompositions of polynomial quotient
algebras, checkable at every completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v

/-- Two polynomials over a field are coprime exactly when their coefficientwise scalar extensions
are coprime. -/
theorem polynomial_isCoprime_iff_map {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (p q : Polynomial K) :
    IsCoprime p q ↔ IsCoprime (p.map (algebraMap K L)) (q.map (algebraMap K L)) := by
  exact (Polynomial.isCoprime_map (p := p) (q := q) (algebraMap K L)).symm

/-- Two polynomials over a number field are coprime exactly when their completed coefficient
extensions are coprime at every place. -/
theorem numberFieldPolynomial_isCoprime_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (p q : Polynomial K) :
    IsCoprime p q ↔ ∀ v : NumberFieldPlace K,
      IsCoprime (p.map (algebraMap K (completion K v)))
        (q.map (algebraMap K (completion K v))) := by
  constructor
  · intro h v
    exact (polynomial_isCoprime_iff_map (L := completion K v) p q).mp h
  · intro h
    exact (polynomial_isCoprime_iff_map (L := completion K (witnessPlace K)) p q).mpr
      (h (witnessPlace K))

/-- Two polynomials over `F(t)` are coprime exactly when their completed coefficient extensions
are coprime at every finite and infinite place. -/
theorem rationalFunctionPolynomial_isCoprime_iff_forall_place
    (F : Type u) [Field F] [Finite F] (p q : Polynomial (RatFunc F)) :
    IsCoprime p q ↔ ∀ v : RationalFunctionPlace F,
      IsCoprime (p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v)))
        (q.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v))) := by
  constructor
  · intro h v
    exact (polynomial_isCoprime_iff_map (L := rationalFunctionCompletion F v) p q).mp h
  · intro h
    exact (polynomial_isCoprime_iff_map
      (L := rationalFunctionCompletion F .infinite) p q).mpr (h .infinite)

/-- Coprimality of number-field polynomials can be certified at one completion. -/
theorem numberFieldPolynomial_isCoprime_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (p q : Polynomial K) :
    IsCoprime p q ↔ ∃ v : NumberFieldPlace K,
      IsCoprime (p.map (algebraMap K (completion K v)))
        (q.map (algebraMap K (completion K v))) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (polynomial_isCoprime_iff_map (L := completion K (witnessPlace K)) p q).mp h⟩
  · rintro ⟨v, hv⟩
    exact (polynomial_isCoprime_iff_map (L := completion K v) p q).mpr hv

/-- Coprimality of `F(t)`-polynomials can be certified at one completion. -/
theorem rationalFunctionPolynomial_isCoprime_iff_exists_place
    (F : Type u) [Field F] [Finite F] (p q : Polynomial (RatFunc F)) :
    IsCoprime p q ↔ ∃ v : RationalFunctionPlace F,
      IsCoprime (p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v)))
        (q.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v))) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (polynomial_isCoprime_iff_map
        (L := rationalFunctionCompletion F .infinite) p q).mp h⟩
  · rintro ⟨v, hv⟩
    exact (polynomial_isCoprime_iff_map (L := rationalFunctionCompletion F v) p q).mpr hv

end GaloisForLFunctions.HTGeometry.ABHN
