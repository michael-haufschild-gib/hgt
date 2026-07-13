import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# The derivative of an algebraic element is algebraic

If `x` is algebraic over a differential subfield `A` of characteristic zero, then its derivative
`x′` is again algebraic over `A`.  Differentiating the minimal-polynomial relation `p(x) = 0` gives
`mapCoeffs(p)(x) + p'(x)·x′ = 0`; `p'(x) ≠ 0` by separability, so `x′` is a rational expression in
`x` and hence lies in the algebraic field `A⟮x⟯`.  Consequently the relative algebraic closure of a
differential field is derivation-closed.
-/

open scoped Differential
open Polynomial

namespace GaloisForLFunctions

variable {A R : Type*} [Field A] [Field R] [Algebra A R]
  [Differential A] [Differential R] [DifferentialAlgebra A R]

omit [Differential A] [Differential R] [DifferentialAlgebra A R] in
/-- For an algebraic element `x` over a characteristic-zero differential field, the derivative of its
minimal polynomial does not vanish at `x`. -/
theorem aeval_derivative_minpoly_ne_zero [CharZero A] {x : R} (hx : IsAlgebraic A x) :
    aeval x (derivative (minpoly A x)) ≠ 0 := by
  intro h
  have hint : IsIntegral A x := hx.isIntegral
  have hdvd : minpoly A x ∣ derivative (minpoly A x) := minpoly.dvd A x h
  have hirr : Irreducible (minpoly A x) := minpoly.irreducible hint
  have hpos : 0 < (minpoly A x).natDegree := hirr.natDegree_pos
  have hderiv_ne : derivative (minpoly A x) ≠ 0 := by
    intro hz
    exact absurd (natDegree_eq_zero_of_derivative_eq_zero hz) (by omega)
  have hle : (derivative (minpoly A x)).natDegree < (minpoly A x).natDegree :=
    natDegree_derivative_lt (Nat.ne_zero_of_lt hpos)
  exact absurd (Polynomial.natDegree_le_of_dvd hdvd hderiv_ne) (by omega)

/-- The derivative of an algebraic element over a characteristic-zero differential field is
algebraic over that field. -/
theorem isAlgebraic_deriv [CharZero A] {x : R} (hx : IsAlgebraic A x) :
    IsAlgebraic A (Differential.deriv x) := by
  have hint : IsIntegral A x := hx.isIntegral
  have hrel : aeval x (minpoly A x) = 0 := minpoly.aeval A x
  have hchain := Differential.deriv_aeval_eq (A := A) x (minpoly A x)
  rw [hrel, map_zero] at hchain
  have hden : aeval x (derivative (minpoly A x)) ≠ 0 := aeval_derivative_minpoly_ne_zero hx
  -- work inside the algebraic field `A⟮x⟯`
  set K := IntermediateField.adjoin A ({x} : Set R) with hK
  have hxK : x ∈ K := IntermediateField.mem_adjoin_simple_self A x
  haveI hfin : FiniteDimensional A K :=
    IntermediateField.adjoin.finiteDimensional hint
  -- polynomial evaluations at `x` lie in `A⟮x⟯`
  have haevalmem : ∀ q : A[X], aeval x q ∈ K := by
    have hle : (Algebra.adjoin A {x} : Subalgebra A R) ≤ K.toSubalgebra :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxK)
    intro q
    apply hle
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨q, rfl⟩
  have hnum : - aeval x (Differential.mapCoeffs (minpoly A x)) ∈ K :=
    K.neg_mem (haevalmem _)
  have hdenmem : aeval x (derivative (minpoly A x)) ∈ K := haevalmem _
  -- `x′ = (-num) * den⁻¹ ∈ A⟮x⟯`
  have hx'K : Differential.deriv x ∈ K := by
    have hval : aeval x (derivative (minpoly A x)) * Differential.deriv x =
        - aeval x (Differential.mapCoeffs (minpoly A x)) := by
      linear_combination -hchain
    have : Differential.deriv x =
        (- aeval x (Differential.mapCoeffs (minpoly A x))) *
          (aeval x (derivative (minpoly A x)))⁻¹ := by
      rw [← hval]; field_simp
    rw [this]
    exact K.mul_mem hnum (K.inv_mem hdenmem)
  -- an element of an algebraic extension is algebraic
  have halg : IsAlgebraic A (⟨Differential.deriv x, hx'K⟩ : K) :=
    Algebra.IsAlgebraic.isAlgebraic _
  have := halg.algHom (IsScalarTower.toAlgHom A K R)
  simpa using this

end GaloisForLFunctions
