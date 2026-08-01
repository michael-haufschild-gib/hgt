import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Degrees under partial differentiation

Differentiating in a variable strictly decreases the degree in that variable, and in characteristic
zero a variable whose partial derivative vanishes does not occur at all.  A polynomial's evaluation
does not depend on a variable that does not occur in it.

These are the bookkeeping facts of the descent on an algebraic differential relation: differentiate
in the top jet until the relation either becomes nondegenerate there or ceases to involve it, in
which case it is a relation of lower order.
-/

open Finsupp

namespace GaloisForLFunctions

variable {σ : Type*} {R : Type*} [CommRing R]

/-- **A partial derivative strictly drops the degree in that variable.** -/
theorem degreeOf_pderiv_lt [NoZeroDivisors R] {i : σ} {p : MvPolynomial σ R}
    (h : MvPolynomial.pderiv i p ≠ 0) :
    MvPolynomial.degreeOf i (MvPolynomial.pderiv i p) < MvPolynomial.degreeOf i p := by
  classical
  have hstep : ∀ m ∈ (MvPolynomial.pderiv i p).support, m i + 1 ≤ MvPolynomial.degreeOf i p := by
    intro m hm
    have hne : MvPolynomial.coeff m (MvPolynomial.pderiv i p) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_pderiv] at hne
    have hcoeff : MvPolynomial.coeff (m + single i 1) p ≠ 0 := fun hc => hne (by simp [hc])
    have hmem : (m + single i 1) ∈ p.support := MvPolynomial.mem_support_iff.mpr hcoeff
    have hle : (m + single i 1 : σ →₀ ℕ) i ≤ MvPolynomial.degreeOf i p := by
      rw [MvPolynomial.degreeOf_eq_sup]
      exact Finset.le_sup (f := fun d : σ →₀ ℕ => d i) hmem
    simpa using hle
  obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.mpr
    (fun hempty => h (MvPolynomial.support_eq_empty.mp hempty))
  have hpos : 0 < MvPolynomial.degreeOf i p := lt_of_lt_of_le (Nat.succ_pos _) (hstep m hm)
  rw [MvPolynomial.degreeOf_lt_iff hpos]
  intro m' hm'
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (hstep m' hm')

/-- **In characteristic zero a variable with vanishing partial derivative does not occur.** -/
theorem degreeOf_eq_zero_of_pderiv_eq_zero [CharZero R] [NoZeroDivisors R] {i : σ}
    {p : MvPolynomial σ R}
    (h : MvPolynomial.pderiv i p = 0) : MvPolynomial.degreeOf i p = 0 := by
  classical
  refine Nat.le_zero.mp (MvPolynomial.degreeOf_le_iff.mpr fun d hd => Nat.le_zero.mpr ?_)
  by_contra hdi
  have hd1 : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr hdi
  set m : σ →₀ ℕ := d - single i 1 with hm
  have hsum : m + single i 1 = d := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hm, Nat.sub_add_cancel hd1]
    · simp [hm, hj]
  have hmi : m i + 1 = d i := by
    simp [hm, Nat.sub_add_cancel hd1]
  have hc := MvPolynomial.coeff_pderiv (i := i) p m
  rw [h] at hc
  simp only [MvPolynomial.coeff_zero, hsum] at hc
  have hne : MvPolynomial.coeff d p ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have hcast : ((m i : R) + 1) ≠ 0 := by
    have h1 : ((m i + 1 : ℕ) : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    simpa using h1
  exact absurd hc.symm (mul_ne_zero hne hcast)

/-- The evaluation of a polynomial does not depend on a variable that does not occur in it. -/
theorem eval_eq_of_degreeOf_eq_zero {i : σ} {p : MvPolynomial σ R}
    (h : MvPolynomial.degreeOf i p = 0) {y z : σ → R} (hyz : ∀ j, j ≠ i → y j = z j) :
    MvPolynomial.eval y p = MvPolynomial.eval z p := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdi : d i = 0 := Nat.le_zero.mp (MvPolynomial.degreeOf_le_iff.mp (le_of_eq h) d hd)
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  have hji : j ≠ i := by
    intro hcon
    subst hcon
    exact (Finsupp.mem_support_iff.mp hj) hdi
  rw [hyz j hji]

end GaloisForLFunctions
