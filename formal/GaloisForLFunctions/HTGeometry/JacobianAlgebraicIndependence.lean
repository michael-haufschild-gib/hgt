import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# A polynomial Jacobian criterion for algebraic independence

Mathlib supplies multivariable partial derivatives, algebraic independence, and the matrix
nondegeneracy theorem, but not their characteristic-zero Jacobian-criterion connection.  This
module proves the square-minor form needed by finite horizon observation maps: a family of
polynomials is algebraically independent whenever one square minor of its formal Jacobian has
nonzero determinant.

The proof is purely algebraic.  A chain rule sends every polynomial relation to a homogeneous
linear system for its partial derivatives.  Matrix nondegeneracy kills that gradient, while a
total-degree induction and the characteristic-zero coefficient formula force the relation itself
to be constant and then zero.
-/

open scoped BigOperators
open Matrix

namespace MvPolynomial

variable {K ι σ : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι]

omit [CharZero K] in
theorem pderiv_aeval_chain (f : ι → MvPolynomial σ K)
    (P : MvPolynomial ι K) (j : σ) :
    pderiv j (aeval f P) =
      ∑ i, aeval f (pderiv i P) * pderiv j (f i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simp only [map_add, hp, hq]
      simp only [add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
      simp only [map_mul, aeval_X, pderiv_mul, hp]
      simp only [map_add, map_mul, aeval_X, pderiv_X]
      simp [Pi.single_apply, Finset.sum_add_distrib, Finset.sum_mul, add_mul]
      apply Finset.sum_congr rfl
      intro x hx
      ring

omit [Fintype ι] in
theorem totalDegree_pderiv_le (P : MvPolynomial ι K) (i : ι) :
    (pderiv i P).totalDegree ≤ P.totalDegree - 1 := by
  classical
  conv_lhs => rw [P.as_sum]
  simp only [map_sum]
  apply totalDegree_finsetSum_le
  intro s hs
  rw [pderiv_monomial]
  by_cases hi : s i = 0
  · simp [hi]
  calc
    (monomial (s - Finsupp.single i 1) (coeff s P * ↑(s i))).totalDegree
        ≤ (s - Finsupp.single i 1).sum (fun _ e => e) :=
      totalDegree_monomial_le _ _
    _ ≤ P.totalDegree - 1 := by
      have hsum :
          (s - Finsupp.single i 1).sum (fun _ e => e) + 1 =
            s.sum (fun _ e => e) := by
        have hEq := congrArg (fun u : ι →₀ ℕ => u.sum (fun _ e => e))
          (Finsupp.sub_add_single_one_cancel hi)
        simpa [Finsupp.sum_add_index] using hEq
      have hdeg := le_totalDegree hs
      omega

omit [Fintype ι] in
theorem totalDegree_pderiv_lt {P : MvPolynomial ι K} {i : ι}
    (h : pderiv i P ≠ 0) :
    (pderiv i P).totalDegree < P.totalDegree := by
  have hpos : 0 < P.totalDegree := by
    by_contra hz
    have hz' : P.totalDegree = 0 := Nat.eq_zero_of_not_pos hz
    rw [totalDegree_eq_zero_iff_eq_C] at hz'
    rw [hz', pderiv_C] at h
    exact h rfl
  exact lt_of_le_of_lt (totalDegree_pderiv_le P i) (Nat.sub_one_lt hpos.ne')

omit [Fintype ι] in
theorem coeff_sub_single_pderiv (P : MvPolynomial ι K) {s : ι →₀ ℕ}
    (hs : s ∈ P.support) {i : ι} (hi : s i ≠ 0) :
    coeff (s - Finsupp.single i 1) (pderiv i P) = coeff s P * (s i : K) := by
  classical
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, coeff_sum, pderiv_monomial, coeff_monomial]
  rw [Finset.sum_eq_single s]
  · simp
  · intro v hv hvs
    by_cases hvi : v i = 0
    · simp [hvi]
    · have hsub : v - Finsupp.single i 1 ≠ s - Finsupp.single i 1 := by
        intro heq
        have hadd := congrArg (fun u : ι →₀ ℕ => u + Finsupp.single i 1) heq
        change (v - Finsupp.single i 1) + Finsupp.single i 1 =
          (s - Finsupp.single i 1) + Finsupp.single i 1 at hadd
        rw [Finsupp.sub_add_single_one_cancel hvi,
          Finsupp.sub_add_single_one_cancel hi] at hadd
        exact hvs hadd
      simp [hsub]
  · intro hnot
    exact (hnot hs).elim

noncomputable def polynomialJacobianMinor (f : ι → MvPolynomial σ K)
    (coordinate : ι → σ) : Matrix ι ι (MvPolynomial σ K) :=
  fun j i => pderiv (coordinate j) (f i)

theorem algebraicIndependent_of_jacobian_det_ne_zero
    (f : ι → MvPolynomial σ K) (coordinate : ι → σ)
    (hdet : (polynomialJacobianMinor f coordinate).det ≠ 0) :
    AlgebraicIndependent K f := by
  classical
  rw [algebraicIndependent_iff]
  intro P
  generalize hP : P.totalDegree = d
  induction d using Nat.strong_induction_on generalizing P with
  | h d ih =>
      intro hrel
      have hchain :
          polynomialJacobianMinor f coordinate *ᵥ
              (fun i => aeval f (pderiv i P)) = 0 := by
        funext j
        have hp := congrArg (pderiv (coordinate j)) hrel
        rw [map_zero] at hp
        simpa [polynomialJacobianMinor, Matrix.mulVec, dotProduct, mul_comm] using
          (pderiv_aeval_chain f P (coordinate j)).symm.trans hp
      have hgrad : (fun i => aeval f (pderiv i P)) = 0 :=
        Matrix.eq_zero_of_mulVec_eq_zero hdet hchain
      have hpderiv : ∀ i, pderiv i P = 0 := by
        intro i
        by_contra hne
        have hlt : (pderiv i P).totalDegree < d := by
          rw [← hP]
          exact totalDegree_pderiv_lt hne
        apply hne
        exact ih (pderiv i P).totalDegree hlt (pderiv i P) rfl (congrFun hgrad i)
      have hdegree : P.totalDegree = 0 := by
        by_contra hne
        have hpos : 0 < P.totalDegree := Nat.pos_of_ne_zero hne
        have hPne : P ≠ 0 := by
          intro hpzero
          simp [hpzero] at hpos
        obtain ⟨s, hs, hsum⟩ :=
          P.support.exists_mem_eq_sup (Finsupp.support_nonempty_iff.mpr hPne)
            (fun s => s.sum fun _ e => e)
        have hsumpos : 0 < s.sum (fun _ e => e) := by
          rw [totalDegree, hsum] at hpos
          exact hpos
        obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
          by_contra hall
          push Not at hall
          have hs0 : s = 0 := Finsupp.ext fun i => hall i
          simp [hs0] at hsumpos
        have hcoeff := congrArg (coeff (s - Finsupp.single i 1)) (hpderiv i)
        simp only [coeff_zero] at hcoeff
        rw [coeff_sub_single_pderiv P hs hi] at hcoeff
        exact (mul_ne_zero (mem_support_iff.mp hs) (Nat.cast_ne_zero.mpr hi)) hcoeff
      rw [totalDegree_eq_zero_iff_eq_C.mp hdegree] at hrel ⊢
      simpa using hrel

end MvPolynomial

