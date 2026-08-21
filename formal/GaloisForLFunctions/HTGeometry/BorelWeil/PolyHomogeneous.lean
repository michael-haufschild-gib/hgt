/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.BorelWeil.PolySections
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Homogeneity and finite dimensionality of the Borel–Weil sections

A section of the Borel–Weil line bundle attached to `lam` is homogeneous of degree `∑ i, lam i`:
this is the scalar case `B = t • 1` of the `B`-equivariance.  Consequently the section space sits
inside a finitely generated homogeneous piece of the polynomial ring, hence is finite dimensional.

## Main results

* `eval_smul_of_isHomogeneous` — homogeneous polynomials scale under scaling of the argument.
* `isHomogeneous_of_eval_smul` — the converse over an infinite field.
* `polySections_le_homogeneousSubmodule`
* `finiteDimensional_polySections`
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

/-- A homogeneous polynomial of degree `e` scales by `t ^ e` when the argument is scaled. -/
theorem eval_smul_of_isHomogeneous {σ : Type*} [Fintype σ] {k : Type*} [CommSemiring k]
    {q : MvPolynomial σ k} {e : ℕ} (hq : q.IsHomogeneous e) (t : k) (x : σ → k) :
    MvPolynomial.eval (fun i => t * x i) q = t ^ e * MvPolynomial.eval x q := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hcoef : MvPolynomial.coeff d q ≠ 0 := by rwa [← MvPolynomial.mem_support_iff]
  have hsum : (∑ i : σ, d i) = e := by
    have hw := hq hcoef
    rw [Finsupp.weight_apply] at hw
    rw [← hw, Finsupp.sum_fintype] <;> simp
  calc MvPolynomial.coeff d q * ∏ i : σ, (t * x i) ^ (d i)
      = MvPolynomial.coeff d q * (t ^ (∑ i : σ, d i) * ∏ i : σ, (x i) ^ (d i)) := by
        rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
        exact congrArg _ (Finset.prod_congr rfl fun i _ => mul_pow _ _ _)
    _ = t ^ e * (MvPolynomial.coeff d q * ∏ i : σ, (x i) ^ (d i)) := by rw [hsum]; ring

/-- Over an infinite field, a polynomial whose evaluations scale by a fixed power is homogeneous of
that degree. -/
theorem isHomogeneous_of_eval_smul {σ : Type*} [Fintype σ] {k : Type*} [Field k] [Infinite k]
    {p : MvPolynomial σ k} {d : ℕ}
    (h : ∀ t : k, t ≠ 0 → ∀ x : σ → k,
      MvPolynomial.eval (fun i => t * x i) p = t ^ d * MvPolynomial.eval x p) :
    p.IsHomogeneous d := by
  classical
  set M := p.totalDegree with hM
  have hcomp : ∀ e : ℕ, e ≠ d → MvPolynomial.homogeneousComponent e p = 0 := by
    intro e he
    refine (MvPolynomial.homogeneousComponent_isHomogeneous e
      p).eq_zero_of_forall_eval_eq_zero fun x => ?_
    by_cases hle : e ≤ M
    · -- compare the two one-variable polynomials in the scaling parameter
      set a : ℕ → k := fun e' => MvPolynomial.eval x (MvPolynomial.homogeneousComponent e' p)
        with ha
      set A : Polynomial k :=
        ∑ e' ∈ Finset.range (M + 1), Polynomial.C (a e') * Polynomial.X ^ e' with hA
      set B : Polynomial k := Polynomial.C (MvPolynomial.eval x p) * Polynomial.X ^ d with hB
      have hAB : A = B := by
        refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
        refine Set.Infinite.mono ?_ ((Set.finite_singleton (0 : k)).infinite_compl)
        intro t ht
        have ht0 : t ≠ 0 := ht
        have hsplit : MvPolynomial.eval (fun i => t * x i) p
            = ∑ e' ∈ Finset.range (M + 1),
              t ^ e' * MvPolynomial.eval x (MvPolynomial.homogeneousComponent e' p) := by
          conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p, ← hM]
          rw [map_sum]
          exact Finset.sum_congr rfl fun e' _ =>
            eval_smul_of_isHomogeneous (MvPolynomial.homogeneousComponent_isHomogeneous e' p) t x
        have hp : MvPolynomial.eval x p
            = ∑ e' ∈ Finset.range (M + 1),
              MvPolynomial.eval x (MvPolynomial.homogeneousComponent e' p) := by
          conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p, ← hM]
          rw [map_sum]
        simp only [Set.mem_setOf_eq, hA, hB, Polynomial.eval_finsetSum, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        rw [show (MvPolynomial.eval x) p * t ^ d = t ^ d * (MvPolynomial.eval x) p from
            mul_comm _ _, ← h t ht0 x, hsplit]
        exact Finset.sum_congr rfl fun e' _ => by rw [ha]; ring
      have hcA : A.coeff e = a e := by
        rw [hA, Polynomial.finsetSum_coeff]
        rw [Finset.sum_eq_single e]
        · simp
        · intro e' _ hne
          simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hne]
        · intro hnot
          exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hle)) hnot
      have hcB : B.coeff e = 0 := by
        rw [hB, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg he, mul_zero]
      rw [hAB, hcB] at hcA
      exact hcA.symm
    · rw [MvPolynomial.homogeneousComponent_eq_zero e p (by omega)]
      simp
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p, ← hM]
  refine MvPolynomial.IsHomogeneous.sum _ _ d fun e _ => ?_
  by_cases he : e = d
  · subst he
    exact MvPolynomial.homogeneousComponent_isHomogeneous e p
  · rw [hcomp e he]
    exact MvPolynomial.isHomogeneous_zero _ _ _

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] {k : Type*} [Field k]

/-- **Sections are homogeneous** of degree `∑ i, lam i`. -/
theorem polySections_le_homogeneousSubmodule [Infinite k] (lam : n → ℕ) :
    polySections lam ≤ MvPolynomial.homogeneousSubmodule (n × n) k (∑ i, lam i) := by
  intro p hp
  rw [MvPolynomial.mem_homogeneousSubmodule]
  refine isHomogeneous_of_eval_smul fun t ht x => ?_
  have hkey := hp (Matrix.of fun i j => x (i, j)) (t • (1 : Matrix n n k))
    (IsBorelMat.smul_one ht)
  rw [borelCharMat_smul_one] at hkey
  have hmat : ((Matrix.of fun i j => x (i, j) : Matrix n n k) * (t • (1 : Matrix n n k)))
      = Matrix.of fun i j => t * x (i, j) := by
    ext i j
    simp [Matrix.mul_smul, Matrix.mul_one, mul_comm]
  rw [hmat] at hkey
  simpa [matEval] using hkey

/-- **Finite dimensionality of the Borel–Weil sections.** -/
instance finiteDimensional_polySections [Infinite k] (lam : n → ℕ) :
    FiniteDimensional k (polySections (k := k) lam) := by
  have hfg : (MvPolynomial.homogeneousSubmodule (n × n) k (∑ i, lam i)).FG :=
    MvPolynomial.homogeneousSubmodule_fg (n × n) k (∑ i, lam i)
  have : FiniteDimensional k (MvPolynomial.homogeneousSubmodule (n × n) k (∑ i, lam i)) :=
    Module.Finite.iff_fg.mpr hfg
  exact Submodule.finiteDimensional_of_le (polySections_le_homogeneousSubmodule lam)

end GaloisForLFunctions.HTGeometry.BorelWeil
