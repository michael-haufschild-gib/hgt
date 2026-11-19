import GaloisForLFunctions.HTGeometry.PolynomialShiftDifference
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Changing the step of factorial polynomials

The generalized Stirling recurrence of Adiya et al. (arXiv:2611.21429, Lemma 2.1)
changes between two Newton bases. Steps `a = -h*s` and `b = h*(1-s)` give
their coefficients. Allowing any complex steps includes coincident nodes,
ordinary powers, and reversed progressions. Composition and inversion follow
from uniqueness of coordinates, including at the degenerate step zero.
-/

open Polynomial Finset
open GaloisForLFunctions.HTGeometry

namespace FiniteFreeProbability

noncomputable section

private def predecessor (f : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | k+1 => f k

/-- Connection coefficients from the falling-factorial step `a` to the step `b`. -/
def factorialConnection (a b : ℂ) : ℕ → ℕ → ℂ
  | 0, k => if k = 0 then 1 else 0
  | n+1, k => predecessor (factorialConnection a b n) k +
      ((k : ℂ)*b - (n : ℂ)*a) * factorialConnection a b n k

private theorem connection_above (a b : ℂ) (n k : ℕ) (h : n < k) :
    factorialConnection a b n k = 0 := by
  induction n generalizing k with
  | zero => simp [factorialConnection, h.ne']
  | succ n ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [factorialConnection, predecessor, ih k (by omega), ih (k+1) (by omega), mul_zero, add_zero]

private theorem connection_diagonal (a b : ℂ) (n : ℕ) : factorialConnection a b n n = 1 := by
  induction n with
  | zero => simp [factorialConnection]
  | succ n ih => rw [factorialConnection, predecessor, ih, connection_above _ _ _ _ (by omega),
      mul_zero, add_zero]

/-- The finite change of basis; no division by either step occurs. -/
theorem fallPoly_change_step (a b : ℂ) (n : ℕ) :
    fallPoly a n = ∑ k ∈ range (n+1), C (factorialConnection a b n k) * fallPoly b k := by
  induction n with
  | zero => simp [factorialConnection]
  | succ n ih =>
    let c := factorialConnection a b n
    have step (k : ℕ) : C (c k) * fallPoly b k * (X - C ((n : ℂ)*a)) =
        C (c k) * fallPoly b (k+1) + C (((k : ℂ)*b-(n : ℂ)*a)*c k) * fallPoly b k := by
      simp only [fallPoly_succ, map_mul, map_sub]
      ring
    rw [fallPoly_succ, ih, Finset.sum_mul]
    change ∑ k ∈ range (n+1), C (c k) * fallPoly b k * (X - C ((n : ℂ)*a)) = _
    change _ = ∑ k ∈ range (n+1+1), C (predecessor c k +
      ((k : ℂ)*b-(n : ℂ)*a)*c k) * fallPoly b k
    simp_rw [step]
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_range_succ' (fun k => C (predecessor c k) * fallPoly b k)]
      simp [predecessor]
    · rw [Finset.sum_range_succ (fun k => C (((k : ℂ)*b-(n : ℂ)*a)*c k) * fallPoly b k) (n+1)]
      simp [c, connection_above a b n (n+1) (by omega)]

private def factorialSequence (b : ℂ) : Polynomial.Sequence ℂ where
  elems' := fallPoly b
  degree_eq' n := by rw [degree_eq_natDegree (monic_fallPoly b n).ne_zero, natDegree_fallPoly]

private def factorialBasis (b : ℂ) : Module.Basis ℕ ℂ ℂ[X] :=
  (factorialSequence b).basis fun i => by
    change IsUnit (fallPoly b i).leadingCoeff
    rw [(monic_fallPoly b i).leadingCoeff]
    exact isUnit_one

private theorem basis_apply (b : ℂ) (k : ℕ) : factorialBasis b k = fallPoly b k :=
  Polynomial.Sequence.basis_eq_self _ _ _

private theorem coordinate (a b : ℂ) (n j : ℕ) :
    (factorialBasis b).repr (fallPoly a n) j = factorialConnection a b n j := by
  classical
  rw [fallPoly_change_step a b, map_sum, Finsupp.finsetSum_apply]
  simp_rw [← smul_eq_C_mul, map_smul, Finsupp.smul_apply, ← basis_apply b,
    Module.Basis.repr_self_apply]
  by_cases hj : j ∈ range (n+1)
  · simp [hj, smul_eq_mul, mul_ite]
  · simp [hj, smul_eq_mul, mul_ite, connection_above a b n j (by simpa using hj)]

/-- Changing steps through an arbitrary third step gives exactly the same signed row. -/
theorem factorialConnection_comp (a b c : ℂ) (n j : ℕ) :
    ∑ k ∈ range (n+1), factorialConnection a b n k * factorialConnection b c k j =
      factorialConnection a c n j := by
  rw [← coordinate a c n j, fallPoly_change_step a b, map_sum, Finsupp.finsetSum_apply]
  simp only [← smul_eq_C_mul, map_smul, Finsupp.smul_apply, smul_eq_mul, coordinate]

/-- Reversing the step change gives the exact triangular inverse. -/
theorem factorialConnection_inverse (a b : ℂ) (n j : ℕ) :
    ∑ k ∈ range (n+1), factorialConnection a b n k * factorialConnection b a k j =
      if n = j then 1 else 0 := by
  rw [factorialConnection_comp, ← coordinate, ← basis_apply a, Module.Basis.repr_self_apply]

/-- Evaluation transfers generalized Stirling rows to the eigenvalue of any Euler monomial. -/
theorem factorialConnection_spectral (a b z : ℂ) (n : ℕ) :
    ∏ i ∈ range n, (z - (i : ℂ)*a) =
      ∑ k ∈ range (n+1), factorialConnection a b n k * ∏ i ∈ range k, (z - (i : ℂ)*b) := by
  simpa only [fallPoly, eval_prod, eval_sub, eval_X, eval_C, eval_finsetSum, eval_mul] using
    congrArg (Polynomial.eval z) (fallPoly_change_step a b n)

private theorem difference_fall_succ (b : ℂ) (k : ℕ) :
    fwdDiff b (fallPoly b (k+1)).eval = (((k : ℂ)+1)*b) • (fallPoly b k).eval := by
  funext x
  have h := congrArg (Polynomial.eval x) (shiftDiff_fallPoly b k)
  simpa only [eval_sub, eval_comp, eval_add, eval_X, eval_C, eval_mul, Pi.smul_apply,
    smul_eq_mul, fwdDiff] using h

/-- Arbitrary forward differences act on the full stepped factorial basis by a single lowering. -/
theorem iterated_difference_fallPoly (b : ℂ) (r k : ℕ) (x : ℂ) :
    (fwdDiff b)^[r] (fallPoly b k).eval x =
      (k.descFactorial r : ℂ) * b^r * (fallPoly b (k-r)).eval x := by
  induction r generalizing k x with
  | zero => simp
  | succ r ih =>
    cases k with
    | zero =>
      rw [Function.iterate_succ_apply', fwdDiff, ih, ih, Nat.zero_descFactorial_succ]
      simp
    | succ k =>
      rw [Function.iterate_succ_apply, difference_fall_succ, fwdDiff_iter_const_smul,
        Pi.smul_apply, smul_eq_mul, ih, Nat.succ_descFactorial_succ, Nat.succ_sub_succ_eq_sub,
        pow_succ]
      push_cast
      ring

private theorem fall_at_origin (b : ℂ) (j : ℕ) :
    (fallPoly b j).eval 0 = if j = 0 then 1 else 0 := by
  cases j with
  | zero => simp
  | succ j =>
    rw [fallPoly, Finset.prod_range_succ']
    simp

private theorem difference_kronecker (b : ℂ) (r j : ℕ) :
    (fwdDiff b)^[r] (fallPoly b j).eval 0 = if j = r then (r.factorial : ℂ)*b^r else 0 := by
  rw [iterated_difference_fallPoly, fall_at_origin]
  rcases lt_trichotomy j r with h | rfl | h
  · simp [Nat.descFactorial_of_lt h, h.ne]
  · simp [Nat.descFactorial_self]
  · simp [h.ne', show j-r ≠ 0 by omega]

/-- A signed binomial sample recovers one connection coefficient, with exact normalization.
This includes zero step without dividing by it. -/
theorem factorialConnection_binomial_sample (a b : ℂ) (n r : ℕ) :
    ∑ j ∈ range (r+1), ((-1 : ℤ)^(r-j) * r.choose j) • (fallPoly a n).eval (j • b) =
      factorialConnection a b n r * (r.factorial : ℂ) * b^r := by
  classical
  have hrow : (fallPoly a n).eval = ∑ j ∈ range (n+1),
      factorialConnection a b n j • (fallPoly b j).eval := by
    funext x
    conv_lhs => rw [fallPoly_change_step a b]
    simp only [eval_finsetSum, eval_mul, eval_C, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h := fwdDiff_iter_eq_sum_shift b (fallPoly a n).eval r 0
  simp only [zero_add] at h
  rw [← h, hrow, fwdDiff_iter_finsetSum]
  simp only [Finset.sum_apply, fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul,
    difference_kronecker, mul_ite, mul_zero]
  by_cases hr : r ∈ range (n+1)
  · simp [hr, mul_assoc]
  · simp [hr, connection_above a b n r (by simpa using hr)]

#print axioms factorialConnection_binomial_sample
#print axioms factorialConnection_inverse
#print axioms factorialConnection_spectral

end

end FiniteFreeProbability
