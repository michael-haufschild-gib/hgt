import Mathlib

/-!
# The drift expansion of a polynomial

For a polynomial `P` of degree `n` the *shift difference* `P(y + a) - P(y)` is a polynomial in `y`
of degree `n - 1` whose coefficients are explicit polynomials in the shift `a`.  In characteristic
zero its top coefficient is `n · P.coeff n · a`, so a nonzero shift never degenerates the equation.

This is the algebraic engine of a polynomial divided difference.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {R : Type*} [CommRing R]

/-- The coefficient of `y ^ c` in `P (y + a) - P y`, as a polynomial in the shift `a`. -/
def driftCoeff (P : Polynomial R) (c : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.Ioc c P.natDegree, C (P.coeff k * (k.choose c : R)) * X ^ (k - c)

/-- **The drift expansion.**  The shift difference of a polynomial expands in the base point with
the drift coefficients. -/
theorem eval_driftCoeff_expansion (P : Polynomial R) (y a : R) :
    P.eval (y + a) - P.eval y
      = ∑ c ∈ Finset.range P.natDegree, ((driftCoeff P c).eval a) * y ^ c := by
  classical
  set n : ℕ := P.natDegree with hn
  have hshift : P.eval (y + a)
      = ∑ k ∈ Finset.range (n + 1), ∑ c ∈ Finset.range (k + 1),
          P.coeff k * (y ^ c * a ^ (k - c) * (k.choose c : R)) := by
    rw [Polynomial.eval_eq_sum_range]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [add_pow, Finset.mul_sum]
  have hbase : P.eval y = ∑ k ∈ Finset.range (n + 1), P.coeff k * y ^ k := by
    rw [Polynomial.eval_eq_sum_range]
  -- split off the diagonal term `c = k`
  have hsplit : ∀ k : ℕ, ∑ c ∈ Finset.range (k + 1),
      P.coeff k * (y ^ c * a ^ (k - c) * (k.choose c : R))
      = (∑ c ∈ Finset.range k, P.coeff k * (y ^ c * a ^ (k - c) * (k.choose c : R)))
        + P.coeff k * y ^ k := by
    intro k
    rw [Finset.sum_range_succ]
    congr 1
    rw [Nat.sub_self, pow_zero, Nat.choose_self]
    push_cast
    ring
  have hdiff : P.eval (y + a) - P.eval y
      = ∑ k ∈ Finset.range (n + 1), ∑ c ∈ Finset.range k,
          P.coeff k * (y ^ c * a ^ (k - c) * (k.choose c : R)) := by
    rw [hshift, hbase]
    rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib]
    ring
  rw [hdiff]
  -- swap the order of summation over the triangle
  have hcomm : ∑ k ∈ Finset.range (n + 1), ∑ c ∈ Finset.range k,
      P.coeff k * (y ^ c * a ^ (k - c) * (k.choose c : R))
      = ∑ c ∈ Finset.range n, ∑ k ∈ Finset.Ioc c n,
          P.coeff k * (y ^ c * a ^ (k - c) * (k.choose c : R)) := by
    refine Finset.sum_comm' ?_
    intro k c
    simp only [Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨hk, hc⟩
      exact ⟨⟨hc, by omega⟩, by omega⟩
    · rintro ⟨⟨hc, hk⟩, hcn⟩
      exact ⟨by omega, hc⟩
  rw [hcomm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [driftCoeff, Polynomial.eval_finsetSum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-- The top drift coefficient of a polynomial of degree at least two. -/
theorem driftCoeff_pred (P : Polynomial R) (hP : 1 ≤ P.natDegree) :
    driftCoeff P (P.natDegree - 1)
      = C (P.coeff P.natDegree * (P.natDegree : R)) * X := by
  classical
  have hIoc : Finset.Ioc (P.natDegree - 1) P.natDegree = {P.natDegree} := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_singleton]
    omega
  rw [driftCoeff, hIoc, Finset.sum_singleton]
  have hsub : P.natDegree - (P.natDegree - 1) = 1 := by omega
  have hchoose : P.natDegree.choose (P.natDegree - 1) = P.natDegree := by
    have hsym := Nat.choose_symm (show P.natDegree - 1 ≤ P.natDegree by omega)
      (n := P.natDegree)
    rw [hsub] at hsym
    rw [← hsym, Nat.choose_one_right]
  rw [hsub, hchoose, pow_one]

/-- The top drift coefficient evaluates to `n · lead · a`. -/
theorem eval_driftCoeff_pred (P : Polynomial R) (hP : 1 ≤ P.natDegree) (a : R) :
    (driftCoeff P (P.natDegree - 1)).eval a = (P.natDegree : R) * P.coeff P.natDegree * a := by
  rw [driftCoeff_pred P hP, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

end GaloisForLFunctions.HTGeometry
