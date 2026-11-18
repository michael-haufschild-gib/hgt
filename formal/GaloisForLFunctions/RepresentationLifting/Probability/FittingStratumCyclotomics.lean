import GaloisForLFunctions.RepresentationLifting.Probability.FittingStratumZeta
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Cyclotomic factors of Fitting-stratum counts

Splitting each factor of the counting polynomial identifies the affine degree, the
roots of unity, and the leading coefficient at field size one.
-/

namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels
open Finset Polynomial
open scoped Classical
noncomputable section

/-- Exponent of the pure affine factor in the stratum. -/
def fittingAffineDegree (d k : ℕ) := d*(d-1)+∑ j ∈ range k, (d+j)

theorem fittingPolynomial_split (d k : ℕ) : fittingPolynomial d k =
    X^(fittingAffineDegree d k)*∏ j ∈ range k, (X^(d+j+1)-1) := by
  induction k with
  | zero => simp [fittingPolynomial,fittingAffineDegree]
  | succ k ih =>
    rw [fittingPolynomial,ih,prod_range_succ]
    have he : fittingAffineDegree d (k+1) = fittingAffineDegree d k+(d+k) := by
      simp [fittingAffineDegree,sum_range_succ,Nat.add_assoc]
    rw [he,pow_add]
    ring

/-- All nonzero roots of a Fitting-stratum count polynomial are roots of unity
whose order divides some dimension strictly between d and the ambient rank,
including the upper endpoint. This gives its full integral factorization. -/
theorem fittingPolynomial_cyclotomic (d k : ℕ) : fittingPolynomial d k =
    X^(fittingAffineDegree d k)*
      ∏ j ∈ range k, ∏ m ∈ (d+j+1).divisors, cyclotomic m ℤ := by
  rw [fittingPolynomial_split]
  simp only [prod_cyclotomic_eq_X_pow_sub_one (Nat.succ_pos _)]

theorem fittingPolynomial_monic (d k : ℕ) : (fittingPolynomial d k).Monic := by
  induction k with
  | zero => exact monic_X_pow _
  | succ k ih =>
    exact ((monic_X_pow _).mul (by simpa using monic_X_pow_sub_C (1:ℤ) (Nat.succ_ne_zero (d+k)))).mul ih

/-- A generalized zero-eigenspace of dimension d imposes exactly d powers
of field size in the leading asymptotic count of square matrices. -/
theorem fittingPolynomial_natDegree (d k : ℕ) : (fittingPolynomial d k).natDegree+d = (d+k)^2 := by
  induction k with
  | zero =>
    simp only [fittingPolynomial,natDegree_X_pow,Nat.add_zero]
    cases d with
    | zero => rfl
    | succ d => simp only [Nat.add_sub_cancel]; ring
  | succ k ih =>
    have hu : ((X:ℤ[X])^(d+k+1)-1).Monic := by
      simpa using monic_X_pow_sub_C (1:ℤ) (Nat.succ_ne_zero (d+k))
    have he : ((X:ℤ[X])^(d+k+1)-1).natDegree = d+k+1 := by
      simpa using (natDegree_X_pow_sub_C (r := (1:ℤ)) (n := d+k+1))
    rw [fittingPolynomial,natDegree_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hu.ne_zero)
      (fittingPolynomial_monic d k).ne_zero,natDegree_mul (pow_ne_zero _ X_ne_zero) hu.ne_zero,natDegree_X_pow,he]
    calc
      _ = (d+k+(d+k+1))+((fittingPolynomial d k).natDegree+d) := by omega
      _ = _ := by rw [ih]; ring

/-- Quotient after removing all (X-1) factors; its value at one is a
strictly positive rising factorial. -/
def fittingReducedAtOne (d k : ℕ) : ℤ[X] := X^(fittingAffineDegree d k)*
  ∏ j ∈ range k, ∑ m ∈ range (d+j+1), X^m

theorem fittingPolynomial_split_at_one (d k : ℕ) :
    fittingPolynomial d k = fittingReducedAtOne d k*(X-1)^k := by
  rw [fittingPolynomial_split,fittingReducedAtOne,mul_assoc]
  congr 1
  have he (j : ℕ) : (X:ℤ[X])^(d+j+1)-1 =
      (∑ m ∈ range (d+j+1), X^m)*(X-1) := (geom_sum_mul X _).symm
  simp_rw [he]
  rw [prod_mul_distrib,prod_const,card_range]

theorem fittingReducedAtOne_eval (d k : ℕ) :
    (fittingReducedAtOne d k).eval 1 = ((d+1).ascFactorial k:ℤ) := by
  simp only [fittingReducedAtOne,eval_mul,eval_pow,eval_X,one_pow,one_mul,eval_prod,eval_finsetSum,
    sum_const,card_range,nsmul_eq_mul,mul_one]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ,ih,Nat.ascFactorial_succ,Nat.cast_mul]
    push_cast
    ring

/-- Vanishing order at field size one records the dimension of the invertible
part, including the rank-zero and nilpotent strata. -/
theorem fittingPolynomial_order_one (d k : ℕ) :
    (fittingPolynomial d k).rootMultiplicity 1 = k := by
  have hv : (fittingReducedAtOne d k).eval 1 ≠ 0 := by
    rw [fittingReducedAtOne_eval]
    exact_mod_cast (Nat.ascFactorial_pos d k).ne'
  have hn : fittingReducedAtOne d k ≠ 0 := fun h => hv (by rw [h,eval_zero])
  rw [fittingPolynomial_split_at_one,show (1:ℤ[X])=C 1 from C_1.symm,
    rootMultiplicity_mul_X_sub_C_pow hn,rootMultiplicity_eq_zero hv,zero_add]

/-- Testing a nonzero root of unity detects exactly which dimensions in the
stratum interval are divisible by its order. -/
theorem fittingPolynomial_rootOfUnity {z : ℂ} {m : ℕ} (hm : 0 < m) (hz : IsPrimitiveRoot z m)
    (d k : ℕ) : (fittingPolynomial d k).eval₂ (Int.castRingHom ℂ) z = 0 ↔
      ∃ j ∈ range k, m ∣ d+j+1 := by
  rw [fittingPolynomial_split,eval₂_mul,eval₂_pow,eval₂_X,eval₂_finsetProd]
  simp only [mul_eq_zero,pow_ne_zero _ (hz.ne_zero hm.ne'),false_or,Finset.prod_eq_zero_iff,
    eval₂_sub,eval₂_one,eval₂_pow,eval₂_X,sub_eq_zero,hz.pow_eq_one_iff_dvd]

end
end GaloisForLFunctions.RepresentationLifting.OperatorKernels
