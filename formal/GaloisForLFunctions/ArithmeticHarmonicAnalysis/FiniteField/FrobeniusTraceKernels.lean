import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTracePolynomialDegree
import Mathlib.FieldTheory.Finite.GaloisField


/-!
# Kernels of relative Frobenius traces

A zero of the relative trace is fixed by the full Frobenius period.
The trace polynomial divides the full Frobenius polynomial and has
unit derivative; over a field of the full period its kernel therefore
has exactly the degree of the trace polynomial.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Polynomial
variable (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [CharP K p]

omit [Fact p.Prime] in
/-- Ring homomorphisms commute with every relative Frobenius trace. -/
theorem frobeniusTraceSum_map {A B : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (d m : ℕ) (x : A) :
    f (frobeniusTraceSum p d m x) = frobeniusTraceSum p d m (f x) := by
  simp only [frobeniusTraceSum, map_sum, map_pow]

omit [Fact p.Prime] [CharP K p] in
/-- Scalars fixed by the short Frobenius pass through the relative trace. -/
theorem frobeniusTraceSum_mul_of_fixed (d m : ℕ) (a x : K)
    (ha : a ^ p ^ d = a) :
    frobeniusTraceSum p d m (a * x) = a * frobeniusTraceSum p d m x := by
  have hj (j : ℕ) : a ^ p ^ (d * j) = a := by
    induction j with
    | zero => simp only [Nat.mul_zero, pow_zero, pow_one]
    | succ j ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, ha]
  simp only [frobeniusTraceSum, mul_pow, hj, Finset.mul_sum]

/-- Fixed scaling and a trace-zero translation act linearly on the trace coordinate. -/
theorem frobeniusTraceSum_affine (d m : ℕ) (a b x : K)
    (ha : a ^ p ^ d = a) (hb : frobeniusTraceSum p d m b = 0) :
    frobeniusTraceSum p d m (a * x + b) = a * frobeniusTraceSum p d m x := by
  rw [frobeniusTraceSum_add, frobeniusTraceSum_mul_of_fixed p d m a x ha, hb, add_zero]

/-- Every zero of the relative trace is fixed by the full Frobenius period. -/
theorem frobeniusTraceSum_zero_fixed (d m : ℕ) {x : K}
    (hx : frobeniusTraceSum p (d + 1) (m + 1) x = 0) :
    x ^ p ^ ((d + 1) * (m + 1)) = x := by
  have h := frobeniusTraceSum_sub_pow p (d + 1) (m + 1) x
  rw [hx, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), sub_self] at h
  exact (sub_eq_zero.mp h.symm).symm

omit [Fact p.Prime] in
/-- The relative trace polynomial is separable in its defining characteristic. -/
theorem frobeniusTraceSum_polynomial_separable (d m : ℕ) :
    (frobeniusTraceSum p (d + 1) (m + 1) (X : K[X])).Separable := by
  rw [separable_def, frobeniusTraceSum_polynomial_derivative]
  exact isCoprime_one_right

/-- Over a field of the full Frobenius period, the relative trace polynomial splits. -/
theorem frobeniusTraceSum_polynomial_splits [Finite K] (d m : ℕ)
    (hcard : Nat.card K = p ^ ((d + 1) * (m + 1))) :
    (frobeniusTraceSum p (d + 1) (m + 1) (X : K[X])).Splits := by
  let P := frobeniusTraceSum p (d + 1) (m + 1) (X : K[X])
  have hq : 0 < p ^ (d + 1) := pow_pos (Fact.out : p.Prime).pos _
  have htel : X ^ p ^ ((d + 1) * (m + 1)) - X = P ^ p ^ (d + 1) - P := by
    have h := frobeniusTraceSum_sub_pow p (d + 1) (m + 1) (X : K[X])
    change P - P ^ p ^ (d + 1) = X - X ^ p ^ ((d + 1) * (m + 1)) at h
    simpa only [neg_sub] using congrArg Neg.neg h.symm
  have hdvd : P ∣ X ^ p ^ ((d + 1) * (m + 1)) - X := by
    rw [htel]
    refine ⟨P ^ (p ^ (d + 1) - 1) - 1, ?_⟩
    rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hq]
  have hQ : 1 < p ^ ((d + 1) * (m + 1)) := Nat.one_lt_pow
    (Nat.mul_ne_zero (Nat.succ_ne_zero d) (Nat.succ_ne_zero m)) (Fact.out : p.Prime).one_lt
  have hne : (X ^ p ^ ((d + 1) * (m + 1)) - X : K[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun f : K[X] => f.coeff (p ^ ((d + 1) * (m + 1)))) h
    simp only [coeff_sub, coeff_X_pow_self, coeff_X,
      if_neg (Ne.symm (ne_of_gt hQ)), sub_zero, coeff_zero] at hc
    exact one_ne_zero hc
  have hs : (X ^ p ^ ((d + 1) * (m + 1)) - X : K[X]).Splits := by
    rw [← hcard]
    exact splits_X_pow_nat_card_sub_X
  exact hs.of_dvd hne hdvd

/-- The relative trace kernel has the exact expected size over its full-period finite field. -/
theorem frobeniusTraceSum_kernel_card [Finite K] (d m : ℕ)
    (hcard : Nat.card K = p ^ ((d + 1) * (m + 1))) :
    Nat.card {x : K // frobeniusTraceSum p (d + 1) (m + 1) x = 0} =
      p ^ ((d + 1) * m) := by
  classical
  let P := frobeniusTraceSum p (d + 1) (m + 1) (X : K[X])
  have hP : P ≠ 0 := (frobeniusTraceSum_polynomial_monic p d m).ne_zero
  have he : {x : K // frobeniusTraceSum p (d + 1) (m + 1) x = 0} ≃ P.rootSet K :=
    Equiv.subtypeEquivRight (fun x => by
      rw [mem_rootSet, and_iff_right hP]
      simp only [P, frobeniusTraceSum, map_sum, map_pow, aeval_X])
  rw [Nat.card_congr he, Nat.card_eq_fintype_card,
    card_rootSet_eq_natDegree (frobeniusTraceSum_polynomial_separable p d m)
      (by simpa only [Algebra.algebraMap_self, Polynomial.map_id] using
        frobeniusTraceSum_polynomial_splits (K := K) p d m hcard)]
  exact frobeniusTraceSum_polynomial_natDegree p d m

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
