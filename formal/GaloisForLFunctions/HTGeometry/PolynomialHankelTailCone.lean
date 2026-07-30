import GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity

/-!
# Polynomial coefficient energy controls Hankel tails

A polynomial square has antidiagonal convolution coefficients.  Young's elementary inequality
controls each such coefficient by twice the total squared coefficient energy.  Consequently an
absolutely summable nonconstant moment tail perturbs the vacuum Hankel term by at most twice that
energy times the tail mass.

This finite-polynomial estimate is independent of any representing measure.  It is intended for
moment sequences whose vacuum coordinate is positive while the remaining coordinates are known
only through an absolute summability estimate.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

noncomputable section

/-- Squared `ℓ²` energy of the nonconstant coefficients of a real polynomial. -/
def polynomialNonconstantCoeffSqEnergy (p : Polynomial ℝ) : ℝ :=
  ∑ k ∈ Finset.range p.natDegree, (p.coeff (k + 1)) ^ 2

/-- Total squared `ℓ²` energy of the coefficients of a real polynomial. -/
def polynomialCoeffSqEnergy (p : Polynomial ℝ) : ℝ :=
  (p.coeff 0) ^ 2 + polynomialNonconstantCoeffSqEnergy p

theorem polynomialCoeffSqEnergy_nonneg (p : Polynomial ℝ) :
    0 ≤ polynomialCoeffSqEnergy p := by
  unfold polynomialCoeffSqEnergy polynomialNonconstantCoeffSqEnergy
  positivity

private theorem summable_coeff_sq (p : Polynomial ℝ) :
    Summable (fun k : ℕ => (p.coeff k) ^ 2) := by
  apply summable_of_ne_finset_zero (s := p.support)
  intro k hk
  have hz : p.coeff k = 0 := by
    simpa only [Polynomial.mem_support_iff, not_not] using hk
  simp [hz]

/-- The total coefficient energy is the sum of the coefficient-square series. -/
theorem tsum_coeff_sq_eq_polynomialCoeffSqEnergy (p : Polynomial ℝ) :
    (∑' k : ℕ, (p.coeff k) ^ 2) = polynomialCoeffSqEnergy p := by
  rw [tsum_eq_sum (s := Finset.range (p.natDegree + 1)) (fun k hk => by
    have hdeg : p.natDegree < k := by simpa using hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg]
    simp)]
  rw [Finset.sum_range_succ']
  unfold polynomialCoeffSqEnergy polynomialNonconstantCoeffSqEnergy
  ring

theorem sum_range_coeff_sq_le_polynomialCoeffSqEnergy
    (p : Polynomial ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (p.coeff k) ^ 2) ≤
      polynomialCoeffSqEnergy p := by
  calc
    (∑ k ∈ Finset.range N, (p.coeff k) ^ 2) ≤
        ∑' k : ℕ, (p.coeff k) ^ 2 :=
      (summable_coeff_sq p).sum_le_tsum _ (fun k _ => sq_nonneg (p.coeff k))
    _ = polynomialCoeffSqEnergy p :=
      tsum_coeff_sq_eq_polynomialCoeffSqEnergy p

/-- Every antidiagonal coefficient of `p²` is controlled by twice the full coefficient energy. -/
theorem abs_coeff_sq_le_two_mul_polynomialCoeffSqEnergy
    (p : Polynomial ℝ) (n : ℕ) :
    |(p ^ 2).coeff n| ≤ 2 * polynomialCoeffSqEnergy p := by
  rw [pow_two, Polynomial.coeff_mul]
  calc
    |∑ x ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) n,
        p.coeff x.1 * p.coeff x.2| ≤
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) n,
          |p.coeff x.1 * p.coeff x.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) n,
          ((p.coeff x.1) ^ 2 + (p.coeff x.2) ^ 2) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [abs_mul]
      calc
        |p.coeff x.1| * |p.coeff x.2| ≤
            (|p.coeff x.1| ^ 2 + |p.coeff x.2| ^ 2) / 2 := by
          nlinarith [sq_nonneg (|p.coeff x.1| - |p.coeff x.2|)]
        _ ≤ (p.coeff x.1) ^ 2 + (p.coeff x.2) ^ 2 := by
          rw [sq_abs, sq_abs]
          nlinarith [sq_nonneg (p.coeff x.1), sq_nonneg (p.coeff x.2)]
    _ = (∑ k ∈ Finset.range (n + 1), (p.coeff k) ^ 2) +
          ∑ k ∈ Finset.range (n + 1), (p.coeff k) ^ 2 := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.Nat.antidiagonal_eq_map]
        simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
      · rw [Finset.Nat.antidiagonal_eq_map']
        simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
    _ ≤ polynomialCoeffSqEnergy p + polynomialCoeffSqEnergy p := by
      gcongr <;> exact sum_range_coeff_sq_le_polynomialCoeffSqEnergy p (n + 1)
    _ = 2 * polynomialCoeffSqEnergy p := by ring

/-- A summable nonconstant moment tail perturbs the vacuum square term by at most twice the
polynomial coefficient energy times the absolute tail mass. -/
theorem abs_momentFunctional_sq_sub_vacuum_le
    (s : ℕ → ℝ) (p : Polynomial ℝ) {B : ℝ}
    (hsum : Summable (fun n : ℕ => |s (n + 1)|))
    (htail : (∑' n : ℕ, |s (n + 1)|) ≤ B) :
    |momentFunctional s (p ^ 2) - (p.coeff 0) ^ 2 * s 0| ≤
      2 * polynomialCoeffSqEnergy p * B := by
  have hrange := (p ^ 2).sum_over_range
    (f := fun k c => c * s k) (by simp)
  rw [Polynomial.sum_def] at hrange
  have hcoeff0 : (p ^ 2).coeff 0 = (p.coeff 0) ^ 2 := by
    simp [Polynomial.coeff_zero_eq_eval_zero]
  rw [momentFunctional_eq_support_sum, hrange, Finset.sum_range_succ']
  rw [hcoeff0]
  ring_nf
  have hindex :
      (∑ k ∈ Finset.range (p ^ 2).natDegree,
          (p ^ 2).coeff (1 + k) * s (1 + k)) =
        ∑ k ∈ Finset.range (p ^ 2).natDegree,
          (p ^ 2).coeff (k + 1) * s (k + 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [add_comm 1 k]
  rw [hindex]
  have hbound :
      |∑ k ∈ Finset.range (p ^ 2).natDegree,
          (p ^ 2).coeff (k + 1) * s (k + 1)| ≤
        2 * polynomialCoeffSqEnergy p * B := by
    calc
      |∑ k ∈ Finset.range (p ^ 2).natDegree,
          (p ^ 2).coeff (k + 1) * s (k + 1)| ≤
          ∑ k ∈ Finset.range (p ^ 2).natDegree,
            |(p ^ 2).coeff (k + 1) * s (k + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (p ^ 2).natDegree,
            (2 * polynomialCoeffSqEnergy p) * |s (k + 1)| := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (abs_coeff_sq_le_two_mul_polynomialCoeffSqEnergy p (k + 1))
          (abs_nonneg _)
      _ = (2 * polynomialCoeffSqEnergy p) *
            ∑ k ∈ Finset.range (p ^ 2).natDegree, |s (k + 1)| := by
        rw [Finset.mul_sum]
      _ ≤ (2 * polynomialCoeffSqEnergy p) * ∑' k : ℕ, |s (k + 1)| := by
        exact mul_le_mul_of_nonneg_left
          (hsum.sum_le_tsum _ (fun k _ => abs_nonneg _))
          (mul_nonneg (by norm_num) (polynomialCoeffSqEnergy_nonneg p))
      _ ≤ 2 * polynomialCoeffSqEnergy p * B := by
        exact mul_le_mul_of_nonneg_left htail
          (mul_nonneg (by norm_num) (polynomialCoeffSqEnergy_nonneg p))
  simpa [mul_assoc, mul_comm, mul_left_comm] using hbound

end

end HTGeometry
