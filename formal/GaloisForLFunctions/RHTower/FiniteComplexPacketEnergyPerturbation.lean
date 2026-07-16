import GaloisForLFunctions.RHTower.FiniteBernsteinCoordinatePacketAsymptotic

/-!
# Finite complex-packet energy perturbation

The change in square energy caused by adding a finite packet is bounded by the two packet `l1`
norms.  This elementary estimate transfers a sharp leading-packet asymptotic through an
exponentially smaller remainder.
-/

open Complex Filter Topology
open scoped BigOperators Real ComplexConjugate

namespace RHTower

noncomputable section

lemma abs_norm_add_sq_sub_norm_sq_le (x y : ℂ) :
    |‖x + y‖ ^ 2 - ‖x‖ ^ 2| ≤
      2 * ‖x‖ * ‖y‖ + ‖y‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_add]
  have hre : |(x * conj y).re| ≤ ‖x‖ * ‖y‖ := by
    calc
      |(x * conj y).re| ≤ ‖x * conj y‖ := abs_re_le_norm _
      _ = ‖x‖ * ‖y‖ := by rw [norm_mul, norm_conj]
  have hnormsq : |Complex.normSq y| = ‖y‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
  calc
    |Complex.normSq x + Complex.normSq y + 2 * (x * conj y).re -
        Complex.normSq x| = |Complex.normSq y + 2 * (x * conj y).re| := by ring_nf
    _ ≤ |Complex.normSq y| + |2 * (x * conj y).re| := abs_add_le _ _
    _ = ‖y‖ ^ 2 + 2 * |(x * conj y).re| := by rw [hnormsq, abs_mul]; norm_num
    _ ≤ ‖y‖ ^ 2 + 2 * (‖x‖ * ‖y‖) := by gcongr
    _ = 2 * ‖x‖ * ‖y‖ + ‖y‖ ^ 2 := by ring

/-- Square energy of a general finite complex packet. -/
def finiteComplexPacketSquareEnergy (a : ℕ → ℂ) (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M, ‖a k‖ ^ 2

/-- The energy change under a finite packet perturbation is controlled by the two `l1` norms. -/
theorem abs_finiteComplexPacketSquareEnergy_add_sub_le
    (a r : ℕ → ℂ) (M : ℕ) :
    |finiteComplexPacketSquareEnergy (fun k => a k + r k) M -
        finiteComplexPacketSquareEnergy a M| ≤
      2 * (∑ k ∈ Finset.range M, ‖a k‖) *
          (∑ k ∈ Finset.range M, ‖r k‖) +
        (∑ k ∈ Finset.range M, ‖r k‖) ^ 2 := by
  rw [finiteComplexPacketSquareEnergy, finiteComplexPacketSquareEnergy,
    ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ Finset.range M, (‖a k + r k‖ ^ 2 - ‖a k‖ ^ 2)| ≤
        ∑ k ∈ Finset.range M, |‖a k + r k‖ ^ 2 - ‖a k‖ ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range M,
        (2 * ‖a k‖ * ‖r k‖ + ‖r k‖ ^ 2) := by
      exact Finset.sum_le_sum fun k _ => abs_norm_add_sq_sub_norm_sq_le (a k) (r k)
    _ ≤ ∑ k ∈ Finset.range M,
        (2 * ‖a k‖ * (∑ j ∈ Finset.range M, ‖r j‖) +
          ‖r k‖ * (∑ j ∈ Finset.range M, ‖r j‖)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hrle : ‖r k‖ ≤ ∑ j ∈ Finset.range M, ‖r j‖ :=
        Finset.single_le_sum (fun j _ => norm_nonneg (r j)) hk
      nlinarith [norm_nonneg (a k), norm_nonneg (r k)]
    _ = 2 * (∑ k ∈ Finset.range M, ‖a k‖) *
          (∑ k ∈ Finset.range M, ‖r k‖) +
        (∑ k ∈ Finset.range M, ‖r k‖) ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      rw [← Finset.mul_sum]
      ring_nf

end

end RHTower
