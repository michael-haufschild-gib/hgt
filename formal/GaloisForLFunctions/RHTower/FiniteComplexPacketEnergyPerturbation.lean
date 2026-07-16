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
    _ = 2 * ‖x‖ * ‖y‖ + ‖y‖ ^ 2 := by ring_nf

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

/-- An exponentially smaller `l1` perturbation preserves a sharp half-order square-energy
limit. -/
theorem tendsto_finiteComplexPacketSquareEnergy_add_of_exponentiallySmaller_l1
    (a r : ℕ → ℕ → ℂ) {A R B beta L : ℝ}
    (hA : 0 ≤ A) (hB : 0 < B)
    (hbeta0 : 0 ≤ beta) (hbeta : beta < B)
    (ha : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), ‖a n k‖ ≤ A * B ^ n)
    (hr : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), ‖r n k‖ ≤ R * beta ^ n)
    (hlead : Tendsto
      (fun n : ℕ => Real.sqrt n * finiteComplexPacketSquareEnergy (a n) (n + 1) /
        (B ^ 2) ^ n) atTop (nhds L)) :
    Tendsto
      (fun n : ℕ => Real.sqrt n *
        finiteComplexPacketSquareEnergy (fun k => a n k + r n k) (n + 1) /
          (B ^ 2) ^ n)
      atTop (nhds L) := by
  let q : ℝ := beta / B
  have hq0 : 0 ≤ q := div_nonneg hbeta0 hB.le
  have hq1 : q < 1 := (div_lt_one hB).2 hbeta
  have hq2zero := tendsto_sqrtNat_mul_const_pow_of_lt_one
    (mul_nonneg hq0 hq0) (by nlinarith [sq_nonneg (q - 1)])
  have hmajor : Tendsto
      (fun n : ℕ => 2 * A * R * (Real.sqrt n * q ^ n) +
        R ^ 2 * (Real.sqrt n * (q ^ 2) ^ n))
      atTop (nhds 0) := by
    have h :=
      ((tendsto_sqrtNat_mul_const_pow_of_lt_one hq0 hq1).const_mul (2 * A * R)).add
        (hq2zero.const_mul (R ^ 2))
    convert h using 1
    · funext n
      rw [pow_two q]
    · ring_nf
  have hdiff : Tendsto
      (fun n : ℕ =>
        Real.sqrt n *
            finiteComplexPacketSquareEnergy (fun k => a n k + r n k) (n + 1) /
              (B ^ 2) ^ n -
          Real.sqrt n * finiteComplexPacketSquareEnergy (a n) (n + 1) /
            (B ^ 2) ^ n)
      atTop (nhds 0) := by
    apply squeeze_zero_norm'
      (a := fun n : ℕ => 2 * A * R * (Real.sqrt n * q ^ n) +
        R ^ 2 * (Real.sqrt n * (q ^ 2) ^ n))
    · filter_upwards with n
      have hBpow : 0 < B ^ n := pow_pos hB n
      have hB2pow : 0 < (B ^ 2) ^ n := pow_pos (sq_pos_of_pos hB) n
      have hpert := abs_finiteComplexPacketSquareEnergy_add_sub_le (a n) (r n) (n + 1)
      have hal1 := ha n
      have hrl1 := hr n
      rw [Real.norm_eq_abs]
      rw [← sub_div, ← mul_sub, abs_div, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hB2pow]
      calc
        Real.sqrt n *
            |finiteComplexPacketSquareEnergy (fun k => a n k + r n k) (n + 1) -
              finiteComplexPacketSquareEnergy (a n) (n + 1)| /
              (B ^ 2) ^ n ≤
          Real.sqrt n *
            (2 * (∑ k ∈ Finset.range (n + 1), ‖a n k‖) *
                (∑ k ∈ Finset.range (n + 1), ‖r n k‖) +
              (∑ k ∈ Finset.range (n + 1), ‖r n k‖) ^ 2) /
                (B ^ 2) ^ n := by gcongr
        _ ≤ Real.sqrt n *
            (2 * (A * B ^ n) * (R * beta ^ n) + (R * beta ^ n) ^ 2) /
              (B ^ 2) ^ n := by
          gcongr
        _ = 2 * A * R * (Real.sqrt n * q ^ n) +
            R ^ 2 * (Real.sqrt n * (q ^ 2) ^ n) := by
          dsimp only [q]
          simp only [pow_two, mul_pow, div_pow]
          field_simp [hBpow.ne']
    · exact hmajor
  have hsum := hlead.add hdiff
  convert hsum using 1
  · funext n
    ring_nf
  · ring_nf

end

end RHTower
