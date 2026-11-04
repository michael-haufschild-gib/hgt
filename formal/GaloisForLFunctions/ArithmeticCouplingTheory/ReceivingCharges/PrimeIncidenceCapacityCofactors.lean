import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.PrimeIncidenceReceivingCapacity
import GaloisForLFunctions.HTGeometry.HarmonicLogWindow

/-!
# Cofactor layers of prime receiving capacity

Inverse harmonic resistance is a sum of its successive drops. Exchanging
those finite layers with the prime sum expresses capacity through differences
of prime Mertens sums at the exact cofactor cutoffs.
-/

noncomputable section
open Finset
open scoped Classical

namespace GaloisForLFunctions.ArithmeticCouplingTheory

private theorem weight_eq_terminal_add_layers (g : ℕ → ℝ) {q N : ℕ}
    (hq : 1 ≤ q) (hqN : q ≤ N) :
    g q = g N + ∑ k ∈ Ico 1 N, if q ≤ k then g k - g (k + 1) else 0 := by
  rw [← sum_filter]
  have hf : (Ico 1 N).filter (fun k => q ≤ k) = Ico q N := by
    ext k
    simp only [mem_filter, mem_Ico]
    omega
  rw [hf]
  have ht : (∑ k ∈ Ico q N, ((-g (k + 1)) - (-g k))) = (-g N) - (-g q) := by
    rw [sum_Ico_eq_sub _ hqN, sum_range_sub (fun k => -g k) N,
      sum_range_sub (fun k => -g k) q]
    ring
  simp only [neg_sub_neg] at ht
  linarith only [ht]

private theorem sum_tail_eq_prefix_sub (a : ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    (∑ p ∈ Icc 1 N, if M < p then a p else 0) =
      (∑ p ∈ Icc 1 N, a p) - ∑ p ∈ Icc 1 M, a p := by
  have hpref : (∑ p ∈ Icc 1 N, if p ≤ M then a p else 0) = ∑ p ∈ Icc 1 M, a p := by
    rw [← sum_filter]
    congr 1
    ext p
    simp only [mem_filter, mem_Icc]
    omega
  have hs : (∑ p ∈ Icc 1 N, a p) =
      (∑ p ∈ Icc 1 N, if p ≤ M then a p else 0) +
        ∑ p ∈ Icc 1 N, if M < p then a p else 0 := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    by_cases hp : p ≤ M
    · simp only [if_pos hp, if_neg (not_lt.mpr hp), add_zero]
    · simp only [if_neg hp, if_pos (Nat.lt_of_not_ge hp), zero_add]
  rw [hpref] at hs
  linarith only [hs]

private theorem cofactor_le_iff_tail {N p k : ℕ} (hp : 0 < p) :
    N / p ≤ k ↔ N / (k + 1) < p := by
  calc
    N / p ≤ k ↔ N / p < k + 1 := by omega
    _ ↔ N < (k + 1) * p := Nat.div_lt_iff_lt_mul hp
    _ ↔ N < p * (k + 1) := by rw [Nat.mul_comm (k + 1) p]
    _ ↔ N / (k + 1) < p := (Nat.div_lt_iff_lt_mul (Nat.succ_pos k)).symm

private theorem cofactor_sum_eq_prefix_layers (a g : ℕ → ℝ) (N : ℕ) :
    (∑ p ∈ Icc 1 N, a p * g (N / p)) =
      g N * (∑ p ∈ Icc 1 N, a p) +
        ∑ k ∈ Ico 1 N, (g k - g (k + 1)) *
          ((∑ p ∈ Icc 1 N, a p) - ∑ p ∈ Icc 1 (N / (k + 1)), a p) := by
  have hlayer (p : ℕ) (hp : p ∈ Icc 1 N) :
      g (N / p) = g N + ∑ k ∈ Ico 1 N, if N / p ≤ k then g k - g (k + 1) else 0 := by
    have hp0 : 0 < p := (mem_Icc.mp hp).1
    have hq : 1 ≤ N / p := (Nat.le_div_iff_mul_le hp0).mpr (by
      simpa only [one_mul] using (mem_Icc.mp hp).2)
    exact weight_eq_terminal_add_layers g hq (Nat.div_le_self N p)
  calc
    _ = ∑ p ∈ Icc 1 N, a p *
        (g N + ∑ k ∈ Ico 1 N, if N / p ≤ k then g k - g (k + 1) else 0) :=
      sum_congr rfl fun p hp => by rw [hlayer p hp]
    _ = g N * (∑ p ∈ Icc 1 N, a p) +
        ∑ k ∈ Ico 1 N, (g k - g (k + 1)) *
          ∑ p ∈ Icc 1 N, if N / p ≤ k then a p else 0 := by
      simp_rw [mul_add, mul_sum]
      rw [sum_add_distrib, ← sum_mul, sum_comm]
      congr 1
      · rw [sum_mul]
        exact sum_congr rfl fun _ _ => mul_comm _ _
      · apply sum_congr rfl
        intro k _
        apply sum_congr rfl
        intro p _
        split_ifs <;> ring
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro k _
      congr 1
      calc
        _ = ∑ p ∈ Icc 1 N, if N / (k + 1) < p then a p else 0 := by
          apply sum_congr rfl
          intro p hp
          simp only [cofactor_le_iff_tail (show 0 < p from (mem_Icc.mp hp).1)]
        _ = _ := sum_tail_eq_prefix_sub a (Nat.div_le_self N (k + 1))

private theorem reciprocal_sum_eq_harmonic (N : ℕ) :
    (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) = (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  simp only [Rat.cast_inv, Rat.cast_natCast, one_div]

/-- The prime capacity is exactly a positive-layer combination of cofactor prime sums. -/
theorem primeIncidenceReceivingCapacity_cofactor_decomposition (N : ℕ) :
    primeIncidenceReceivingCapacity ((Icc 1 N).filter Nat.Prime) N =
      (∑ p ∈ Icc 1 N with p.Prime, Real.log p / (p : ℝ)) / (harmonic N : ℝ) +
        ∑ k ∈ Ico 1 N, (1 / (harmonic k : ℝ) - 1 / (harmonic (k + 1) : ℝ)) *
          ((∑ p ∈ Icc 1 N with p.Prime, Real.log p / (p : ℝ)) -
            ∑ p ∈ Icc 1 (N / (k + 1)) with p.Prime, Real.log p / (p : ℝ)) := by
  let a : ℕ → ℝ := fun p => if p.Prime then Real.log p / p else 0
  have h := cofactor_sum_eq_prefix_layers a (fun k => 1 / (harmonic k : ℝ)) N
  have hc : primeIncidenceReceivingCapacity ((Icc 1 N).filter Nat.Prime) N =
      ∑ p ∈ Icc 1 N, a p * (1 / (harmonic (N / p) : ℝ)) := by
    unfold primeIncidenceReceivingCapacity
    rw [sum_filter]
    apply sum_congr rfl
    intro p _
    rw [reciprocal_sum_eq_harmonic]
    dsimp only [a]
    split_ifs <;> ring
  rw [hc, h]
  simp only [a, ← sum_filter]
  ring

end GaloisForLFunctions.ArithmeticCouplingTheory

#print axioms GaloisForLFunctions.ArithmeticCouplingTheory.primeIncidenceReceivingCapacity_cofactor_decomposition
