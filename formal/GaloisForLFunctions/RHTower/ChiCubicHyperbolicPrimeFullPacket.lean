import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeTies

/-!
# The complete fixed-radius hyperbolic prime packet

The original cubic is partitioned into both strict gap orders and EVERY tie.
The two orders agree by the literal entry symmetry; the entire tie sector is
negligible. The complementary full-cubic tail is retained exactly.
-/

noncomputable section

namespace RHTower

open Finset Filter Topology

/-- The full original sharp hyperbolic packet, with both contraction exclusions
and every allowed numerator collision retained. -/
def chiCubicHyperbolicPrimeFullPacket (N : ℝ) (M : ℕ) : ℂ :=
  ∑ r ∈ primeProfileBand N, ∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N,
    if p ≠ r ∧ q ≠ r ∧ |(p : ℝ) - r| * |(q : ℝ) - r| ≤ (M : ℝ) * r
    then primeGaussianCubicMainEntry N p q r else 0

private theorem entry_swap (N : ℝ) (p q r : ℕ) :
    primeGaussianCubicMainEntry N p q r = primeGaussianCubicMainEntry N q p r := by
  unfold primeGaussianCubicMainEntry
  rw [mul_comm (p : ℝ) (q : ℝ)]
  ring

private theorem ordered_tie_split (a b K : ℝ) (z : ℂ) :
    (if a * b ≤ K then z else 0) =
      (if a < b ∧ a * b ≤ K then z else 0) +
      (if b < a ∧ b * a ≤ K then z else 0) +
      (if a ^ 2 ≤ K then if a = b then z else 0 else 0) := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h, not_lt_of_ge h.le, ne_of_lt h]
  · simp [pow_two]
  · simp [h, not_lt_of_ge h.le, ne_of_gt h, mul_comm]

/-- Exact finite completion of the original ordered sector. No tie is omitted. -/
theorem chiCubicHyperbolicPrimeFullPacket_eq (N : ℝ) (M : ℕ) :
    chiCubicHyperbolicPrimeFullPacket N M =
      2 * chiCubicHyperbolicPrimePacket N M + chiCubicHyperbolicPrimeTiePacket N M := by
  classical
  let P := primeProfileBand N
  let O := fun p q r : ℕ =>
    if p ≠ r ∧ |(p : ℝ) - r| < |(q : ℝ) - r| ∧
        |(p : ℝ) - r| * |(q : ℝ) - r| ≤ (M : ℝ) * r
    then primeGaussianCubicMainEntry N p q r else 0
  let T := fun p q r : ℕ =>
    if p ≠ r ∧ |(p : ℝ) - r| ^ 2 ≤ (M : ℝ) * r then
      if |(p : ℝ) - r| = |(q : ℝ) - r| then primeGaussianCubicMainEntry N p q r else 0
    else 0
  have hO : chiCubicHyperbolicPrimePacket N M =
      ∑ r ∈ P, ∑ p ∈ P, ∑ q ∈ P, O p q r := by
    change (∑ q ∈ P, ∑ p ∈ P, ∑ r ∈ P, O p q r) = _
    calc
      _ = ∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P, O p q r := Finset.sum_comm
      _ = ∑ p ∈ P, ∑ r ∈ P, ∑ q ∈ P, O p q r :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  have hswap : (∑ r ∈ P, ∑ p ∈ P, ∑ q ∈ P, O q p r) =
      ∑ r ∈ P, ∑ p ∈ P, ∑ q ∈ P, O p q r :=
    Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  have hT : chiCubicHyperbolicPrimeTiePacket N M =
      ∑ r ∈ P, ∑ p ∈ P, ∑ q ∈ P, T p q r := by
    unfold chiCubicHyperbolicPrimeTiePacket chiCubicHyperbolicPrimeHolePairs
    rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro p _
    by_cases hact : p ≠ r ∧ |(p : ℝ) - r| ^ 2 ≤ (M : ℝ) * r
    · simp [T, hact.1, hact.2, Finset.sum_filter, P]
    · simp only [T, hact, ite_false]
      simp
  have hsplit (p q r : ℕ) :
      (if p ≠ r ∧ q ≠ r ∧ |(p : ℝ) - r| * |(q : ℝ) - r| ≤ (M : ℝ) * r
        then primeGaussianCubicMainEntry N p q r else 0) = O p q r + O q p r + T p q r := by
    by_cases hpr : p = r
    · subst p
      simp [O, T, not_lt_of_ge (abs_nonneg ((q : ℝ) - r))]
    by_cases hqr : q = r
    · subst q
      have hgap : 0 < |(p : ℝ) - r| := abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast hpr))
      simp [O, T, not_lt_of_ge (abs_nonneg ((p : ℝ) - r)), hgap.ne']
    · simpa only [O, T, ne_eq, hpr, hqr, not_false_eq_true, true_and, entry_swap N q p r] using
        ordered_tie_split |(p : ℝ) - r| |(q : ℝ) - r| ((M : ℝ) * r)
          (primeGaussianCubicMainEntry N p q r)
  unfold chiCubicHyperbolicPrimeFullPacket
  simp only [hsplit, Finset.sum_add_distrib]
  change (∑ r ∈ P, ∑ p ∈ P, ∑ q ∈ P, O p q r) +
    (∑ r ∈ P, ∑ p ∈ P, ∑ q ∈ P, O q p r) +
    (∑ r ∈ P, ∑ p ∈ P, ∑ q ∈ P, T p q r) = _
  rw [hswap, ← hO, ← hT]
  ring

/-- Unconditional cancellation of the FULL original fixed-radius hyperbolic
prime packet, including the transpose and every equal-gap tie. -/
theorem chiCubicHyperbolicPrimeFullPacket_tendsto (M : ℕ) :
    Tendsto (fun N : ℝ => Real.log N ^ 2 / N * ‖chiCubicHyperbolicPrimeFullPacket N M‖)
      atTop (𝓝 0) := by
  have hlim := ((chiCubicHyperbolicPrimePacket_tendsto M).const_mul (2 : ℝ)).add
    (chiCubicHyperbolicPrimeTiePacket_tendsto M)
  simp only [mul_zero, add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    positivity
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    rw [chiCubicHyperbolicPrimeFullPacket_eq]
    calc
      _ ≤ (Real.log N ^ 2 / N) *
          (‖2 * chiCubicHyperbolicPrimePacket N M‖ + ‖chiCubicHyperbolicPrimeTiePacket N M‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ = _ := by rw [norm_mul, Complex.norm_ofNat]; ring

/-- The entire complementary cubic tail, with original prime labels and both
contraction exclusions retained. -/
def chiCubicHyperbolicPrimeTail (N : ℝ) (M : ℕ) : ℂ :=
  ∑ r ∈ primeProfileBand N, ∑ p ∈ primeProfileBand N, ∑ q ∈ primeProfileBand N,
    if p ≠ r ∧ q ≠ r ∧ (M : ℝ) * r < |(p : ℝ) - r| * |(q : ℝ) - r|
    then primeGaussianCubicMainEntry N p q r else 0

/-- Exact full-cubic partition. Fixed-radius cancellation leaves this ENTIRE
complementary tail; no uniform tail saving is asserted. -/
theorem primeGaussianCubicOffDiagonal_eq_hyperbolic_add_tail (N : ℝ) (M : ℕ) :
    primeGaussianCubicOffDiagonal N =
      chiCubicHyperbolicPrimeFullPacket N M + chiCubicHyperbolicPrimeTail N M := by
  classical
  unfold primeGaussianCubicOffDiagonal chiCubicHyperbolicPrimeFullPacket chiCubicHyperbolicPrimeTail
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  by_cases hpr : p = r
  · simp [hpr]
  by_cases hqr : q = r
  · simp [hqr]
  by_cases hcut : |(p : ℝ) - r| * |(q : ℝ) - r| ≤ (M : ℝ) * r
  · simp [hpr, hqr, hcut, not_lt_of_ge hcut]
  · simp [hpr, hqr, hcut, lt_of_not_ge hcut]

end RHTower
