import GaloisForLFunctions.RHTower.EulerDeletionUpperHalfPrimePhaseCovariance

/-!
Prime upper-half beta packets inherit short-period covariance after physical
carrier recombination. The final theorem applies to literal clockResidualBetaWeight.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction
namespace RHTower.DeletionPrimeWindowPhase

def betaPacket (p C Q t : ℕ) (x : ℝ) : ℝ :=
  ∑ s ∈ range Q, phase p ((s + 1) * C) t * x ^ (s * C)

private theorem betaPacket_cross_expand
    (p q C Q R M : ℕ) (x y z : ℝ) :
    (∑ t ∈ range M, betaPacket p C Q t x * betaPacket q C R t y * z ^ t) =
      ∑ s ∈ range Q, ∑ r ∈ range R,
        x ^ (s * C) * y ^ (r * C) *
          ∑ t ∈ range M,
            phase p ((s + 1) * C) t * phase q ((r + 1) * C) t * z ^ t := by
  calc
    _ = ∑ t ∈ range M, ∑ s ∈ range Q, ∑ r ∈ range R,
          x ^ (s * C) * y ^ (r * C) *
            (phase p ((s + 1) * C) t * phase q ((r + 1) * C) t * z ^ t) := by
      apply Finset.sum_congr rfl
      intro t ht
      unfold betaPacket
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = ∑ s ∈ range Q, ∑ r ∈ range R, ∑ t ∈ range M,
          x ^ (s * C) * y ^ (r * C) *
            (phase p ((s + 1) * C) t * phase q ((r + 1) * C) t * z ^ t) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]

theorem betaPacket_cross_weighted_abs_le
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : p.Coprime q)
    (C Q R M : ℕ) (x y z : ℝ)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |∑ t ∈ range M, betaPacket p C Q t x * betaPacket q C R t y * z ^ t| ≤
      (p * q : ℕ) *
        (∑ s ∈ range Q, x ^ (s * C)) *
          (∑ r ∈ range R, y ^ (r * C)) := by
  rw [betaPacket_cross_expand]
  have hterm (s r : ℕ) :
      |x ^ (s * C) * y ^ (r * C) *
        ∑ t ∈ range M,
          phase p ((s + 1) * C) t * phase q ((r + 1) * C) t * z ^ t| ≤
        (p * q : ℕ) * x ^ (s * C) * y ^ (r * C) := by
    have hx : 0 ≤ x ^ (s * C) := pow_nonneg hx0 _
    have hy : 0 ≤ y ^ (r * C) := pow_nonneg hy0 _
    have hpair := phase_pair_weighted_prefix_abs_le_period hp hq hpq
      ((s + 1) * C) ((r + 1) * C) M z hz0 hz1
    rw [abs_mul, abs_of_nonneg (mul_nonneg hx hy)]
    calc
      (x ^ (s * C) * y ^ (r * C)) *
          |∑ t ∈ range M,
            phase p ((s + 1) * C) t * phase q ((r + 1) * C) t * z ^ t| ≤
        (x ^ (s * C) * y ^ (r * C)) * (p * q : ℕ) :=
        mul_le_mul_of_nonneg_left hpair (mul_nonneg hx hy)
      _ = _ := by ring
  calc
    |∑ s ∈ range Q, ∑ r ∈ range R,
        x ^ (s * C) * y ^ (r * C) *
          ∑ t ∈ range M,
            phase p ((s + 1) * C) t * phase q ((r + 1) * C) t * z ^ t| ≤
      ∑ s ∈ range Q, |∑ r ∈ range R,
        x ^ (s * C) * y ^ (r * C) *
          ∑ t ∈ range M,
            phase p ((s + 1) * C) t * phase q ((r + 1) * C) t * z ^ t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ range Q, ∑ r ∈ range R,
        |x ^ (s * C) * y ^ (r * C) *
          ∑ t ∈ range M,
            phase p ((s + 1) * C) t * phase q ((r + 1) * C) t * z ^ t| := by
      apply Finset.sum_le_sum
      intro s hs
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ range Q, ∑ r ∈ range R,
        (p * q : ℕ) * x ^ (s * C) * y ^ (r * C) := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro r hr
      exact hterm s r
    _ = (p * q : ℕ) *
          (∑ s ∈ range Q, x ^ (s * C)) *
            (∑ r ∈ range R, y ^ (r * C)) := by
      calc
        _ = ∑ s ∈ range Q, (p * q : ℕ) * x ^ (s * C) *
            (∑ r ∈ range R, y ^ (r * C)) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.mul_sum]
        _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem clockResidualBetaWeight_prime_eq_neg_betaPacket
    (L p t Q : ℕ) (x : ℝ) (hp : p.Prime) :
    DeletionResidueMartingale.clockResidualBetaWeight L t Q x p =
      -betaPacket p (DeletionResidueMartingale.clock L) Q t x := by
  have hsource :=
    (DeletionResidueMartingale.moebius_divisor_betaPrefix_eq_clockResidualBetaWeight
      L p t Q x).symm
  calc
    _ = ((moebius p : ℤ) : ℝ) *
          ∑ s ∈ range Q,
            (∑ i ∈ range (s + 1),
              DeletionResidueMartingale.divisorWindowDiscrepancy p
                (t + i * DeletionResidueMartingale.clock L)
                (DeletionResidueMartingale.clock L)) *
                  x ^ (s * DeletionResidueMartingale.clock L) := hsource
    _ = -(∑ s ∈ range Q,
            (∑ i ∈ range (s + 1),
              DeletionResidueMartingale.divisorWindowDiscrepancy p
                (t + i * DeletionResidueMartingale.clock L)
                (DeletionResidueMartingale.clock L)) *
                  x ^ (s * DeletionResidueMartingale.clock L)) := by
      rw [moebius_apply_prime hp]
      norm_num
    _ = -betaPacket p (DeletionResidueMartingale.clock L) Q t x := by
      congr 1
      unfold betaPacket
      apply Finset.sum_congr rfl
      intro s hs
      rw [DeletionResidueMartingale.divisorWindowDiscrepancy_prefix_eq_remainder
        p t (DeletionResidueMartingale.clock L) s hp.pos
          (DeletionResidueMartingale.clock_pos L)]
      rfl

theorem clockResidualBetaWeight_prime_cross_weighted_abs_le
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p.Coprime q)
    (L Q R M : ℕ) (x y z : ℝ)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |∑ t ∈ range M,
      DeletionResidueMartingale.clockResidualBetaWeight L t Q x p *
        DeletionResidueMartingale.clockResidualBetaWeight L t R y q * z ^ t| ≤
      (p * q : ℕ) *
        (∑ s ∈ range Q, x ^ (s * DeletionResidueMartingale.clock L)) *
          (∑ r ∈ range R, y ^ (r * DeletionResidueMartingale.clock L)) := by
  simp_rw [clockResidualBetaWeight_prime_eq_neg_betaPacket L p _ Q x hp,
    clockResidualBetaWeight_prime_eq_neg_betaPacket L q _ R y hq]
  simp only [neg_mul_neg]
  exact betaPacket_cross_weighted_abs_le hp.pos hq.pos hpq
    (DeletionResidueMartingale.clock L) Q R M x y z hx0 hy0 hz0 hz1

end RHTower.DeletionPrimeWindowPhase
