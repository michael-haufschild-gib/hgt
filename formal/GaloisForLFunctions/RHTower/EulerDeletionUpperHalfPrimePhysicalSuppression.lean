import GaloisForLFunctions.RHTower.EulerDeletionUpperHalfPrimePacketCovariance

/-!
Pointwise suppression of literal upper-half prime packets after the physical
canonical beta normalization. No completed-period averaging is used.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower.DeletionPrimeWindowPhase

theorem geometric_packet_head_le_full (C Q : ℕ) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x < 1) (hC : 0 < C) :
    (1 - x ^ C) * (∑ s ∈ range (Q - 1), x ^ (s * C)) ≤
      1 - x ^ (Q * C) := by
  have hpow : x ^ C ≤ 1 := (pow_lt_one₀ hx0 hx1 hC.ne').le
  have hsum : (∑ s ∈ range (Q - 1), (x ^ C) ^ s) ≤
      ∑ s ∈ range Q, (x ^ C) ^ s := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (Nat.sub_le Q 1)
    · intro i hi hnot
      exact pow_nonneg (pow_nonneg hx0 _) _
  calc
    (1 - x ^ C) * (∑ s ∈ range (Q - 1), x ^ (s * C)) =
        (1 - x ^ C) * (∑ s ∈ range (Q - 1), (x ^ C) ^ s) := by
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      rw [Nat.mul_comm s C, pow_mul]
    _ ≤ (1 - x ^ C) * (∑ s ∈ range Q, (x ^ C) ^ s) :=
      mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hpow)
    _ = 1 - x ^ (Q * C) := by
      rw [mul_neg_geom_sum]
      rw [← pow_mul, Nat.mul_comm C Q]

theorem geometric_denominator_lower (C : ℕ) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (C : ℝ) * x ^ C ≤ ∑ a ∈ range C, x ^ a := by
  have hterm (a : ℕ) (ha : a ∈ range C) : x ^ C ≤ x ^ a :=
    pow_le_pow_of_le_one hx0 hx1 (Nat.le_of_lt (Finset.mem_range.mp ha))
  have h := Finset.sum_le_sum hterm
  simpa using h

theorem betaPacket_abs_le_geometric
    {p : ℕ} (hp : 0 < p) (C Q t : ℕ) (x : ℝ) (hx0 : 0 ≤ x) :
    |betaPacket p C Q t x| ≤ ∑ s ∈ range Q, x ^ (s * C) := by
  unfold betaPacket
  calc
    |∑ s ∈ range Q, phase p ((s + 1) * C) t * x ^ (s * C)| ≤
        ∑ s ∈ range Q, |phase p ((s + 1) * C) t * x ^ (s * C)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ range Q, x ^ (s * C) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 _)]
      calc
        |phase p ((s + 1) * C) t| * x ^ (s * C) ≤
            1 * x ^ (s * C) :=
          mul_le_mul_of_nonneg_right (phase_abs_le_one hp _ _) (pow_nonneg hx0 _)
        _ = _ := one_mul _

private theorem normalized_amplitude_abs_le_inv
    {a b d g B S C : ℝ}
    (hC : 0 < C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 < d) (hg : 0 < g)
    (hag : C * a ≤ g) (hB : |B| ≤ S) (hSd : b * S ≤ d) :
    |a * b * B / (d * g)| ≤ C⁻¹ := by
  have hbd : b * |B| ≤ d :=
    (mul_le_mul_of_nonneg_left hB hb).trans hSd
  have hprod : C * (a * b * |B|) ≤ d * g := by
    calc
      C * (a * b * |B|) = (C * a) * (b * |B|) := by ring
      _ ≤ g * (b * |B|) :=
        mul_le_mul_of_nonneg_right hag (mul_nonneg hb (abs_nonneg B))
      _ ≤ g * d := mul_le_mul_of_nonneg_left hbd hg.le
      _ = d * g := mul_comm _ _
  have hquot : a * b * |B| / (d * g) ≤ C⁻¹ := by
    apply (div_le_iff₀ (mul_pos hd hg)).2
    have haux : a * b * |B| ≤ (d * g) / C :=
      (le_div_iff₀ hC).2 (by nlinarith [hprod])
    calc
      a * b * |B| ≤ (d * g) / C := haux
      _ = C⁻¹ * (d * g) := by rw [div_eq_mul_inv, mul_comm]
  simpa [abs_div, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb,
    abs_of_nonneg (mul_nonneg hd.le hg.le)] using hquot

theorem clockResidualBetaWeight_prime_normalized_abs_le_inv_clock
    (L p Q t : ℕ) (x : ℝ) (hp : p.Prime) (hQ : 0 < Q)
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |x ^ DeletionResidueMartingale.clock L *
        (1 - x ^ DeletionResidueMartingale.clock L) *
        DeletionResidueMartingale.clockResidualBetaWeight L t (Q - 1) x p /
          ((1 - x ^ (Q * DeletionResidueMartingale.clock L)) *
            (∑ a ∈ range (DeletionResidueMartingale.clock L), x ^ a))| ≤
      (DeletionResidueMartingale.clock L : ℝ)⁻¹ := by
  let C := DeletionResidueMartingale.clock L
  have hC : 0 < C := DeletionResidueMartingale.clock_pos L
  have hpow : x ^ C < 1 := pow_lt_one₀ hx0 hx1 hC.ne'
  have hD : 0 < 1 - x ^ (Q * C) := by
    have hQC : 0 < Q * C := Nat.mul_pos hQ hC
    exact sub_pos.mpr (pow_lt_one₀ hx0 hx1 hQC.ne')
  have hG : 0 < ∑ a ∈ range C, x ^ a := geom_sum_pos hx0 hC.ne'
  have hB : |DeletionResidueMartingale.clockResidualBetaWeight L t (Q - 1) x p| ≤
      ∑ s ∈ range (Q - 1), x ^ (s * C) := by
    rw [clockResidualBetaWeight_prime_eq_neg_betaPacket L p t (Q - 1) x hp, abs_neg]
    exact betaPacket_abs_le_geometric hp.pos C (Q - 1) t x hx0
  have h := normalized_amplitude_abs_le_inv
    (show (0:ℝ) < C from Nat.cast_pos.mpr hC)
    (pow_nonneg hx0 C) (sub_nonneg.mpr hpow.le) hD hG
    (geometric_denominator_lower C x hx0 hx1.le)
    hB (geometric_packet_head_le_full C Q x hx0 hx1 hC)
  exact h

theorem upper_half_prime_packet_kernel_abs_le
    (N L p r : ℕ) (x : ℝ) (hLN : L ≤ N) (hp : p.Prime)
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |x ^ r *
      (x ^ DeletionResidueMartingale.clock L *
        (1 - x ^ DeletionResidueMartingale.clock L) *
        DeletionResidueMartingale.clockResidualBetaWeight L (r + 1)
          (DeletionResidueMartingale.canonicalClockRatio N L - 1) x p /
          ((1 - x ^ DeletionResidueMartingale.clock N) *
            (∑ a ∈ range (DeletionResidueMartingale.clock L), x ^ a)))| ≤
      x ^ r * (DeletionResidueMartingale.clock L : ℝ)⁻¹ := by
  have hQ : 0 < DeletionResidueMartingale.canonicalClockRatio N L := by
    unfold DeletionResidueMartingale.canonicalClockRatio
    omega
  have hclock : DeletionResidueMartingale.canonicalClockRatio N L *
      DeletionResidueMartingale.clock L = DeletionResidueMartingale.clock N := by
    rw [DeletionResidueMartingale.canonicalClockRatio_eq_div_of_le N L hLN]
    exact Nat.div_mul_cancel (DeletionResidueMartingale.clock_dvd hLN)
  rw [← hclock]
  rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 r)]
  exact mul_le_mul_of_nonneg_left
    (clockResidualBetaWeight_prime_normalized_abs_le_inv_clock L p
      (DeletionResidueMartingale.canonicalClockRatio N L) (r + 1) x hp hQ hx0 hx1)
    (pow_nonneg hx0 r)

end RHTower.DeletionPrimeWindowPhase
