import GaloisForLFunctions.RHTower.SoninPacketChannelCombinedForm

/-!
# Choosing the cut index at the carrier

The tower's radii are geometric, so the least index whose radius reaches a target overshoots it by at
most one factor of the ratio.  Placing the cut there puts the cut radius between twice the carrier
and a fixed multiple of it, which is what both halves of the height-uniform bound need: the layer
logarithms below the cut are then bounded by the logarithm at that radius, and the half-width times
the cut radius is bounded below by the half-width times the carrier.

The bound on the frequency-side channel over a rescaled packet therefore becomes explicit in the
packet's own data — carrier and half-width — with neither the tower's height nor a cut index left in
it.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-- **The least shell index past a target overshoots by at most one ratio.** -/
theorem exists_soninChannelCutIndex {a r : ℝ} (ha : 0 < a) (hr : 1 < r) (T : ℝ) :
    ∃ Kc : ℕ, T ≤ logShellRadius a r Kc ∧ logShellRadius a r Kc ≤ max a (r * T) := by
  classical
  have hex : ∃ k : ℕ, T ≤ logShellRadius a r k := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (T / a) hr
    refine ⟨k, ?_⟩
    rw [div_lt_iff₀ ha] at hk
    rw [logShellRadius]
    linarith
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, logShellRadius, pow_zero, one_mul]
    exact le_max_left a (r * T)
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hnot : ¬ T ≤ logShellRadius a r j := Nat.find_min hex (by omega)
    have hlt : logShellRadius a r j < T := lt_of_not_ge hnot
    have hstep : logShellRadius a r (j + 1) = r * logShellRadius a r j := by
      rw [logShellRadius, logShellRadius, pow_succ]
      ring
    have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
    rw [hj, hstep]
    exact le_trans (mul_le_mul_of_nonneg_left hlt.le hr0.le) (le_max_right a (r * T))

/-- The layer logarithms below an index lie between the base's and that index's. -/
theorem abs_log_logShellRadius_le_max {a r : ℝ} (ha : 0 < a) (hr : 1 < r) {k Kc : ℕ}
    (hk : k < Kc) :
    |Real.log (logShellRadius a r k)| ≤ max |Real.log a| |Real.log (logShellRadius a r Kc)| := by
  have h0 : logShellRadius a r 0 = a := by rw [logShellRadius, pow_zero, one_mul]
  have hlo : a ≤ logShellRadius a r k := by
    have h := logShellRadius_mono ha hr (Nat.zero_le k)
    rwa [h0] at h
  have hhi : logShellRadius a r k ≤ logShellRadius a r Kc := logShellRadius_mono ha hr hk.le
  exact abs_le_max_abs_abs (Real.log_le_log ha hlo)
    (Real.log_le_log (logShellRadius_pos ha hr k) hhi)

/-- **The frequency-side channel on a rescaled packet, in the packet's own data.**  With the cut
taken at the least shell radius past twice the carrier, the bound involves only the carrier, the
half-width and the tower's base and ratio — no cut index, and no tower height. -/
theorem exists_norm_evenFourierLogShellChannel_soninScaledPacketEven_le_carrier
    (N : ℕ) (hN : 2 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a r : ℝ), 0 < a → 1 < r → ∀ (n : ℕ) (m δ w : ℝ) (hδ : 0 < δ),
      0 < w → 1 ≤ 2 * w → |soninScaledPacketMean m δ (2 * Real.pi * w)| ≤ 1 →
        ‖evenFourierLogShellChannel a r n
            (soninScaledPacketEven m δ (2 * Real.pi * w) hδ)‖ ≤
          Real.sqrt (max |Real.log a| |Real.log (max a (r * (2 * w)))| ^ 2 *
              ‖soninScaledPacketEven m δ (2 * Real.pi * w) hδ‖ ^ 2 +
            8 * K / (((2 * N : ℝ) - 1) * (1 - (r ^ (2 * N - 2))⁻¹)) *
              ((δ * (2 * w)) ^ (2 * N - 2))⁻¹) := by
  obtain ⟨K, hK0, hK⟩ :=
    exists_norm_evenFourierLogShellChannel_soninScaledPacketEven_le_combined N hN
  refine ⟨K, hK0, ?_⟩
  intro a r ha hr n m δ w hδ hw hone hmean
  obtain ⟨Kc, hlow, hhigh⟩ := exists_soninChannelCutIndex ha hr (2 * w)
  set Mval : ℝ := max |Real.log a| |Real.log (max a (r * (2 * w)))| with hMval
  -- the cut radius sits between the base and the overshoot bound
  have h0 : logShellRadius a r 0 = a := by rw [logShellRadius, pow_zero, one_mul]
  have hbase : a ≤ logShellRadius a r Kc := by
    have h := logShellRadius_mono ha hr (Nat.zero_le Kc)
    rwa [h0] at h
  have habsKc : |Real.log (logShellRadius a r Kc)| ≤ Mval :=
    abs_le_max_abs_abs (Real.log_le_log ha hbase)
      (Real.log_le_log (logShellRadius_pos ha hr Kc) hhigh)
  have hM : ∀ k, k < Kc → |Real.log (logShellRadius a r k)| ≤ Mval := by
    intro k hk
    refine le_trans (abs_log_logShellRadius_le_max ha hr hk) ?_
    exact max_le (le_max_left _ _) habsKc
  have hcut1 : (1 : ℝ) ≤ logShellRadius a r Kc := le_trans hone hlow
  have h := hK a r ha hr n Kc m δ w Mval hδ hw hmean hcut1 hlow hM
  refine le_trans h (Real.sqrt_le_sqrt ?_)
  -- the outer term only improves when the cut radius is replaced by the carrier
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (2 * N : ℝ) - 1 := by linarith
  have hrp1 : (1 : ℝ) < r ^ (2 * N - 2) := one_lt_pow₀ hr (by omega)
  have hgap : (0 : ℝ) < 1 - (r ^ (2 * N - 2))⁻¹ := by
    have := inv_lt_one_of_one_lt₀ hrp1
    linarith
  have hcoef : (0 : ℝ) ≤ 8 * K / (((2 * N : ℝ) - 1) * (1 - (r ^ (2 * N - 2))⁻¹)) := by
    positivity
  have hwpos : (0 : ℝ) < δ * (2 * w) := by positivity
  have hle : δ * (2 * w) ≤ δ * logShellRadius a r Kc :=
    mul_le_mul_of_nonneg_left hlow hδ.le
  gcongr

end RHTower

