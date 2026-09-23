import GaloisForLFunctions.RHTower.SoninSublinearChannelFamily
import GaloisForLFunctions.HTGeometry.LogMaxSublinear

/-!
# The frequency-side channel is closed as a completion

The channel's size on a rescaled packet is the logarithm at the cut against the packet's mass plus a
constant in the half-width times the carrier.  Along a schedule whose carriers stay proportional to
the scale and whose half-width times carrier stays bounded below, both are sublinear in the scale —
the first logarithmically, the second not at all.

A sublinear channel family cannot restore the floor, so no completion built from the frequency-side
channel does, whatever heights it chooses.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology InnerProduct InnerProductSpace

/-- **No completion from the frequency-side channel restores the floor.**  The tower's heights are
arbitrary; what is used is that the packets' carriers stay proportional to the scale, their
half-width times carrier stays bounded below, and their norms stay bounded. -/
theorem not_bddBelow_soninCompletedPacketValueVar_fourierLogShellChannelFamily
    (N₀ : ℕ) (hN₀ : 1 ≤ N₀) (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b)
    (haq : a < q) (hqb : 2 * q ≤ b)
    {Nd : ℕ} (hNd : 2 ≤ Nd) {a₀ r₀ : ℝ} (ha₀ : 0 < a₀) (hr₀ : 1 < r₀)
    {Q c₀ W : ℝ} (hQ : 0 < Q) (hc₀ : 0 < c₀) (hW : 0 ≤ W) :
    ∃ (κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      ∀ (height : ℕ → ℕ) (m δ w : ℕ → ℝ) (hδ : ∀ i, 0 < δ i),
        (∀ i, 0 < w i) → (∀ i, 1 ≤ 2 * w i) →
        (∀ i, |soninScaledPacketMean (m i) (δ i) (2 * Real.pi * w i)| ≤ 1) →
        (∀ i, w i ≤ Q * soninShellCutScale b c (Nstart + i) κ) →
        (∀ i, c₀ ≤ δ i * (2 * w i)) →
        (∀ i, ‖soninScaledPacketEven (m i) (δ i) (2 * Real.pi * w i) (hδ i)‖ ≤ W) →
        ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
          M ≤ soninCompletedPacketValueVar s a b c
            (fun i => soninShellCutScale b c (Nstart + i) κ) hp
            (fun i => (⟪soninScaledPacketEven (m i) (δ i) (2 * Real.pi * w i) (hδ i),
              evenFourierLogShellChannel a₀ r₀ (height i)
                (soninScaledPacketEven (m i) (δ i) (2 * Real.pi * w i) (hδ i))⟫_ℂ).re) := by
  obtain ⟨Kc, hKc0, hKc⟩ :=
    exists_norm_evenFourierLogShellChannel_soninScaledPacketEven_le_carrier Nd hNd
  have hr₀0 : (0 : ℝ) < r₀ := lt_trans zero_lt_one hr₀
  have hNR : (2 : ℝ) ≤ (Nd : ℝ) := by exact_mod_cast hNd
  have hden : (0 : ℝ) < (2 * Nd : ℝ) - 1 := by linarith
  have hrp1 : (1 : ℝ) < r₀ ^ (2 * Nd - 2) := one_lt_pow₀ hr₀ (by omega)
  have hgap : (0 : ℝ) < 1 - (r₀ ^ (2 * Nd - 2))⁻¹ := by
    have := inv_lt_one_of_one_lt₀ hrp1
    linarith
  have hCf0 : (0 : ℝ) ≤
      8 * Kc / (((2 * Nd : ℝ) - 1) * (1 - (r₀ ^ (2 * Nd - 2))⁻¹)) := by positivity
  have hCconst0 : (0 : ℝ) ≤
      8 * Kc / (((2 * Nd : ℝ) - 1) * (1 - (r₀ ^ (2 * Nd - 2))⁻¹)) / c₀ ^ (2 * Nd - 2) := by
    positivity
  -- the logarithmic part is nonnegative and sublinear
  have hF0 : ∀ r : ℝ, 0 ≤ |Real.log a₀| + Real.log (max a₀ (2 * r₀ * Q * r)) := by
    intro r
    have h1 : Real.log a₀ ≤ Real.log (max a₀ (2 * r₀ * Q * r)) :=
      Real.log_le_log ha₀ (le_max_left _ _)
    have h2 : -|Real.log a₀| ≤ Real.log a₀ := neg_abs_le _
    linarith
  have hFsub : Tendsto
      (fun r : ℝ => (|Real.log a₀| + Real.log (max a₀ (2 * r₀ * Q * r))) / r) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => |Real.log a₀| / r) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop tendsto_id _
    have hKpos : (0 : ℝ) < 2 * r₀ * Q := by positivity
    have h2 := h1.add
      (GaloisForLFunctions.HTGeometry.tendsto_log_max_div_atTop (A := a₀) hKpos)
    rw [add_zero] at h2
    exact h2.congr fun r => by ring
  have hBsub : Tendsto (fun r : ℝ => Real.sqrt
      ((|Real.log a₀| + Real.log (max a₀ (2 * r₀ * Q * r))) ^ (2 : ℕ) * W ^ (2 : ℕ) +
        8 * Kc / (((2 * Nd : ℝ) - 1) * (1 - (r₀ ^ (2 * Nd - 2))⁻¹)) /
          c₀ ^ (2 * Nd - 2)) / r) atTop (𝓝 0) :=
    GaloisForLFunctions.HTGeometry.tendsto_sqrt_sq_mul_add_div_atTop hF0 hFsub hW hCconst0
  obtain ⟨κ, Nstart, hpsc, hmain⟩ :=
    not_bddBelow_soninCompletedPacketValueVar_of_sublinear_channel N₀ hN₀ a b c q hbc ha hab hb
      haq hqb _ hW hBsub
  refine ⟨κ, Nstart, hpsc, ?_⟩
  intro height m δ w hδ hwpos hw1 hmean hwQ hprod hnorm
  refine hmain (fun i => soninScaledPacketEven (m i) (δ i) (2 * Real.pi * w i) (hδ i))
    (fun i => evenFourierLogShellChannel a₀ r₀ (height i)) hnorm ?_
  intro i
  refine le_trans
    (hKc a₀ r₀ ha₀ hr₀ (height i) (m i) (δ i) (w i) (hδ i) (hwpos i) (hw1 i) (hmean i))
    (Real.sqrt_le_sqrt ?_)
  -- the logarithmic slot
  have hpos₁ : (0 : ℝ) < max a₀ (r₀ * (2 * w i)) := lt_of_lt_of_le ha₀ (le_max_left _ _)
  have hone₁ : (1 : ℝ) ≤ max a₀ (r₀ * (2 * w i)) := by
    have : (1 : ℝ) ≤ r₀ * (2 * w i) := by nlinarith [hw1 i, hr₀.le]
    exact le_trans this (le_max_right _ _)
  have hlognn : (0 : ℝ) ≤ Real.log (max a₀ (r₀ * (2 * w i))) := Real.log_nonneg hone₁
  have hmaxle : max |Real.log a₀| |Real.log (max a₀ (r₀ * (2 * w i)))| ≤
      |Real.log a₀| + Real.log (max a₀ (r₀ * (2 * w i))) := by
    rw [abs_of_nonneg hlognn]
    exact max_le (le_add_of_nonneg_right hlognn) (le_add_of_nonneg_left (abs_nonneg _))
  have hargle : r₀ * (2 * w i) ≤ 2 * r₀ * Q * soninShellCutScale b c (Nstart + i) κ := by
    have := hwQ i
    nlinarith [hr₀0, this]
  have hmaxmono : max a₀ (r₀ * (2 * w i)) ≤
      max a₀ (2 * r₀ * Q * soninShellCutScale b c (Nstart + i) κ) :=
    max_le_max le_rfl hargle
  have hlogmono : Real.log (max a₀ (r₀ * (2 * w i))) ≤
      Real.log (max a₀ (2 * r₀ * Q * soninShellCutScale b c (Nstart + i) κ)) :=
    Real.log_le_log hpos₁ hmaxmono
  have hLle : max |Real.log a₀| |Real.log (max a₀ (r₀ * (2 * w i)))| ≤
      |Real.log a₀| +
        Real.log (max a₀ (2 * r₀ * Q * soninShellCutScale b c (Nstart + i) κ)) := by
    linarith
  have hLnn : (0 : ℝ) ≤ max |Real.log a₀| |Real.log (max a₀ (r₀ * (2 * w i)))| :=
    le_trans (abs_nonneg _) (le_max_left _ _)
  have hsq₁ : max |Real.log a₀| |Real.log (max a₀ (r₀ * (2 * w i)))| ^ (2 : ℕ) ≤
      (|Real.log a₀| +
        Real.log (max a₀ (2 * r₀ * Q * soninShellCutScale b c (Nstart + i) κ))) ^ (2 : ℕ) := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hLnn hLle
  have hsq₂ : ‖soninScaledPacketEven (m i) (δ i) (2 * Real.pi * w i) (hδ i)‖ ^ (2 : ℕ) ≤ W ^ (2 : ℕ) := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self (norm_nonneg _) (hnorm i)
  have hpartA : max |Real.log a₀| |Real.log (max a₀ (r₀ * (2 * w i)))| ^ (2 : ℕ) *
      ‖soninScaledPacketEven (m i) (δ i) (2 * Real.pi * w i) (hδ i)‖ ^ (2 : ℕ) ≤
      (|Real.log a₀| +
        Real.log (max a₀ (2 * r₀ * Q * soninShellCutScale b c (Nstart + i) κ))) ^ (2 : ℕ) * W ^ (2 : ℕ) :=
    mul_le_mul hsq₁ hsq₂ (sq_nonneg _) (sq_nonneg _)
  -- the constant slot
  have hc₀p : (0 : ℝ) < c₀ ^ (2 * Nd - 2) := pow_pos hc₀ (2 * Nd - 2)
  have hprodp : c₀ ^ (2 * Nd - 2) ≤ (δ i * (2 * w i)) ^ (2 * Nd - 2) :=
    pow_le_pow_left₀ hc₀.le (hprod i) (2 * Nd - 2)
  have hpartB : 8 * Kc / (((2 * Nd : ℝ) - 1) * (1 - (r₀ ^ (2 * Nd - 2))⁻¹)) *
      ((δ i * (2 * w i)) ^ (2 * Nd - 2))⁻¹ ≤
      8 * Kc / (((2 * Nd : ℝ) - 1) * (1 - (r₀ ^ (2 * Nd - 2))⁻¹)) / c₀ ^ (2 * Nd - 2) := by
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ hCf0
    exact inv_anti₀ hc₀p hprodp
  linarith

end RHTower

