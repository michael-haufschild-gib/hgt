import GaloisForLFunctions.RHTower.SoninIdealErrorEnergyConstant

/-!
# The coupling's energy is unbounded along the schedule

Fixing the shortfall at a half turns the schedule's bound into the number of annuli less a constant
of the aperture, quartered.  The number of annuli may be demanded past any threshold, so the bound
passes any prescribed level.

The coupling's Hilbert--Schmidt energy therefore has no upper bound over the schedules available at
a fixed aperture window.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- **The coupling's energy exceeds every level.**  At a fixed aperture window and carrier ratio,
some schedule drives the Hilbert--Schmidt energy past any prescribed bound. -/
theorem exists_hsNormSq_soninApertureCoupling_ge (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a ≤ b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) (B : ℝ) :
    ∃ (κ : ℝ) (N : ℕ) (hr : 1 < soninShellCutScale b c N κ),
      B ≤ hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c
        (soninShellCutScale b c N κ) hr) := by
  obtain ⟨K, hK0, hK⟩ := exists_schedule_card_sub_le_hsNormSq_soninApertureCoupling N₀ hN₀
  set Dis : ℝ := 2 * hsNormSq (evenSoninProjectionCorrection b) +
    hsNormSq (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) with hDis
  obtain ⟨κ, hκ, hev⟩ := hK a b c q hbc ha hab hb haq hqb (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨N, hMN, hr, hN, hbound⟩ := ((Filter.eventually_ge_atTop ⌈4 * B + 144 * Dis⌉₊).and hev).exists
  refine ⟨κ, N, hr, ?_⟩
  have hrpos : (0 : ℝ) < soninShellCutScale b c N κ := zero_lt_one.trans hr
  have hinv : (0 : ℝ) < (soninShellCutScale b c N κ)⁻¹ := inv_pos.mpr hrpos
  -- the discount is the aperture's own constant
  have hsum : ∑ k : Fin 3, hsNormSq (soninCouplingIdealErrors a b
      (soninShellCutScale b c N κ)⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) k) /
      ((1 : ℝ) / 2 / 6) ^ (2 : ℕ) = Dis / ((1 : ℝ) / 2 / 6) ^ (2 : ℕ) := by
    rw [← Finset.sum_div, hDis,
      sum_hsNormSq_soninCouplingIdealErrors a b (soninShellCutScale b c N κ)⁻¹ ha hb hinv]
  rw [hsum] at hbound
  -- the count passes the threshold
  have hceil : 4 * B + 144 * Dis ≤ (⌈4 * B + 144 * Dis⌉₊ : ℝ) := Nat.le_ceil _
  have hNge : ((⌈4 * B + 144 * Dis⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
  have hNlarge : 4 * B + 144 * Dis ≤ (N : ℝ) := le_trans hceil hNge
  have harith : ((N : ℝ) - Dis / ((1 : ℝ) / 2 / 6) ^ (2 : ℕ)) * (1 - (1 : ℝ) / 2) ^ (2 : ℕ) =
      ((N : ℝ) - 144 * Dis) / 4 := by
    norm_num
    ring
  rw [harith] at hbound
  refine le_trans ?_ hbound
  linarith [hNlarge]

end RHTower
