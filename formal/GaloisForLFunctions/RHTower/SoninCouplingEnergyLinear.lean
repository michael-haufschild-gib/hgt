import GaloisForLFunctions.RHTower.SoninCouplingEnergyUnbounded

/-!
# The coupling's energy is linear in the scale

The schedule ties the scale to the number of annuli, so the count that bounds the energy from below
is itself a fixed multiple of the scale.  The energy bound therefore reads as a positive slope times
the scale, less a constant of the aperture.

Unboundedness alone is weaker and already known; what a linear rate adds is a comparison with any
sublinear cap.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The count is a fixed multiple of the scale. -/
theorem soninShellCutScale_mul_slope (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) {κ : ℝ}
    (hκ : 0 < κ) : (c - b) / (2 * κ) * soninShellCutScale b c N κ = (N : ℝ) := by
  have hne : c - b ≠ 0 := by
    have : (0 : ℝ) < c - b := by linarith
    exact this.ne'
  rw [soninShellCutScale]
  field_simp

/-- **The energy is linear in the scale.**  With the schedule's own scale the coupling's
Hilbert--Schmidt energy is at least a positive multiple of the scale, less a constant of the
aperture and nothing else. -/
theorem exists_linear_hsNormSq_soninApertureCoupling (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a ≤ b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) :
    ∃ κ C₀ : ℝ, 0 < κ ∧ ∀ M : ℕ,
      ∃ (N : ℕ) (hr : 1 < soninShellCutScale b c N κ), M ≤ N ∧
        (c - b) / (8 * κ) * soninShellCutScale b c N κ - C₀ ≤
          hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c
            (soninShellCutScale b c N κ) hr) := by
  obtain ⟨K, hK0, hK⟩ := exists_schedule_card_sub_le_hsNormSq_soninApertureCoupling N₀ hN₀
  set Dis : ℝ := 2 * hsNormSq (evenSoninProjectionCorrection b) +
    hsNormSq (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) with hDis
  obtain ⟨κ, hκ, hev⟩ := hK a b c q hbc ha hab hb haq hqb (1 / 2) (by norm_num) (by norm_num)
  refine ⟨κ, 36 * Dis, hκ, fun M => ?_⟩
  obtain ⟨N, hMN, hr, hN, hbound⟩ := ((Filter.eventually_ge_atTop M).and hev).exists
  refine ⟨N, hr, hMN, ?_⟩
  have hrpos : (0 : ℝ) < soninShellCutScale b c N κ := zero_lt_one.trans hr
  have hinv : (0 : ℝ) < (soninShellCutScale b c N κ)⁻¹ := inv_pos.mpr hrpos
  have hsum : ∑ k : Fin 3, hsNormSq (soninCouplingIdealErrors a b
      (soninShellCutScale b c N κ)⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) k) /
      ((1 : ℝ) / 2 / 6) ^ (2 : ℕ) = Dis / ((1 : ℝ) / 2 / 6) ^ (2 : ℕ) := by
    rw [← Finset.sum_div, hDis,
      sum_hsNormSq_soninCouplingIdealErrors a b (soninShellCutScale b c N κ)⁻¹ ha hb hinv]
  rw [hsum] at hbound
  have harith : ((N : ℝ) - Dis / ((1 : ℝ) / 2 / 6) ^ (2 : ℕ)) * (1 - (1 : ℝ) / 2) ^ (2 : ℕ) =
      (N : ℝ) / 4 - 36 * Dis := by
    norm_num
    ring
  rw [harith] at hbound
  refine le_trans (le_of_eq ?_) hbound
  have hslope : (c - b) / (8 * κ) * soninShellCutScale b c N κ = (N : ℝ) / 4 := by
    have h := soninShellCutScale_mul_slope b c hbc hN hκ
    calc (c - b) / (8 * κ) * soninShellCutScale b c N κ
        = ((c - b) / (2 * κ) * soninShellCutScale b c N κ) / 4 := by ring
      _ = (N : ℝ) / 4 := by rw [h]
  rw [hslope]

end RHTower
