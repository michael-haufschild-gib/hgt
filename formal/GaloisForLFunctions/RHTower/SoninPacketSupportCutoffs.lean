import GaloisForLFunctions.RHTower.SoninPacketL2
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry

/-!
# Physical cutoffs on the wavepacket and on its dilate

The wavepacket lives strictly inside the annulus, so the physical cutoff at the inner radius kills
it and the cutoff at the outer radius fixes it.  Conjugating through a dilation moves both radii by
the scale, which is what puts the dilated packet outside every aperture of the flag.

These are the two hypotheses of the corpus's two-branch estimate for the successive-layer coupling.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory ContinuousLinearMap

/-- The inner physical cutoff annihilates the wavepacket. -/
theorem evenIndicatorCutoff_soninPacketEven_eq_zero
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    evenIndicatorCutoff b (soninPacketEven b c hb hbc κ) = 0 := by
  have hgoal : indicatorCutoff (centralInterval b) (measurableSet_centralInterval b)
      (soninPacketL2 b c hb hbc κ) = 0 := by
    apply Lp.ext
    filter_upwards [indicatorCutoff_ae (centralInterval b) (measurableSet_centralInterval b)
      (soninPacketL2 b c hb hbc κ), soninPacketL2_coeFn b c hb hbc κ,
      Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hval hzero
    rw [hx, hzero]
    by_cases hmem : x ∈ centralInterval b
    · rw [Set.indicator_of_mem hmem, hval]
      have habs : |x| ≤ b := abs_le.mpr ⟨hmem.1, hmem.2⟩
      rw [soninPacket_eq_zero_of_abs_le b c hb hbc κ habs]
      simp
    · rw [Set.indicator_of_notMem hmem]
      rfl
  apply Subtype.ext
  rw [coe_evenIndicatorCutoff_apply, coe_soninPacketEven, hgoal]
  simp

/-- The outer physical cutoff fixes the wavepacket. -/
theorem evenIndicatorCutoff_soninPacketEven_eq_self
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    evenIndicatorCutoff c (soninPacketEven b c hb hbc κ) = soninPacketEven b c hb hbc κ := by
  apply Subtype.ext
  rw [coe_evenIndicatorCutoff_apply, coe_soninPacketEven]
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (centralInterval c) (measurableSet_centralInterval c)
    (soninPacketL2 b c hb hbc κ), soninPacketL2_coeFn b c hb hbc κ] with x hx hval
  rw [hx]
  by_cases hmem : x ∈ centralInterval c
  · rw [Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem hmem, hval]
    have habs : c ≤ |x| := by
      by_contra hlt
      push Not at hlt
      exact hmem (abs_le.mp hlt.le)
    rw [soninPacket_eq_zero_of_le_abs b c hb hbc κ habs]
    simp

/-- A physical cutoff below the inner radius still annihilates the wavepacket. -/
theorem evenIndicatorCutoff_soninPacketEven_eq_zero_of_le
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ s : ℝ) (hs : s ≤ b) :
    evenIndicatorCutoff s (soninPacketEven b c hb hbc κ) = 0 := by
  have hnest := DFunLike.congr_fun (evenIndicatorCutoff_mul_of_le s b hs)
    (soninPacketEven b c hb hbc κ)
  rw [mul_apply_eq_comp, evenIndicatorCutoff_soninPacketEven_eq_zero b c hb hbc κ,
    map_zero] at hnest
  exact hnest.symm

/-- A physical cutoff above the outer radius still fixes the wavepacket. -/
theorem evenIndicatorCutoff_soninPacketEven_eq_self_of_le
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ s : ℝ) (hs : c ≤ s) :
    evenIndicatorCutoff s (soninPacketEven b c hb hbc κ) = soninPacketEven b c hb hbc κ := by
  have hnest := DFunLike.congr_fun (evenIndicatorCutoff_mul_of_le_rev c s hs)
    (soninPacketEven b c hb hbc κ)
  rw [mul_apply_eq_comp, evenIndicatorCutoff_soninPacketEven_eq_self b c hb hbc κ] at hnest
  exact hnest

/-! ### The dilated packet -/

/-- **`(11)`.**  Every aperture below `r b` misses the inverse-dilated wavepacket. -/
theorem evenIndicatorCutoff_evenDilationCLM_inv_soninPacketEven_eq_zero
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ r : ℝ) (hr : 0 < r) (s : ℝ) (hs : s ≤ r * b) :
    evenIndicatorCutoff s
        (evenDilationCLM r⁻¹ (inv_pos.mpr hr) (soninPacketEven b c hb hbc κ)) = 0 := by
  have hcov := DFunLike.congr_fun
    (evenIndicatorCutoff_mul_evenDilationCLM s r⁻¹ (inv_pos.mpr hr))
    (soninPacketEven b c hb hbc κ)
  rw [mul_apply_eq_comp, mul_apply_eq_comp] at hcov
  rw [hcov, evenIndicatorCutoff_soninPacketEven_eq_zero_of_le b c hb hbc κ (r⁻¹ * s) ?_,
    map_zero]
  rw [inv_mul_le_iff₀ hr] at *
  linarith [hs]

/-- Every aperture above `r c` fixes the inverse-dilated wavepacket. -/
theorem evenIndicatorCutoff_evenDilationCLM_inv_soninPacketEven_eq_self
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ r : ℝ) (hr : 0 < r) (s : ℝ) (hs : r * c ≤ s) :
    evenIndicatorCutoff s
        (evenDilationCLM r⁻¹ (inv_pos.mpr hr) (soninPacketEven b c hb hbc κ)) =
      evenDilationCLM r⁻¹ (inv_pos.mpr hr) (soninPacketEven b c hb hbc κ) := by
  have hcov := DFunLike.congr_fun
    (evenIndicatorCutoff_mul_evenDilationCLM s r⁻¹ (inv_pos.mpr hr))
    (soninPacketEven b c hb hbc κ)
  rw [mul_apply_eq_comp, mul_apply_eq_comp] at hcov
  rw [hcov, evenIndicatorCutoff_soninPacketEven_eq_self_of_le b c hb hbc κ (r⁻¹ * s) ?_]
  rw [le_inv_mul_iff₀ hr]
  linarith [hs]

end RHTower
