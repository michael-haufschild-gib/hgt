import GaloisForLFunctions.RHTower.SoninDilatedPacketLayerLimit
import GaloisForLFunctions.RHTower.SoninPacketCompactVanishing
import GaloisForLFunctions.RHTower.SoninPacketFourierEscape

/-!
# The coupling carries the wavepacket to its dilate

The two-branch estimate reduces the successive-layer coupling on an annulus vector to the
difference of its two dilation branches.  On the wavepacket the expanding branch dies with the
central Fourier band, the exact projection correction dies by compactness, and the contracting
branch is the aperture layer applied to the dilated packet, which the layer fixes in the limit.

So the coupling sends the wavepacket to its inverse dilate, asymptotically.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology

/-- **`(3)`.**  Along any clock exceeding the crossing threshold, the coupling carries the
wavepacket to its inverse dilate. -/
theorem tendsto_norm_soninApertureCoupling_soninPacketEven_sub
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, c ≤ r n * a)
    (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
            (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))) -
          soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖)
      atTop (𝓝 0) := by
  have hq : 0 < q := ha.trans haq
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hq hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  -- the three vanishing inputs
  have hLayer := tendsto_norm_evenSoninApertureLayer_soninDilatedPacket_sub b c hb hbc q a b
    ha haq hqb r hrpos hr
  have hBand := tendsto_norm_evenFourierCutoff_soninPacketEven b c hb hbc b
    (fun n : ℕ => 2 * Real.pi * (r n * q)) hfreq
  have hCorr := tendsto_norm_evenSoninProjectionCorrection_apply_soninPacketEven b c b
    hb hbc hb (fun n : ℕ => 2 * Real.pi * (r n * q)) hfreq
  have hmaj : Tendsto (fun n : ℕ =>
      2 * ‖evenSoninProjectionCorrection b
            (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))‖ +
        (‖evenSoninApertureLayer a b
              (soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)) -
            soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖ +
          ‖evenFourierCutoff b
            (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))‖)) atTop (𝓝 0) := by
    simpa using (hCorr.const_mul (2 : ℝ)).add (hLayer.add hBand)
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hmaj
  set w : evenSubspace := soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)) with hw
  set v : evenSubspace :=
    soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n) with hv
  have hvdef : v = evenDilationCLM (r n)⁻¹ (inv_pos.mpr (hrpos n)) w := rfl
  have hlow : evenIndicatorCutoff b w = 0 :=
    evenIndicatorCutoff_soninPacketEven_eq_zero b c hb hbc (2 * Real.pi * (r n * q))
  have hhigh : evenIndicatorCutoff c w = w :=
    evenIndicatorCutoff_soninPacketEven_eq_self b c hb hbc (2 * Real.pi * (r n * q))
  have hbranch := norm_evenSoninApertureSuccessiveLayerTransition_sub_branches_le
    hab.le hbc.le (hrgt n) (hcr n) hlow hhigh
  have hexp : ‖evenSoninApertureLayer a b
      (evenDilationCLM (r n) (zero_lt_one.trans (hrgt n)) (evenFourierCutoff b w))‖ ≤
      ‖evenFourierCutoff b w‖ := by
    calc ‖evenSoninApertureLayer a b
          (evenDilationCLM (r n) (zero_lt_one.trans (hrgt n)) (evenFourierCutoff b w))‖
        ≤ ‖evenDilationCLM (r n) (zero_lt_one.trans (hrgt n)) (evenFourierCutoff b w)‖ :=
          norm_evenSoninApertureLayer_apply_le hab.le _
      _ = ‖evenFourierCutoff b w‖ :=
          norm_evenDilationCLM_apply (r n) (zero_lt_one.trans (hrgt n)) _
  calc ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) w - v‖
      ≤ ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) w -
            (evenSoninApertureLayer a b
                (evenDilationCLM (r n)⁻¹ (inv_pos.mpr (zero_lt_one.trans (hrgt n))) w) -
              evenSoninApertureLayer a b
                (evenDilationCLM (r n) (zero_lt_one.trans (hrgt n))
                  (evenFourierCutoff b w)))‖ +
          ‖(evenSoninApertureLayer a b
                (evenDilationCLM (r n)⁻¹ (inv_pos.mpr (zero_lt_one.trans (hrgt n))) w) -
              evenSoninApertureLayer a b
                (evenDilationCLM (r n) (zero_lt_one.trans (hrgt n))
                  (evenFourierCutoff b w))) - v‖ := by
        simpa using norm_sub_le_norm_sub_add_norm_sub
          (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) w)
          (evenSoninApertureLayer a b
              (evenDilationCLM (r n)⁻¹ (inv_pos.mpr (zero_lt_one.trans (hrgt n))) w) -
            evenSoninApertureLayer a b
              (evenDilationCLM (r n) (zero_lt_one.trans (hrgt n)) (evenFourierCutoff b w))) v
    _ ≤ 2 * ‖evenSoninProjectionCorrection b w‖ +
          (‖evenSoninApertureLayer a b v - v‖ + ‖evenFourierCutoff b w‖) := by
        refine add_le_add hbranch ?_
        calc ‖(evenSoninApertureLayer a b
                  (evenDilationCLM (r n)⁻¹ (inv_pos.mpr (zero_lt_one.trans (hrgt n))) w) -
                evenSoninApertureLayer a b
                  (evenDilationCLM (r n) (zero_lt_one.trans (hrgt n))
                    (evenFourierCutoff b w))) - v‖
              = ‖(evenSoninApertureLayer a b v - v) -
                  evenSoninApertureLayer a b
                    (evenDilationCLM (r n) (zero_lt_one.trans (hrgt n))
                      (evenFourierCutoff b w))‖ := by
                rw [hvdef]
                congr 1
                abel
          _ ≤ ‖evenSoninApertureLayer a b v - v‖ +
                ‖evenSoninApertureLayer a b
                    (evenDilationCLM (r n) (zero_lt_one.trans (hrgt n))
                      (evenFourierCutoff b w))‖ := norm_sub_le _ _
          _ ≤ ‖evenSoninApertureLayer a b v - v‖ + ‖evenFourierCutoff b w‖ := by
              gcongr

end RHTower
