import GaloisForLFunctions.RHTower.SoninPacketFourierConcentration
import GaloisForLFunctions.RHTower.SoninLayerShellCongruence

/-!
# The aperture layer fixes the dilated wavepacket in the limit

The aperture layer splits exactly into a physical shell, a Fourier shell and a difference of
projection corrections.  On the dilated wavepacket the physical shell eventually vanishes because
the support has escaped, the Fourier shell converges to the identity by frequency concentration,
and the corrections die because they are compact.  So the layer fixes the dilated packet
asymptotically.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology

/-- **Exact splitting of the aperture layer.**  Physical shell, Fourier shell, and the difference
of the two exact projection corrections. -/
theorem evenSoninApertureLayer_eq_shell_add_correctionDiff (a b : ℝ) :
    evenSoninApertureLayer a b =
      (evenIndicatorCutoff b - evenIndicatorCutoff a) +
        (evenFourierCutoff b - evenFourierCutoff a) +
        (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) := by
  unfold evenSoninApertureLayer evenSoninProjectionCorrection
  abel

/-- **`(16)`.**  The aperture layer between two fixed apertures fixes the dilated wavepacket in the
limit. -/
theorem tendsto_norm_evenSoninApertureLayer_soninDilatedPacket_sub
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (q a₀ b₀ : ℝ)
    (ha₀ : 0 < a₀) (haq : a₀ < q) (hqb : q < b₀)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninApertureLayer a₀ b₀
            (soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)) -
          soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖)
      atTop (𝓝 0) := by
  have hq : 0 < q := ha₀.trans haq
  have hb₀ : 0 < b₀ := hq.trans hqb
  set v : ℕ → evenSubspace := fun n =>
    soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n) with hv
  -- the physical shell eventually annihilates the dilated packet
  have hphysEv : ∀ᶠ n : ℕ in atTop,
      (evenIndicatorCutoff b₀ - evenIndicatorCutoff a₀) (v n) = 0 := by
    have hrb : Tendsto (fun n : ℕ => r n * b) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hb hr
    filter_upwards [hrb.eventually_ge_atTop b₀] with n hn
    have h1 : evenIndicatorCutoff b₀ (v n) = 0 :=
      evenIndicatorCutoff_evenDilationCLM_inv_soninPacketEven_eq_zero b c hb hbc
        (2 * Real.pi * (r n * q)) (r n) (hrpos n) b₀ hn
    have h2 : evenIndicatorCutoff a₀ (v n) = 0 :=
      evenIndicatorCutoff_evenDilationCLM_inv_soninPacketEven_eq_zero b c hb hbc
        (2 * Real.pi * (r n * q)) (r n) (hrpos n) a₀ (by linarith)
    rw [sub_apply, h1, h2, sub_zero]
  have hphys : Tendsto (fun n : ℕ =>
      ‖(evenIndicatorCutoff b₀ - evenIndicatorCutoff a₀) (v n)‖) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hphysEv] with n hn
    rw [hn, norm_zero]
  -- the Fourier shell converges to the identity
  have hlow := tendsto_norm_evenFourierCutoff_soninDilatedPacket b c hb hbc q a₀ ha₀ haq
    r hrpos hr
  have hhigh := tendsto_norm_sub_evenFourierCutoff_soninDilatedPacket b c hb hbc q b₀ hq hqb
    r hrpos hr
  have hfour : Tendsto (fun n : ℕ =>
      ‖(evenFourierCutoff b₀ - evenFourierCutoff a₀) (v n) - v n‖) atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ =>
        ‖v n - evenFourierCutoff b₀ (v n)‖ + ‖evenFourierCutoff a₀ (v n)‖) atTop (𝓝 0) := by
      simpa using hhigh.add hlow
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hg
    have hsplit : (evenFourierCutoff b₀ - evenFourierCutoff a₀) (v n) - v n =
        -(v n - evenFourierCutoff b₀ (v n)) - evenFourierCutoff a₀ (v n) := by
      rw [sub_apply]
      abel
    rw [hsplit]
    calc ‖-(v n - evenFourierCutoff b₀ (v n)) - evenFourierCutoff a₀ (v n)‖
        ≤ ‖-(v n - evenFourierCutoff b₀ (v n))‖ + ‖evenFourierCutoff a₀ (v n)‖ :=
          norm_sub_le _ _
      _ = ‖v n - evenFourierCutoff b₀ (v n)‖ + ‖evenFourierCutoff a₀ (v n)‖ := by
          rw [norm_neg]
  -- the corrections die
  have hcorrA := tendsto_norm_evenSoninProjectionCorrection_apply_soninDilatedPacket b c a₀
    hb hbc ha₀ (fun n : ℕ => 2 * Real.pi * (r n * q)) r hrpos hr
  have hcorrB := tendsto_norm_evenSoninProjectionCorrection_apply_soninDilatedPacket b c b₀
    hb hbc hb₀ (fun n : ℕ => 2 * Real.pi * (r n * q)) r hrpos hr
  have hcorr : Tendsto (fun n : ℕ =>
      ‖(evenSoninProjectionCorrection a₀ - evenSoninProjectionCorrection b₀) (v n)‖)
      atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ =>
        ‖evenSoninProjectionCorrection a₀ (v n)‖ +
          ‖evenSoninProjectionCorrection b₀ (v n)‖) atTop (𝓝 0) := by
      simpa using hcorrA.add hcorrB
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hg
    rw [sub_apply]
    calc ‖evenSoninProjectionCorrection a₀ (v n) - evenSoninProjectionCorrection b₀ (v n)‖
        ≤ ‖evenSoninProjectionCorrection a₀ (v n)‖ +
            ‖evenSoninProjectionCorrection b₀ (v n)‖ := norm_sub_le _ _
      _ = _ := rfl
  -- combine
  have hgtot : Tendsto (fun n : ℕ =>
      (‖(evenIndicatorCutoff b₀ - evenIndicatorCutoff a₀) (v n)‖ +
        ‖(evenFourierCutoff b₀ - evenFourierCutoff a₀) (v n) - v n‖) +
        ‖(evenSoninProjectionCorrection a₀ - evenSoninProjectionCorrection b₀) (v n)‖)
      atTop (𝓝 0) := by
    simpa using (hphys.add hfour).add hcorr
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hgtot
  have hdecomp : evenSoninApertureLayer a₀ b₀ (v n) - v n =
      (evenIndicatorCutoff b₀ - evenIndicatorCutoff a₀) (v n) +
        ((evenFourierCutoff b₀ - evenFourierCutoff a₀) (v n) - v n) +
        (evenSoninProjectionCorrection a₀ - evenSoninProjectionCorrection b₀) (v n) := by
    rw [evenSoninApertureLayer_eq_shell_add_correctionDiff a₀ b₀]
    simp only [add_apply]
    abel
  rw [hdecomp]
  calc ‖(evenIndicatorCutoff b₀ - evenIndicatorCutoff a₀) (v n) +
          ((evenFourierCutoff b₀ - evenFourierCutoff a₀) (v n) - v n) +
          (evenSoninProjectionCorrection a₀ - evenSoninProjectionCorrection b₀) (v n)‖
      ≤ ‖(evenIndicatorCutoff b₀ - evenIndicatorCutoff a₀) (v n) +
            ((evenFourierCutoff b₀ - evenFourierCutoff a₀) (v n) - v n)‖ +
          ‖(evenSoninProjectionCorrection a₀ - evenSoninProjectionCorrection b₀) (v n)‖ :=
        norm_add_le _ _
    _ ≤ (‖(evenIndicatorCutoff b₀ - evenIndicatorCutoff a₀) (v n)‖ +
            ‖(evenFourierCutoff b₀ - evenFourierCutoff a₀) (v n) - v n‖) +
          ‖(evenSoninProjectionCorrection a₀ - evenSoninProjectionCorrection b₀) (v n)‖ := by
        gcongr
        exact norm_add_le _ _

end RHTower
