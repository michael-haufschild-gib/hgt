import GaloisForLFunctions.RHTower.SoninPacketBandGapLimits
import GaloisForLFunctions.RHTower.SoninCouplingAdjointSetup

/-!
# The outer layer annihilates the doubly contracted packet

Contracting twice pushes the support out to radius `r² b` while the carrier only reaches `r q`, so
the doubly contracted packet is missed by every fixed physical aperture and captured by every fixed
Fourier aperture.  The outer aperture layer therefore kills it in the limit.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology

/-- The square clock grows. -/
theorem tendsto_sq_mul_atTop {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => r n ^ (2 : ℕ) * t) atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ hr
  filter_upwards [hr.eventually_ge_atTop (1 / t), hr.eventually_ge_atTop 0] with n h1 h2
  have hrt : 1 ≤ r n * t := by
    rw [div_le_iff₀ ht] at h1
    linarith
  nlinarith [h2, hrt]

/-- The gap between a fixed aperture on the square clock and the carrier on the linear clock
grows. -/
theorem tendsto_sq_gap_atTop {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) {q t : ℝ}
    (hq : 0 < q) (ht : 0 < t) :
    Tendsto (fun n : ℕ => r n ^ (2 : ℕ) * t - |r n * q|) atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ hr
  filter_upwards [hr.eventually_ge_atTop ((q + 1) / t), hr.eventually_ge_atTop 0] with n h1 h2
  have hrt : q + 1 ≤ r n * t := by
    rw [div_le_iff₀ ht] at h1
    linarith
  rw [abs_of_nonneg (mul_nonneg h2 hq.le)]
  nlinarith [h2, hrt]

/-- **`(19d)`.**  The outer aperture layer annihilates the doubly contracted wavepacket. -/
theorem tendsto_norm_evenSoninApertureLayer_doublyContracted
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (q : ℝ) (hq : 0 < q)
    (r : ℕ → ℝ) (hsq : ∀ n, 0 < r n ^ (2 : ℕ)) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninApertureLayer b c
          (soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n))‖)
      atTop (𝓝 0) := by
  have hc : 0 < c := hb.trans hbc
  set z : ℕ → evenSubspace := fun n =>
    soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n) with hz
  have hA : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hq hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  -- physical part: eventually exactly zero
  have hphysEv : ∀ᶠ n : ℕ in atTop,
      (evenIndicatorCutoff c - evenIndicatorCutoff b) (z n) = 0 := by
    filter_upwards [(tendsto_sq_mul_atTop hr hb).eventually_ge_atTop c] with n hn
    have h1 : evenIndicatorCutoff c (z n) = 0 :=
      evenIndicatorCutoff_evenDilationCLM_inv_soninPacketEven_eq_zero b c hb hbc
        (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n) c hn
    have h2 : evenIndicatorCutoff b (z n) = 0 :=
      evenIndicatorCutoff_evenDilationCLM_inv_soninPacketEven_eq_zero b c hb hbc
        (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n) b (by linarith)
    rw [sub_apply, h1, h2, sub_zero]
  have hphys : Tendsto (fun n : ℕ =>
      ‖(evenIndicatorCutoff c - evenIndicatorCutoff b) (z n)‖) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hphysEv] with n hn
    rw [hn, norm_zero]
  -- Fourier part: both apertures capture the packet
  have hcap : ∀ t : ℝ, 0 < t → Tendsto (fun n : ℕ => ‖z n - evenFourierCutoff t (z n)‖)
      atTop (𝓝 0) := by
    intro t ht
    have hgapT := tendsto_sq_gap_atTop hr hq ht
    have hbase := tendsto_norm_sub_evenFourierCutoff_soninPacketEven_gap b c hb hbc
      (fun n : ℕ => r n ^ (2 : ℕ) * t) (fun n : ℕ => r n * q) hgapT hA
    refine hbase.congr fun n => ?_
    exact (norm_sub_evenFourierCutoff_evenDilationCLM_inv t (r n ^ (2 : ℕ)) (hsq n)
      (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))).symm
  have hfour : Tendsto (fun n : ℕ =>
      ‖(evenFourierCutoff c - evenFourierCutoff b) (z n)‖) atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ =>
        ‖z n - evenFourierCutoff c (z n)‖ + ‖z n - evenFourierCutoff b (z n)‖)
        atTop (𝓝 0) := by
      simpa using (hcap c hc).add (hcap b hb)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hg
    have hsplit : (evenFourierCutoff c - evenFourierCutoff b) (z n) =
        (z n - evenFourierCutoff b (z n)) - (z n - evenFourierCutoff c (z n)) := by
      rw [sub_apply]
      abel
    rw [hsplit]
    calc ‖(z n - evenFourierCutoff b (z n)) - (z n - evenFourierCutoff c (z n))‖
        ≤ ‖z n - evenFourierCutoff b (z n)‖ + ‖z n - evenFourierCutoff c (z n)‖ :=
          norm_sub_le _ _
      _ = ‖z n - evenFourierCutoff c (z n)‖ + ‖z n - evenFourierCutoff b (z n)‖ :=
          add_comm _ _
  -- correction part: compactness on escaping support
  have hcorrB := tendsto_norm_compactOperator_apply_of_evenIndicatorCutoff_apply_eq_zero
    (evenSoninProjectionCorrection b)
    (IsSoninPrincipalRelativeIdeal.isCompactOperator
      (IsSoninPrincipalRelativeIdeal.projectionCorrection b hb)) z
    (2 * ‖soninBumpL2 b c hb hbc‖)
    (fun n => norm_soninDilatedPacket_le b c hb hbc (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n))
    (fun n : ℕ => r n ^ (2 : ℕ) * b) (tendsto_sq_mul_atTop hr hb)
    (fun n => evenIndicatorCutoff_soninDilatedPacket_eq_zero b c hb hbc
      (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n))
  have hcorrC := tendsto_norm_compactOperator_apply_of_evenIndicatorCutoff_apply_eq_zero
    (evenSoninProjectionCorrection c)
    (IsSoninPrincipalRelativeIdeal.isCompactOperator
      (IsSoninPrincipalRelativeIdeal.projectionCorrection c hc)) z
    (2 * ‖soninBumpL2 b c hb hbc‖)
    (fun n => norm_soninDilatedPacket_le b c hb hbc (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n))
    (fun n : ℕ => r n ^ (2 : ℕ) * b) (tendsto_sq_mul_atTop hr hb)
    (fun n => evenIndicatorCutoff_soninDilatedPacket_eq_zero b c hb hbc
      (2 * Real.pi * (r n * q)) (r n ^ (2 : ℕ)) (hsq n))
  have hcorr : Tendsto (fun n : ℕ =>
      ‖(evenSoninProjectionCorrection b - evenSoninProjectionCorrection c) (z n)‖)
      atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ =>
        ‖evenSoninProjectionCorrection b (z n)‖ +
          ‖evenSoninProjectionCorrection c (z n)‖) atTop (𝓝 0) := by
      simpa using hcorrB.add hcorrC
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hg
    rw [sub_apply]
    exact norm_sub_le _ _
  -- combine
  have hgtot : Tendsto (fun n : ℕ =>
      (‖(evenIndicatorCutoff c - evenIndicatorCutoff b) (z n)‖ +
        ‖(evenFourierCutoff c - evenFourierCutoff b) (z n)‖) +
        ‖(evenSoninProjectionCorrection b - evenSoninProjectionCorrection c) (z n)‖)
      atTop (𝓝 0) := by
    simpa using (hphys.add hfour).add hcorr
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hgtot
  have hdecomp : evenSoninApertureLayer b c (z n) =
      (evenIndicatorCutoff c - evenIndicatorCutoff b) (z n) +
        (evenFourierCutoff c - evenFourierCutoff b) (z n) +
        (evenSoninProjectionCorrection b - evenSoninProjectionCorrection c) (z n) := by
    rw [evenSoninApertureLayer_eq_shell_add_correctionDiff b c]
    simp only [add_apply]
  rw [hdecomp]
  calc ‖(evenIndicatorCutoff c - evenIndicatorCutoff b) (z n) +
          (evenFourierCutoff c - evenFourierCutoff b) (z n) +
          (evenSoninProjectionCorrection b - evenSoninProjectionCorrection c) (z n)‖
      ≤ ‖(evenIndicatorCutoff c - evenIndicatorCutoff b) (z n) +
            (evenFourierCutoff c - evenFourierCutoff b) (z n)‖ +
          ‖(evenSoninProjectionCorrection b - evenSoninProjectionCorrection c) (z n)‖ :=
        norm_add_le _ _
    _ ≤ (‖(evenIndicatorCutoff c - evenIndicatorCutoff b) (z n)‖ +
            ‖(evenFourierCutoff c - evenFourierCutoff b) (z n)‖) +
          ‖(evenSoninProjectionCorrection b - evenSoninProjectionCorrection c) (z n)‖ := by
        gcongr
        exact norm_add_le _ _

end RHTower
