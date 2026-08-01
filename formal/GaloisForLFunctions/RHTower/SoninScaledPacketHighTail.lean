import GaloisForLFunctions.RHTower.SoninScaledPacketBandFraction

/-!
# The energy a rescaled packet keeps outside a band

The Fourier cutoff is the transform-side restriction to a central band, so what the cutoff discards
is the transform restricted to the band's complement.  The discarded energy is therefore the
spectral density integrated over that complement — the exact counterpart of the band energy, and the
quantity that decides whether a band captures a packet.

Unlike the band, the complement is unbounded, so this integral is the one that needs a decaying
majorant rather than a supremum.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- The complement of a central band is measurable. -/
theorem measurableSet_strictCentralTail (t : ℝ) : MeasurableSet {η : ℝ | t < |η|} := by
  have hset : {η : ℝ | t < |η|} = {η : ℝ | |η| ≤ t}ᶜ := by
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  rw [hset, centralBand_eq_Icc]
  exact measurableSet_Icc.compl

/-- **The discarded energy is the spectral density outside the band.** -/
theorem norm_sq_sub_evenFourierCutoff_soninScaledPacketEven_eq_density
    (m δ κ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    ‖soninScaledPacketEven m δ κ hδ - evenFourierCutoff t (soninScaledPacketEven m δ κ hδ)‖ ^ 2 =
      ∫ ξ : ℝ, {η : ℝ | t < |η|}.indicator (soninScaledPacketSpectralDensity m δ κ) ξ := by
  set g : SoninL2 := fourierUnitary (soninScaledPacketL2 m δ κ hδ) with hg
  have hcoe : ((soninScaledPacketEven m δ κ hδ -
        evenFourierCutoff t (soninScaledPacketEven m δ κ hδ) : evenSubspace) : SoninL2) =
      fourierUnitary.symm (g - indicatorCutoff (centralInterval t)
        (measurableSet_centralInterval t) g) := by
    have h₁ : ((evenFourierCutoff t (soninScaledPacketEven m δ κ hδ) : evenSubspace) : SoninL2) =
        fourierUnitary.symm (indicatorCutoff (centralInterval t)
          (measurableSet_centralInterval t) g) := rfl
    have h₂ : ((soninScaledPacketEven m δ κ hδ : evenSubspace) : SoninL2) =
        fourierUnitary.symm g := by
      rw [hg, LinearIsometryEquiv.symm_apply_apply]
      rfl
    rw [Submodule.coe_sub, h₁, h₂, ← map_sub]
  have hnorm : ‖soninScaledPacketEven m δ κ hδ -
      evenFourierCutoff t (soninScaledPacketEven m δ κ hδ)‖ =
      ‖g - indicatorCutoff (centralInterval t) (measurableSet_centralInterval t) g‖ := by
    rw [show ‖soninScaledPacketEven m δ κ hδ -
        evenFourierCutoff t (soninScaledPacketEven m δ κ hδ)‖ =
      ‖((soninScaledPacketEven m δ κ hδ -
        evenFourierCutoff t (soninScaledPacketEven m δ κ hδ) : evenSubspace) : SoninL2)‖ from rfl,
      hcoe]
    exact fourierUnitary.symm.norm_map _
  rw [hnorm, norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub g (indicatorCutoff (centralInterval t)
      (measurableSet_centralInterval t) g),
    indicatorCutoff_ae (centralInterval t) (measurableSet_centralInterval t) g,
    fourierUnitary_soninScaledPacketL2_coeFn m δ κ hδ] with ξ hsub hind hval
  rw [hsub, Pi.sub_apply, hind]
  by_cases hmem : ξ ∈ centralInterval t
  · have hnot : ξ ∉ {η : ℝ | t < |η|} := by
      have := (mem_centralInterval_iff t ξ).mp hmem
      simp only [Set.mem_setOf_eq, not_lt]
      exact this
    rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot, sub_self, norm_zero]
    norm_num
  · have hmemT : ξ ∈ {η : ℝ | t < |η|} := by
      have : ¬ |ξ| ≤ t := fun h => hmem ((mem_centralInterval_iff t ξ).mpr h)
      simp only [Set.mem_setOf_eq]
      linarith [not_le.mp this]
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_mem hmemT, sub_zero,
      soninScaledPacketSpectralDensity, hval]

/-- **Above twice the carrier the density is a majorant square.**  Every one of the three tail
arguments is then at least half the frequency, so the whole spectral density is bounded by the
reference majorant at half the scaled frequency. -/
theorem soninScaledPacketSpectralDensity_le_tailSup (m δ w ξ : ℝ) (hδ : 0 < δ) (hw : 0 < w)
    (hmean : |soninScaledPacketMean m δ (2 * Real.pi * w)| ≤ 1) (hξ : 2 * w ≤ |ξ|) :
    soninScaledPacketSpectralDensity m δ (2 * Real.pi * w) ξ ≤
      16 * δ ^ 2 * soninRefTailSup (δ * |ξ| / 2) ^ 2 := by
  set S : ℝ := soninRefTailSup (δ * |ξ| / 2) with hS
  have hSnn : 0 ≤ S := soninRefTailSup_nonneg _
  have habsw : |w| = w := abs_of_pos hw
  have hminus : δ * |ξ| / 2 ≤ δ * |ξ - w| := by
    have h := abs_sub_abs_le_abs_sub ξ w
    rw [habsw] at h
    nlinarith [hδ, h, hξ]
  have hplus : δ * |ξ| / 2 ≤ δ * |ξ + w| := by
    have h := abs_sub_abs_le_abs_sub ξ (-w)
    rw [abs_neg, habsw, sub_neg_eq_add] at h
    nlinarith [hδ, h, hξ]
  have hzero : δ * |ξ| / 2 ≤ δ * |ξ| := by
    have : (0 : ℝ) ≤ δ * |ξ| := by positivity
    linarith
  have h₁ := soninScaledBumpTailBound_le hδ hminus
  have h₂ := soninScaledBumpTailBound_le hδ hplus
  have h₃ := soninScaledBumpTailBound_le hδ hzero
  have hmain := norm_fourier_soninScaledPacket_le m δ w ξ hδ
  have hmeannn : (0 : ℝ) ≤ |soninScaledPacketMean m δ (2 * Real.pi * w)| := abs_nonneg _
  have hB3nn : 0 ≤ soninScaledBumpTailBound δ ξ := soninScaledBumpTailBound_nonneg δ ξ hδ
  have hmul : |soninScaledPacketMean m δ (2 * Real.pi * w)| * soninScaledBumpTailBound δ ξ ≤
      2 * δ * S := by
    calc |soninScaledPacketMean m δ (2 * Real.pi * w)| * soninScaledBumpTailBound δ ξ
        ≤ 1 * soninScaledBumpTailBound δ ξ := mul_le_mul_of_nonneg_right hmean hB3nn
      _ = soninScaledBumpTailBound δ ξ := one_mul _
      _ ≤ 2 * δ * S := h₃
  have hbound : ‖𝓕 (fun x : ℝ => (soninScaledPacket m δ (2 * Real.pi * w) x : ℂ)) ξ‖ ≤
      4 * δ * S := by
    linarith [hmain, h₁, h₂, hmul]
  have hnn := norm_nonneg (𝓕 (fun x : ℝ => (soninScaledPacket m δ (2 * Real.pi * w) x : ℂ)) ξ)
  show ‖𝓕 (fun x : ℝ => (soninScaledPacket m δ (2 * Real.pi * w) x : ℂ)) ξ‖ ^ 2 ≤
    16 * δ ^ 2 * S ^ 2
  nlinarith [hbound, hnn, hδ, hSnn]

end RHTower
