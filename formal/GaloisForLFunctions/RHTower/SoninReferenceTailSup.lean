import GaloisForLFunctions.RHTower.SoninScaledPacketTail

/-!
# A uniform tail majorant for the reference profile

Rapid decay is a statement about one frequency tending to infinity; a band estimate needs a single
number controlling *all* frequencies outside a symmetric band at once.  The supremum of the
reference transform's magnitude outside the band is that number: it is finite because the transform
is bounded by the profile's mass, and it vanishes as the band grows because the transform decays in
both directions.

Applied to the packet, this turns the three-term tail bound into one estimate valid throughout a
band: as long as the band radius stays below the carrier frequency, every in-band frequency is
separated from both shifted spectra by at least the gap, so the whole in-band spectrum is bounded by
the majorant at the gap.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter MeasureTheory
open scoped Topology FourierTransform

/-- The transform of the reference profile is bounded by the profile's mass. -/
theorem norm_fourier_soninUnitBumpC_le (v : ℝ) :
    ‖𝓕 soninUnitBumpC v‖ ≤ ∫ y : ℝ, ‖soninUnitBumpC y‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- **The reference tail majorant.**  The largest transform magnitude outside a symmetric band. -/
def soninRefTailSup (u : ℝ) : ℝ :=
  ⨆ v : ℝ, if u ≤ |v| then ‖𝓕 soninUnitBumpC v‖ else 0

theorem bddAbove_soninRefTail (u : ℝ) :
    BddAbove (Set.range fun v : ℝ => if u ≤ |v| then ‖𝓕 soninUnitBumpC v‖ else 0) := by
  refine ⟨∫ y : ℝ, ‖soninUnitBumpC y‖, ?_⟩
  rintro _ ⟨v, rfl⟩
  by_cases h : u ≤ |v|
  · simp only [h, if_true]
    exact norm_fourier_soninUnitBumpC_le v
  · simp only [h, if_false]
    exact integral_nonneg fun y => norm_nonneg _

/-- Outside the band, the transform is bounded by the majorant. -/
theorem norm_fourier_soninUnitBumpC_le_tailSup {u v : ℝ} (h : u ≤ |v|) :
    ‖𝓕 soninUnitBumpC v‖ ≤ soninRefTailSup u := by
  have hle := le_ciSup (bddAbove_soninRefTail u) v
  simpa only [soninRefTailSup, h, if_true] using hle

theorem soninRefTailSup_nonneg (u : ℝ) : 0 ≤ soninRefTailSup u := by
  refine le_trans (norm_nonneg (𝓕 soninUnitBumpC (|u| + 1))) ?_
  refine norm_fourier_soninUnitBumpC_le_tailSup ?_
  rw [abs_of_pos (by positivity : (0 : ℝ) < |u| + 1)]
  exact le_trans (le_abs_self u) (by linarith)

/-- A uniform bound outside the band bounds the majorant. -/
theorem soninRefTailSup_le {u c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v : ℝ, u ≤ |v| → ‖𝓕 soninUnitBumpC v‖ ≤ c) : soninRefTailSup u ≤ c := by
  refine ciSup_le fun v => ?_
  by_cases hv : u ≤ |v|
  · simpa only [hv, if_true] using h v hv
  · simpa only [hv, if_false] using hc

/-- **The majorant vanishes.**  Rapid decay in both directions makes the whole outside of a growing
band uniformly small. -/
theorem tendsto_soninRefTailSup_atTop : Tendsto soninRefTailSup atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hpos := (tendsto_pow_mul_norm_fourier_soninUnitBumpC_atTop 0)
  have hneg := tendsto_pow_mul_norm_fourier_neg_atTop
    hasCompactSupport_soninUnitBumpC contDiff_soninUnitBumpC 0
  rw [Metric.tendsto_atTop] at hpos hneg
  obtain ⟨U₁, hU₁⟩ := hpos (ε / 2) (by linarith)
  obtain ⟨U₂, hU₂⟩ := hneg (ε / 2) (by linarith)
  refine ⟨max U₁ U₂, fun u hu => ?_⟩
  have hbound : soninRefTailSup u ≤ ε / 2 := by
    refine soninRefTailSup_le (by linarith) fun v hv => ?_
    rcases le_total 0 v with hv0 | hv0
    · have hvU : U₁ ≤ v := by
        rw [abs_of_nonneg hv0] at hv
        exact le_trans (le_trans (le_max_left U₁ U₂) hu) hv
      have h := hU₁ v hvU
      rw [Real.dist_eq, sub_zero, pow_zero, one_mul, abs_of_nonneg (norm_nonneg _)] at h
      exact h.le
    · have hvU : U₂ ≤ -v := by
        rw [abs_of_nonpos hv0] at hv
        exact le_trans (le_trans (le_max_right U₁ U₂) hu) hv
      have h := hU₂ (-v) hvU
      rw [Real.dist_eq, sub_zero, pow_zero, one_mul, neg_neg,
        abs_of_nonneg (norm_nonneg _)] at h
      exact h.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (soninRefTailSup_nonneg u)]
  linarith

/-- The profile tail at a frequency separated from the origin. -/
theorem soninScaledBumpTailBound_le {δ u η : ℝ} (hδ : 0 < δ) (hsep : u ≤ δ * |η|) :
    soninScaledBumpTailBound δ η ≤ 2 * δ * soninRefTailSup u := by
  have h₁ : ‖𝓕 soninUnitBumpC (δ * η)‖ ≤ soninRefTailSup u := by
    refine norm_fourier_soninUnitBumpC_le_tailSup ?_
    rw [abs_mul, abs_of_pos hδ]
    exact hsep
  have h₂ : ‖𝓕 soninUnitBumpC (δ * -η)‖ ≤ soninRefTailSup u := by
    refine norm_fourier_soninUnitBumpC_le_tailSup ?_
    rw [abs_mul, abs_of_pos hδ, abs_neg]
    exact hsep
  rw [soninScaledBumpTailBound]
  nlinarith [hδ, soninRefTailSup_nonneg u]

/-- **Uniform in-band bound for the packet's spectrum.**  Below the carrier frequency, the packet's
spectral magnitude is bounded by the reference majorant at the gap, plus the mean times the global
majorant. -/
theorem norm_fourier_soninScaledPacket_le_tailSup
    (m δ w₀ t ξ : ℝ) (hδ : 0 < δ) (ht : |ξ| ≤ t) (htw : t < w₀) :
    ‖𝓕 (fun x : ℝ => (soninScaledPacket m δ (2 * Real.pi * w₀) x : ℂ)) ξ‖ ≤
      2 * δ * soninRefTailSup (δ * (w₀ - t)) +
        |soninScaledPacketMean m δ (2 * Real.pi * w₀)| * (2 * δ * soninRefTailSup 0) := by
  have habs : |ξ| ≤ t := ht
  have hξt : -t ≤ ξ ∧ ξ ≤ t := abs_le.mp habs
  have hgap : (0 : ℝ) < w₀ - t := by linarith
  have hminus : δ * (w₀ - t) ≤ δ * |ξ - w₀| := by
    refine mul_le_mul_of_nonneg_left ?_ hδ.le
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hξt.2] : (0 : ℝ) ≤ w₀ - ξ)]
    linarith [hξt.2]
  have hplus : δ * (w₀ - t) ≤ δ * |ξ + w₀| := by
    refine mul_le_mul_of_nonneg_left ?_ hδ.le
    rw [abs_of_nonneg (by linarith [hξt.1] : (0 : ℝ) ≤ ξ + w₀)]
    linarith [hξt.1]
  have hzero : (0 : ℝ) ≤ δ * |ξ| := by positivity
  have h₁ := soninScaledBumpTailBound_le hδ hminus
  have h₂ := soninScaledBumpTailBound_le hδ hplus
  have h₃ := soninScaledBumpTailBound_le hδ hzero
  have hmain := norm_fourier_soninScaledPacket_le m δ w₀ ξ hδ
  have hmean : (0 : ℝ) ≤ |soninScaledPacketMean m δ (2 * Real.pi * w₀)| := abs_nonneg _
  nlinarith [hmain, h₁, h₂, h₃, hmean]

end RHTower
