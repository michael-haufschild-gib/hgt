import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTranslatedCorrelationHasADoublePole
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicEisensteinCorrectionIsBoundedOnVerticalStrips

/-!
# Vertical bounds for the full and translated theta pairings

The compact-height seed kernels vanish below height two and decay as `v^(-13/3)`.
Their Mellin transforms are uniformly bounded on every smaller left half-plane.
The renormalized theta squares are fixed `L²` test vectors, so their correction
pairings inherit the uniform self-adjoint resolvent bound away from `Re s=1`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

private theorem mellin_tail_bounded (f : ℝ → ℂ) (q B : ℝ) (hB : B < q)
    (hz : ∀ v : ℝ, v ≤ 2 → f v = 0)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 2 ≤ v → ‖f v‖ ≤ C * v ^ (-q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ≤ B → ‖mellin f s‖ ≤ C := by
  obtain ⟨D, hD, hd⟩ := hb
  let g : ℝ → ℝ := (Ioi 2).indicator (fun v => D * v ^ (B - 1 - q))
  have hg : Integrable g :=
    (integrable_indicator_iff measurableSet_Ioi).2
      ((integrableOn_Ioi_rpow_of_lt (by linarith : B - 1 - q < -1)
      (by norm_num : (0 : ℝ) < 2)).const_mul D)
  refine ⟨∫ v in Ioi (0 : ℝ), g v, ?_, ?_⟩
  · apply integral_nonneg
    intro v
    exact indicator_nonneg (fun v hv => mul_nonneg hD (Real.rpow_nonneg (by have hv' : 2 < v := hv; linarith) _)) v
  · intro s hs
    unfold mellin
    apply norm_integral_le_of_norm_le hg.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := hv
    by_cases hv2 : 2 < v
    · dsimp only [g]
      rw [indicator_of_mem (s := Ioi (2 : ℝ)) hv2, norm_smul,
        Complex.norm_cpow_eq_rpow_re_of_pos hv0]
      simp only [Complex.sub_re, Complex.one_re]
      calc
        _ ≤ v ^ (B - 1) * (D * v ^ (-q)) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
            (hd v hv2.le) (norm_nonneg _) (Real.rpow_nonneg hv0.le _)
        _ = D * v ^ (B - 1 - q) := by
          rw [mul_left_comm, ← Real.rpow_add hv0]
          congr 2
    · dsimp only [g]
      rw [hz v (not_lt.mp hv2), smul_zero, norm_zero, indicator_of_notMem (s := Ioi (2 : ℝ)) hv2]

/-- Both cusp seed pairings are bounded on every left half-plane strictly below `13/3`. -/
theorem thetaSeedPairings_bounded (B : ℝ) (hB : B < 13 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ≤ B →
      ‖seedPair s‖ ≤ C ∧ ‖transSeedPair s‖ ≤ C := by
  obtain ⟨C, hC, hc⟩ := mellin_tail_bounded seedKernel (13 / 3) B hB
    seedKernel_eq_zero (by simpa only [neg_div] using norm_seedKernel_le)
  obtain ⟨D, hD, hd⟩ := mellin_tail_bounded transSeedKernel (13 / 3) B hB
    transSeedKernel_eq_zero (by simpa only [neg_div] using norm_transSeedKernel_le)
  refine ⟨max C D, le_trans hC (le_max_left _ _), fun s hs => ?_⟩
  rw [seedPair_eq_mellin, transSeedPair_eq_mellin]
  exact ⟨(hc s hs).trans (le_max_left _ _), (hd s hs).trans (le_max_right _ _)⟩

open MetaplecticMobiusDescent.CubicEisenstein

/-- Both actual correction pairings are uniformly bounded on vertical strips right of one. -/
theorem thetaCorrectionPairings_bounded (a B : ℝ) (ha : 1 < a) (haB : a ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ B → 1 ≤ |s.im| →
      ‖corrPair s‖ ≤ C ∧ ‖transCorrPair s‖ ≤ C := by
  have hB : 0 ≤ B := by linarith
  obtain ⟨D, hD, hd⟩ := kernelEisensteinL2Correction_vertical_bound 2 3
    (by norm_num) (by norm_num) B (a - 1) hB (by linarith)
  let F := levelPairing renormalizedThetaSq renormalizedThetaSq_memLp
  let G := levelPairing translatedRenormalized translatedRenormalized_memLp
  refine ⟨(‖F‖ + ‖G‖) * D, mul_nonneg (add_nonneg (norm_nonneg F) (norm_nonneg G)) hD, ?_⟩
  intro s hs hsb ht
  have hc : ‖eisensteinCorrection s‖ ≤ D := hd s
    (abs_le.mpr ⟨by linarith, hsb⟩)
    ((by linarith : a - 1 ≤ s.re - 1).trans (le_abs_self _)) ht
  constructor
  · change ‖F (eisensteinCorrection s)‖ ≤ _
    calc
      _ ≤ ‖F‖ * ‖eisensteinCorrection s‖ := F.le_opNorm _
      _ ≤ ‖F‖ * D := mul_le_mul_of_nonneg_left hc (norm_nonneg F)
      _ ≤ _ := by nlinarith only [mul_nonneg (norm_nonneg G) hD]
  · change ‖G (eisensteinCorrection s)‖ ≤ _
    calc
      _ ≤ ‖G‖ * ‖eisensteinCorrection s‖ := G.le_opNorm _
      _ ≤ ‖G‖ * D := mul_le_mul_of_nonneg_left hc (norm_nonneg G)
      _ ≤ _ := by nlinarith only [mul_nonneg (norm_nonneg F) hD]

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
