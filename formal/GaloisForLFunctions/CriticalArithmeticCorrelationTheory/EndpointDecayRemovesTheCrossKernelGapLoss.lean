import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BoundaryVanishingControlsTheTouchingAutocorrelation
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanDensityHasQuadraticIncrementControl
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAtomCrossMatrixIsCloseToItsCenterKernel

/-!
# Endpoint decay pays the cross-kernel singularity

The inverse-square variation of the archimedean density is paired with the
quadratic endpoint decay of the actual autocorrelation before integration.
The resulting cross error stays bounded when the gap between supports closes.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory
open _root_.RHTower (archLevyDensity)

private theorem autocorr_eq_zero_off {g : ℝ → ℝ} {w z : ℝ}
    (hsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hz : z ∉ Icc (-w) w) :
    bumpAutocorr g z = 0 := by
  apply bumpAutocorr_eq_zero hsupp
  by_contra h
  exact hz ⟨by linarith only [neg_abs_le z, not_lt.mp h],
    (le_abs_self z).trans (not_lt.mp h)⟩

private theorem abs_density_shift_le {s w z : ℝ} (hw : 0 ≤ w)
    (hws : w < s) (hz : |z| ≤ w) :
    |archLevyDensity (s + z) - archLevyDensity s| ≤ 38 * w / (s - |z|) ^ 2 := by
  have ht : |z| < s := hz.trans_lt hws
  have hm : 0 < s - |z| := sub_pos.mpr ht
  have hs : 0 < s := hw.trans_lt hws
  have hp : 0 < s + |z| := add_pos_of_pos_of_nonneg hs (abs_nonneg z)
  have hsz : 0 < s + z := by linarith only [neg_abs_le z, hm]
  have h1 := archLevyDensity_antitoneOn hm hsz (by linarith only [neg_abs_le z])
  have h2 := archLevyDensity_antitoneOn hsz hp (by linarith only [le_abs_self z])
  have h3 := archLevyDensity_antitoneOn hm hs (by linarith only [abs_nonneg z])
  have h4 := archLevyDensity_antitoneOn hs hp (by linarith only [abs_nonneg z])
  have hvar : |archLevyDensity (s + z) - archLevyDensity s| ≤
      archLevyDensity (s - |z|) - archLevyDensity (s + |z|) := by
    rw [abs_le]
    constructor <;> linarith only [h1, h2, h3, h4]
  exact hvar.trans ((archLevyDensity_window_sub_le (abs_nonneg z) ht).trans
    (div_le_div_of_nonneg_right (by linarith only [hz]) (sq_nonneg _)))

/-- The cross-integral replacement has a bound independent of the support gap. -/
theorem abs_crossTerm_sub_le_endpoint_lipschitz {g : ℝ → ℝ} {w s L : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hw : 0 < w) (hws : w < s)
    (hL : 0 ≤ L) (hLip : ∀ x y, |g y - g x| ≤ L * |y - x|) :
    |atomCrossTerm g s - archLevyDensity s * (∫ u, g u) ^ 2| ≤ 19 * L ^ 2 * w ^ 3 := by
  let H : ℝ → ℝ := fun z =>
    (archLevyDensity (s + z) - archLevyDensity s) * bumpAutocorr g z
  let C : ℝ := (38 / 4) * L ^ 2 * w ^ 2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hGint : Integrable (bumpAutocorr g) := (integrable_mul_shift_prod hg hgc).integral_prod_left
  have hzero : ∀ z, z ∉ Icc (-w) w → H z = 0 := by
    intro z hz
    simp only [H, autocorr_eq_zero_off hsupp hz, mul_zero]
  have hpoint : ∀ z, |H z| ≤ C := by
    intro z
    by_cases hz : z ∈ Icc (-w) w
    · have habs : |z| ≤ w := abs_le.mpr hz
      have hd : 0 < s - |z| := sub_pos.mpr (habs.trans_lt hws)
      have ha : 0 ≤ w - |z| := sub_nonneg.mpr habs
      have hsq : (w - |z|) ^ 2 ≤ (s - |z|) ^ 2 := by
        have hle := sub_le_sub_right hws.le |z|
        simpa only [pow_two] using mul_le_mul hle hle ha hd.le
      have hratio : (w - |z|) ^ 2 / (s - |z|) ^ 2 ≤ 1 :=
        (div_le_one (sq_pos_of_pos hd)).mpr hsq
      calc
        |H z| = |archLevyDensity (s + z) - archLevyDensity s| * |bumpAutocorr g z| := abs_mul _ _
        _ ≤ (38 * w / (s - |z|) ^ 2) * ((L ^ 2 * w / 4) * (w - |z|) ^ 2) :=
          mul_le_mul (abs_density_shift_le hw.le hws habs)
            (abs_bumpAutocorr_le_endpoint_square hg hsupp hw.le hL hLip)
            (abs_nonneg _) (by positivity)
        _ = C * ((w - |z|) ^ 2 / (s - |z|) ^ 2) := by dsimp only [C]; ring
        _ ≤ C := (mul_le_mul_of_nonneg_left hratio hC).trans_eq (mul_one C)
    · rw [hzero z hz, abs_zero]
      exact hC
  have hHint : Integrable H := by
    apply integrable_of_bounded_of_vanish (a := -w) (b := w) (C := C) ?_ hzero hpoint
    exact ((_root_.RHTower.measurable_archLevyDensity.comp
      (measurable_const.add measurable_id)).sub measurable_const).aestronglyMeasurable.mul
        hGint.aestronglyMeasurable
  have hX : atomCrossTerm g s = ∫ z, archLevyDensity (s + z) * bumpAutocorr g z := by
    unfold atomCrossTerm
    rw [← integral_indicator measurableSet_Ioi]
    rw [← integral_add_right_eq_self
      (fun y => (Ioi (0 : ℝ)).indicator (fun y => archLevyDensity y * bumpAutocorr g (y - s)) y) s]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ Icc (-w) w
    · have hpos : z + s ∈ Ioi (0 : ℝ) := by
        show 0 < z + s
        linarith only [hz.1, hws]
      rw [Set.indicator_of_mem hpos, add_sub_cancel_right, add_comm z s]
    · rw [autocorr_eq_zero_off hsupp hz, mul_zero]
      by_cases hpos : z + s ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hpos, add_sub_cancel_right,
          autocorr_eq_zero_off hsupp hz, mul_zero]
      · rw [Set.indicator_of_notMem hpos]
  have hsplit : (∫ z, archLevyDensity (s + z) * bumpAutocorr g z) =
      (∫ z, H z) + archLevyDensity s * ∫ z, bumpAutocorr g z := by
    rw [← integral_const_mul, ← integral_add hHint (hGint.const_mul _)]
    congr 1
    funext z
    dsimp only [H]
    ring
  rw [hX, hsplit, integral_bumpAutocorr hg hgc, add_sub_cancel_right]
  have hrestrict : (∫ z, |H z|) = ∫ z in Icc (-w) w, |H z| := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
    intro z hz
    rw [hzero z hz, abs_zero]
  calc
    |∫ z, H z| ≤ ∫ z, |H z| := abs_integral_le_integral_abs
    _ = ∫ z in Icc (-w) w, |H z| := hrestrict
    _ ≤ ∫ _ in Icc (-w) w, C :=
      setIntegral_mono_on hHint.abs.integrableOn continuous_const.integrableOn_Icc
        measurableSet_Icc (fun z _ => hpoint z)
    _ = _ := by simp [C, show 0 ≤ w + w by positivity]; ring

/-- Every fixed smooth compact profile has a reciprocal-square cross-error
constant uniform over all widths and all positive gaps between supports. -/
theorem exists_profile_crossError_uniform {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ w s : ℝ, 0 < w → w < s →
      |atomCrossTerm (atomDilate φ w) s -
        archLevyDensity s * (∫ u, atomDilate φ w u) ^ 2| /
          (∫ u, atomDilate φ w u ^ 2) ≤ C * w ^ 2 / s ^ 2 := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hsupp
  obtain ⟨L, hL, hLip⟩ := ArithmeticCriticalityTheory.exists_lipschitz_bound_of_compactSupport
    (hφ.of_le (by norm_num)) hφc
  let A : ℝ := (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)
  let D : ℝ := L ^ 2 / (∫ u, φ u ^ 2)
  have hA : 0 ≤ A := div_nonneg (sq_nonneg _) hM.le
  have hD : 0 ≤ D := div_nonneg (sq_nonneg _) hM.le
  let C : ℝ := 1 + 152 * A + 76 * D
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro w s hw hws
  have hs : 0 < s := hw.trans hws
  obtain ⟨hg, hgsupp, hgc⟩ := atomDilate_facts hφ hsupp hw
  have hG : 0 < ∫ u, atomDilate φ w u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  have hAC : 152 * A ≤ C := by dsimp only [C]; linarith only [hD]
  have hDC : 76 * D ≤ C := by dsimp only [C]; linarith only [hA]
  by_cases hfar : 2 * w ≤ s
  · have hinv : 1 / (s - w) ^ 2 ≤ 4 / s ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hws)) (sq_pos_of_pos hs)).mpr
      have hle : s ≤ 2 * (s - w) := by linarith only [hfar]
      have hsq := mul_le_mul hle hle hs.le (by linarith only [hws] : 0 ≤ 2 * (s - w))
      nlinarith only [hsq]
    have hb := (abs_crossTerm_sub_le hg.continuous hgc hgsupp hw.le hws).trans
      (mul_le_mul_of_nonneg_right (archLevyDensity_window_sub_le hw.le hws)
        (sq_nonneg (∫ u, |atomDilate φ w u|)))
    calc
      _ ≤ ((38 * w / (s - w) ^ 2) * (∫ u, |atomDilate φ w u|) ^ 2) /
          (∫ u, atomDilate φ w u ^ 2) := div_le_div_of_nonneg_right hb hG.le
      _ = (38 * A * w ^ 2) * (1 / (s - w) ^ 2) := by
        rw [integral_abs_atomDilate hw, integral_atomDilate_sq hw]
        dsimp only [A]
        field_simp [hw.ne', hM.ne', (sub_pos.mpr hws).ne']
      _ ≤ (38 * A * w ^ 2) * (4 / s ^ 2) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (152 * A) * w ^ 2 / s ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hAC (sq_nonneg w)) (sq_nonneg s)
  · have hLipw : ∀ x y, |atomDilate φ w y - atomDilate φ w x| ≤ (L / w) * |y - x| := by
      intro x y
      have h := hLip (x / w) (y / w)
      change |φ (y / w) - φ (x / w)| ≤ _
      calc
        _ ≤ L * |y / w - x / w| := h
        _ = _ := by rw [← sub_div, abs_div, abs_of_pos hw]; ring
    have hb := abs_crossTerm_sub_le_endpoint_lipschitz hg.continuous hgc hgsupp hw hws
      (div_nonneg hL hw.le) hLipw
    have hquarter : (1 : ℝ) / 4 ≤ w ^ 2 / s ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hs)).mpr
      have hle : s ≤ 2 * w := (lt_of_not_ge hfar).le
      have hsq := mul_le_mul hle hle hs.le (by positivity : 0 ≤ 2 * w)
      nlinarith only [hsq]
    calc
      _ ≤ (19 * (L / w) ^ 2 * w ^ 3) / (∫ u, atomDilate φ w u ^ 2) :=
        div_le_div_of_nonneg_right hb hG.le
      _ = 19 * D := by
        rw [integral_atomDilate_sq hw]
        dsimp only [D]
        field_simp [hw.ne', hM.ne']
      _ = (76 * D) * (1 / 4) := by ring
      _ ≤ (76 * D) * (w ^ 2 / s ^ 2) := mul_le_mul_of_nonneg_left hquarter (by positivity)
      _ = (76 * D) * w ^ 2 / s ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hDC (sq_nonneg w)) (sq_nonneg s)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_crossTerm_sub_le_endpoint_lipschitz
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_profile_crossError_uniform
