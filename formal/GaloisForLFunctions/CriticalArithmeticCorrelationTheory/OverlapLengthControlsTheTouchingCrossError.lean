import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EndpointDecayRemovesTheCrossKernelGapLoss
import GaloisForLFunctions.ArithmeticIncidencePositivity.CubicGaugeSurplusPotential
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheMarkovFormFailsInsideTheSeparatedRegime

/-!
# Overlap length pays the touching singularity

The autocorrelation of a bounded interval-supported profile is bounded by its
height squared times the overlap length. Pairing this decay with the actual
Lévy density gives a cross-error bound independent of transition derivatives.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory
open _root_.RHTower (archLevyDensity)

/-- The actual autocorrelation is bounded by height squared times overlap length. -/
theorem abs_bumpAutocorr_le_overlap_length {g : ℝ → ℝ} {w B z : ℝ}
    (hg : Continuous g) (hsupp : ∀ u, u ∉ Icc 0 w → g u = 0)
    (hB : 0 ≤ B) (hheight : ∀ u, |g u| ≤ B) (hz : |z| ≤ w) :
    |bumpAutocorr g z| ≤ B ^ 2 * (w - |z|) := by
  have hpos (t : ℝ) (htw : t ≤ w) :
      |bumpAutocorr g t| ≤ B ^ 2 * (w - t) := by
    have heq : bumpAutocorr g t = ∫ u in Icc 0 (w - t), g u * g (u + t) := by
      unfold bumpAutocorr
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro u hu
      simp only [mem_Icc, not_and_or, not_le] at hu
      rcases hu with hu | hu
      · rw [hsupp u (fun h => (not_le_of_gt hu) h.1), zero_mul]
      · rw [hsupp (u + t) (fun h => by linarith only [hu, h.2]), mul_zero]
    have hc : Continuous fun u => |g u * g (u + t)| := by fun_prop
    rw [heq]
    calc
      _ ≤ ∫ u in Icc 0 (w - t), |g u * g (u + t)| := abs_integral_le_integral_abs
      _ ≤ ∫ _ in Icc (0 : ℝ) (w - t), B ^ 2 :=
        setIntegral_mono_on hc.integrableOn_Icc continuous_const.integrableOn_Icc
          measurableSet_Icc (fun u _ => by
            rw [abs_mul, pow_two]
            exact mul_le_mul (hheight u) (hheight (u + t)) (abs_nonneg _) hB)
      _ = _ := by simp [sub_nonneg.mpr htw, mul_comm]
  by_cases hz0 : 0 ≤ z
  · simpa only [abs_of_nonneg hz0] using hpos z ((le_abs_self z).trans hz)
  · have heven : bumpAutocorr g z = bumpAutocorr g (-z) := by
      unfold bumpAutocorr
      rw [← integral_add_right_eq_self (fun u => g u * g (u + z)) (-z)]
      congr 1
      funext u
      simp only [neg_add_cancel_right]
      ring
    rw [heven]
    simpa only [abs_of_nonpos (le_of_not_ge hz0), sub_neg_eq_add] using
      hpos (-z) (by simpa only [abs_of_nonpos (le_of_not_ge hz0)] using hz)

private theorem autocorr_off {g : ℝ → ℝ} {w z : ℝ}
    (hsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hz : z ∉ Icc (-w) w) :
    bumpAutocorr g z = 0 := by
  apply bumpAutocorr_eq_zero hsupp
  by_contra h
  exact hz ⟨by linarith only [neg_abs_le z, not_lt.mp h],
    (le_abs_self z).trans (not_lt.mp h)⟩

/-- A height bound pays the actual cross-integral singularity, with no derivative cost. -/
theorem abs_crossTerm_sub_le_height {g : ℝ → ℝ} {w s B : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hw : 0 < w) (hws : w < s)
    (hB : 0 ≤ B) (hheight : ∀ u, |g u| ≤ B) :
    |atomCrossTerm g s - archLevyDensity s * (∫ u, g u) ^ 2| ≤
      B ^ 2 * w * (1 + w / 2) := by
  let H : ℝ → ℝ := fun z =>
    (archLevyDensity (s + z) - archLevyDensity s) * bumpAutocorr g z
  let C : ℝ := B ^ 2 * (1 / 2 + w / 4)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hGint : Integrable (bumpAutocorr g) := (integrable_mul_shift_prod hg hgc).integral_prod_left
  have hzero : ∀ z, z ∉ Icc (-w) w → H z = 0 := by
    intro z hz
    simp only [H, autocorr_off hsupp hz, mul_zero]
  have hpoint : ∀ z, |H z| ≤ C := by
    intro z
    by_cases hz : z ∈ Icc (-w) w
    · have habs : |z| ≤ w := abs_le.mpr hz
      have hd : 0 < s - |z| := sub_pos.mpr (habs.trans_lt hws)
      have hs : 0 < s := hw.trans hws
      have hsz : 0 < s + z := by linarith only [neg_abs_le z, hd]
      have ha : 0 ≤ w - |z| := sub_nonneg.mpr habs
      have hsmall : w - |z| ≤ s - |z| := sub_le_sub_right hws.le _
      have hvar : |archLevyDensity (s + z) - archLevyDensity s| ≤
          archLevyDensity (s - |z|) := by
        have h1 := archLevyDensity_antitoneOn hd hsz (by linarith only [neg_abs_le z])
        have h2 := archLevyDensity_antitoneOn hd hs (by linarith only [abs_nonneg z])
        have h3 := (_root_.RHTower.archLevyDensity_pos hsz).le
        have h4 := (_root_.RHTower.archLevyDensity_pos hs).le
        rw [abs_le]
        constructor <;> linarith only [h1, h2, h3, h4]
      have hratio : (w - |z|) / (s - |z|) ≤ 1 := (div_le_one hd).mpr hsmall
      have hlength : w - |z| ≤ w := sub_le_self _ (abs_nonneg z)
      calc
        |H z| = |archLevyDensity (s + z) - archLevyDensity s| * |bumpAutocorr g z| := abs_mul _ _
        _ ≤ (1 / (2 * (s - |z|)) + 1 / 4) * (B ^ 2 * (w - |z|)) :=
          mul_le_mul (hvar.trans (ArithmeticIncidencePositivity.archLevyDensity_le_inv hd))
            (abs_bumpAutocorr_le_overlap_length hg hsupp hB hheight habs)
            (abs_nonneg _) (by positivity)
        _ = B ^ 2 * ((1 / 2) * ((w - |z|) / (s - |z|)) + (w - |z|) / 4) := by ring
        _ ≤ B ^ 2 * ((1 / 2) * 1 + w / 4) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left hratio (by norm_num))
              (div_le_div_of_nonneg_right hlength (by norm_num))) (sq_nonneg B)
        _ = C := by dsimp only [C]; ring
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
    · rw [autocorr_off hsupp hz, mul_zero]
      by_cases hpos : z + s ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hpos, add_sub_cancel_right, autocorr_off hsupp hz, mul_zero]
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

/-- For bounded widths, height and mass give a derivative-free reciprocal-square budget. -/
theorem profile_crossError_le_height {φ : ℝ → ℝ} {B : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (hB : 0 ≤ B) (hheight : ∀ u, |φ u| ≤ B)
    {w s : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) (hws : w < s) :
    |atomCrossTerm (atomDilate φ w) s -
      archLevyDensity s * (∫ u, atomDilate φ w u) ^ 2| /
        (∫ u, atomDilate φ w u ^ 2) ≤
      ((152 * (∫ u, |φ u|) ^ 2 + 6 * B ^ 2) / (∫ u, φ u ^ 2)) * w ^ 2 / s ^ 2 := by
  let A : ℝ := (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)
  let D : ℝ := B ^ 2 / (∫ u, φ u ^ 2)
  have hA : 0 ≤ A := div_nonneg (sq_nonneg _) hM.le
  have hD : 0 ≤ D := div_nonneg (sq_nonneg _) hM.le
  let C : ℝ := 152 * A + 6 * D
  have hCeq : (152 * (∫ u, |φ u|) ^ 2 + 6 * B ^ 2) / (∫ u, φ u ^ 2) = C := by
    dsimp only [C, A, D]
    ring
  rw [hCeq]
  have hs : 0 < s := hw.trans hws
  obtain ⟨hg, hgsupp, hgc⟩ := atomDilate_facts hφ hsupp hw
  have hG : 0 < ∫ u, atomDilate φ w u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  have hAC : 152 * A ≤ C := by dsimp only [C]; linarith only [hD]
  have hDC : 6 * D ≤ C := by dsimp only [C]; linarith only [hA]
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
  · have hb := abs_crossTerm_sub_le_height hg.continuous hgc hgsupp hw hws hB
      (fun u => hheight (u / w))
    have hquarter : (1 : ℝ) / 4 ≤ w ^ 2 / s ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hs)).mpr
      have hle : s ≤ 2 * w := (lt_of_not_ge hfar).le
      have hsq := mul_le_mul hle hle hs.le (by positivity : 0 ≤ 2 * w)
      nlinarith only [hsq]
    calc
      _ ≤ (B ^ 2 * w * (1 + w / 2)) / (∫ u, atomDilate φ w u ^ 2) :=
        div_le_div_of_nonneg_right hb hG.le
      _ = D * (1 + w / 2) := by
        rw [integral_atomDilate_sq hw]
        dsimp only [D]
        field_simp [hw.ne', hM.ne']
      _ ≤ D * (3 / 2) := mul_le_mul_of_nonneg_left (by linarith only [hw1]) hD
      _ = (6 * D) * (1 / 4) := by ring
      _ ≤ (6 * D) * (w ^ 2 / s ^ 2) := mul_le_mul_of_nonneg_left hquarter (by positivity)
      _ = (6 * D) * w ^ 2 / s ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hDC (sq_nonneg w)) (sq_nonneg s)

/-- The same cross-error budget works as smooth plateaus approach the indicator. -/
theorem plateau_crossError_le_uniform {η w s : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hw : 0 < w) (hw1 : w ≤ 1) (hws : w < s) :
    |atomCrossTerm (atomDilate (plateau η) w) s -
      archLevyDensity s * (∫ u, atomDilate (plateau η) w u) ^ 2| /
        (∫ u, atomDilate (plateau η) w u ^ 2) ≤ 316 * w ^ 2 / s ^ 2 := by
  have hMhalf : (1 / 2 : ℝ) ≤ ∫ u, plateau η u ^ 2 := by
    have h := integral_plateau_sq_ge hη (by linarith only [hη4])
    linarith only [h, hη4]
  have hM : 0 < ∫ u, plateau η u ^ 2 := lt_of_lt_of_le (by norm_num) hMhalf
  have hI0 : 0 ≤ ∫ u, |plateau η u| := integral_nonneg fun u => abs_nonneg _
  have hI1 := integral_abs_plateau_le hη
  have hIsq : (∫ u, |plateau η u|) ^ 2 ≤ 1 := by nlinarith only [hI0, hI1]
  have hc : (152 * (∫ u, |plateau η u|) ^ 2 + 6 * (1 : ℝ) ^ 2) /
      (∫ u, plateau η u ^ 2) ≤ 316 := by
    apply (div_le_iff₀ hM).mpr
    nlinarith only [hIsq, hMhalf]
  exact (profile_crossError_le_height (contDiff_plateau η) (fun u hu => plateau_eq_zero hη hu)
    hM zero_le_one (fun u => by rw [abs_of_nonneg (plateau_nonneg u)]; exact plateau_le_one u)
    hw hw1 hws).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (sq_nonneg w)) (sq_nonneg s))

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_crossTerm_sub_le_height

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.profile_crossError_le_height

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.plateau_crossError_le_uniform
