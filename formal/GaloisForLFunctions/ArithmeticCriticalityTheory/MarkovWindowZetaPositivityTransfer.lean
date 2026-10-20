import GaloisForLFunctions.ArithmeticCriticalityTheory.PoleConductanceWindowWeilPositivity
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTentActualZetaDetectionAndFullZeroFormBridge
import GaloisForLFunctions.SquareRootThreshold.ZetaSmallApertureHeightWindowPositivity
import GaloisForLFunctions.SquareRootThreshold.HeightWindowAverageRepresentation
import GaloisForLFunctions.RHTower.CHMDTranslatedPrimitiveSource

/-!
# The Markov window transferred: zeta positivity on every window of length `21/100`

The Markov-window theorem (`fullZeroForm_ge_of_support_le_sharp`) gives `Ẑ(F) ≥ (1/30) ∫ F²` for real
`F ∈ C²_c` supported in `[−21/200, 21/200]`. Three consequences:

* **Every window** (`fullZeroForm_ge_of_support_window`). `Ẑ` depends on `F` only through its
  autocorrelation, so it is translation invariant (`fullZeroForm_translate`), and the bound holds for
  tests supported in any interval of length `21/100`.
* **Complex tests** (`zetaZeroConfig_re_W_ge_of_support_le`). The real part of the zero-side Weil form of
  `ζ` splits over real and imaginary parts (`zeta_W_re_eq_fullZeroForm_re_add_im`), so
  `Re W_ζ(g, g) ≥ (1/30) ∫ |g|²` for every complex `g ∈ C²_c` supported in `[−21/200, 21/200]`.
* **Height windows** (`re_windowedW_zetaZeroConfig_nonneg_of_markovWindow`,
  `re_integral_heightShift_zetaZeroConfig_nonneg_of_markovWindow`). The windowed Weil form and the
  height-averaged Weil form of `ζ` are nonnegative for every window supported in `[−21/200, 21/200]`
  and every test of any aperture: the aperture premise of the height-window machinery
  (`re_windowedW_nonneg_of_aperture_nonneg`, `re_integral_heightShift_nonneg_of_aperture_nonneg`) is
  discharged at `21/200`, against `1/100` from the Fourier bound
  (`re_windowedW_zetaZeroConfig_nonneg_of_hundredth`).
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar
open GaloisForLFunctions.SquareRootThreshold
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- `Ẑ` is translation invariant: it depends on a test only through its autocorrelation. -/
theorem fullZeroForm_translate {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) (c : ℝ) :
    fullZeroForm (RHTower.CHMDTranslation.translate F c) = fullZeroForm F := by
  have hFt : HasCompactSupport (RHTower.CHMDTranslation.translate F c) :=
    hFc.comp_homeomorph (Homeomorph.subRight c)
  have hw := funext (RHTower.CHMDTranslation.weilTest_translate F c)
  rw [GaloisForLFunctions.ArithmeticPositivityTheory.fullZeroForm_eq_re_weilFullFunctional
      (RHTower.CHMDTranslation.continuous_translate hF c) hFt,
    GaloisForLFunctions.ArithmeticPositivityTheory.fullZeroForm_eq_re_weilFullFunctional hF hFc, hw]

/-- **Weil positivity on every window of length `21/100`.** -/
theorem fullZeroForm_ge_of_support_window {F : ℝ → ℝ} {c : ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hsupp : ∀ x, 21 / 200 < |x - c| → F x = 0) :
    1 / 30 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set G : ℝ → ℝ := RHTower.CHMDTranslation.translate F (-c) with hG
  have hGd : ContDiff ℝ 2 G := by
    show ContDiff ℝ 2 fun x => F (x - -c)
    exact hF.comp (contDiff_id.sub contDiff_const)
  have hGc : HasCompactSupport G := by
    show HasCompactSupport fun x => F (x - -c)
    exact hFc.comp_homeomorph (Homeomorph.subRight (-c))
  have hGs : ∀ x, 21 / 200 < |x| → G x = 0 := fun x hx => by
    simp only [hG, RHTower.CHMDTranslation.translate, sub_neg_eq_add]
    exact hsupp _ (by rwa [add_sub_cancel_right])
  have h := fullZeroForm_ge_of_support_le_sharp hGd hGc hGs
  have hback : RHTower.CHMDTranslation.translate G c = F := funext fun x => by
    simp only [hG, RHTower.CHMDTranslation.translate, sub_neg_eq_add, sub_add_cancel]
  have hZ := fullZeroForm_translate hGd.continuous hGc c
  rw [hback] at hZ
  have hI : (∫ x, G x ^ 2) = ∫ x, F x ^ 2 := by
    simp only [hG, RHTower.CHMDTranslation.translate]
    exact integral_sub_right_eq_self (fun x => F x ^ 2) (-c)
  rw [hZ, ← hI]
  exact h

/-- **Coercive zeta positivity for complex tests on the Markov window.** -/
theorem zetaZeroConfig_re_W_ge_of_support_le {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Icc (-(21 / 200)) (21 / 200)) :
    1 / 30 * ∫ x, ‖g x‖ ^ 2 ≤ (zetaZeroConfig.W g g).re := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hzero : ∀ x, 21 / 200 < |x| → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hgs h
      rw [mem_Icc] at this
      exact absurd (abs_le.mpr this) (not_le.mpr hx)
  have hre : ContDiff ℝ 2 fun u => (g u).re := Complex.reCLM.contDiff.comp hg
  have him : ContDiff ℝ 2 fun u => (g u).im := Complex.imCLM.contDiff.comp hg
  have hrec : HasCompactSupport fun u => (g u).re := hgc.comp_left Complex.zero_re
  have himc : HasCompactSupport fun u => (g u).im := hgc.comp_left Complex.zero_im
  have h1 := fullZeroForm_ge_of_support_le_sharp hre hrec fun x hx => by simp [hzero x hx]
  have h2 := fullZeroForm_ge_of_support_le_sharp him himc fun x hx => by simp [hzero x hx]
  have hsplit := GaloisForLFunctions.ArithmeticPositivityTheory.zeta_W_re_eq_fullZeroForm_re_add_im
    hg hgc
  have i1 : Integrable fun x => (g x).re ^ 2 :=
    (hre.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hrec)
  have i2 : Integrable fun x => (g x).im ^ 2 :=
    (him.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq himc)
  have hnorm : (∫ x, ‖g x‖ ^ 2) = (∫ x, (g x).re ^ 2) + ∫ x, (g x).im ^ 2 := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hsplit, hnorm]
  linarith

/-- **Windowed positivity for `ζ` on the Markov window.** For every window supported in
`[−21/200, 21/200]` and every test of arbitrary aperture, the windowed Weil form of the zeros of `ζ`
has nonnegative real part. -/
theorem re_windowedW_zetaZeroConfig_nonneg_of_markovWindow {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-(21 / 200)) (21 / 200)) :
    0 ≤ (windowedW zetaZeroConfig f η).re :=
  re_windowedW_nonneg_of_aperture_nonneg _ temperedConfig_zetaZeroConfig
    (fun _ hg hgs => le_trans (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
      (zetaZeroConfig_re_W_ge_of_support_le hg hgs)) hf hfc hη hηs

/-- **Height-window positivity for `ζ` on the Markov window.** For every window `η` supported in
`[−21/200, 21/200]` and every test `f`, `∫ |h_η(−2πξ)|² W_ζ(S_ξ f, S_ξ f) dξ` has nonnegative real
part. -/
theorem re_integral_heightShift_zetaZeroConfig_nonneg_of_markovWindow {f η : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-(21 / 200)) (21 / 200)) :
    0 ≤ (∫ ξ : ℝ, ((‖paperFT η (-(2 * Real.pi * (ξ : ℂ)))‖ ^ 2 : ℝ) : ℂ) *
      zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re :=
  re_integral_heightShift_nonneg_of_aperture_nonneg _ temperedConfig_zetaZeroConfig
    (fun _ hg hgs => le_trans (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
      (zetaZeroConfig_re_W_ge_of_support_le hg hgs)) hf hfc hη hηs

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
