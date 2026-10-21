import GaloisForLFunctions.ArithmeticCriticalityTheory.ThreeTenthsSharpGaugeWeilPositivity
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTentActualZetaDetectionAndFullZeroFormBridge
import GaloisForLFunctions.SquareRootThreshold.ZetaWeilPositivityBelowApertureOneHundredth

/-!
# Weil positivity of `ζ` through aperture `3/10`

Every complex `C²` test supported in `[−3/10, 3/10]` satisfies
`Re W_ζ(f, f) ≥ (1/5000) ∫ |f|²` (`zetaZeroConfig_re_W_ge_of_aperture_le_threeTenths`), against the
aperture `1/100` of the three archimedean bands.

The zero-side form splits over real and imaginary parts, `Re W_ζ(f, f) = Ẑ(Re f) + Ẑ(Im f)`, where
`Ẑ` is the full zero form of real tests. Any all-profile window `Ẑ(F) ≥ c ∫ F²` on `[−A, A]`
therefore transfers to complex tests with the same constant (`zetaZeroConfig_re_W_ge_of_window`);
the sharp-gauge window `A = 3/10`, `c = 1/5000` is the present one. Height-window positivity
follows for windows of aperture `3/10`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticPositivityTheory

/-- **Transfer of an all-profile window.** If every real `C²_c` test supported in `[−A, A]` has
`Ẑ(F) ≥ c ∫ F²`, then every complex `C²` test supported in `[−A, A]` has
`Re W_ζ(f, f) ≥ c ∫ |f|²`. -/
theorem zetaZeroConfig_re_W_ge_of_window {A c : ℝ}
    (hwin : ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, A < |x| → F x = 0) →
      c * ∫ x, F x ^ 2 ≤ fullZeroForm F)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-A) A) :
    c * ∫ x, ‖f x‖ ^ 2 ≤ (zetaZeroConfig.W f f).re := by
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport f).trans hfs)
  have hzero : ∀ x, A < |x| → f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hfs hmem
      rw [mem_Icc] at this
      exact absurd (abs_le.mpr this) (not_le.mpr hx)
  have hRe : ContDiff ℝ 2 (fun u => (f u).re) := Complex.reCLM.contDiff.comp hf
  have hIm : ContDiff ℝ 2 (fun u => (f u).im) := Complex.imCLM.contDiff.comp hf
  have hRec : HasCompactSupport (fun u => (f u).re) := hfc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have hImc : HasCompactSupport (fun u => (f u).im) := hfc.comp_left (g := fun z : ℂ => z.im) (by simp)
  have h1 := hwin _ hRe hRec fun x hx => by simp [hzero x hx]
  have h2 := hwin _ hIm hImc fun x hx => by simp [hzero x hx]
  have hint (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
      Integrable (fun x => g x ^ 2) volume := by
    have hs : HasCompactSupport (fun x => g x ^ 2) :=
      HasCompactSupport.of_support_subset_isCompact hgc.isCompact fun x hx =>
        subset_tsupport g (by simpa using hx)
    exact (hg.pow 2).integrable_of_hasCompactSupport hs
  have hsplit : ∫ x, ‖f x‖ ^ 2 = (∫ x, (f x).re ^ 2) + ∫ x, (f x).im ^ 2 := by
    rw [← integral_add (hint _ hRe.continuous hRec) (hint _ hIm.continuous hImc)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [zeta_W_re_eq_fullZeroForm_re_add_im hf hfc, hsplit, mul_add]
  exact add_le_add h1 h2

/-- **Weil positivity of `ζ` through aperture `3/10`.** -/
theorem zetaZeroConfig_re_W_ge_of_aperture_le_threeTenths {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-(3 / 10)) (3 / 10)) :
    1 / 5000 * ∫ x, ‖f x‖ ^ 2 ≤ (zetaZeroConfig.W f f).re :=
  zetaZeroConfig_re_W_ge_of_window (fun _ hF hFc hs => fullZeroForm_ge_of_support_le_threeTenths hF hFc hs)
    hf hfs

theorem zetaZeroConfig_re_W_nonneg_of_aperture_le_threeTenths {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-(3 / 10)) (3 / 10)) : 0 ≤ (zetaZeroConfig.W f f).re :=
  le_trans (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
    (zetaZeroConfig_re_W_ge_of_aperture_le_threeTenths hf hfs)

/-- **Windowed positivity for `ζ` at aperture `3/10`.** For every window supported in
`[−3/10, 3/10]` and every test of arbitrary aperture, the windowed Weil form of the zeros of `ζ`
has nonnegative real part. -/
theorem re_windowedW_zetaZeroConfig_nonneg_of_threeTenths {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-(3 / 10)) (3 / 10)) :
    0 ≤ (windowedW zetaZeroConfig f η).re :=
  re_windowedW_nonneg_of_aperture_nonneg _ temperedConfig_zetaZeroConfig
    (fun _ hg hgs => zetaZeroConfig_re_W_nonneg_of_aperture_le_threeTenths hg hgs) hf hfc hη hηs

end GaloisForLFunctions.SquareRootThreshold
