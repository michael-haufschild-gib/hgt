import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.Readout
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity


/-!
# Positive on-line weighted images

Absolute Lorentzian mass gives absolute convergence of every compact smooth
weighted image. On the critical line, a diagonal image is the positive weighted
Fourier energy, so it bounds each finite sub-sum.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23

/-- Absolute Lorentzian mass makes every compact smooth weighted image absolutely summable. -/
theorem summable_norm_weighted_pointImage {w : ℂ → ℂ}
    (hstrip : ∀ z, w z ≠ 0 → 0 ≤ z.re ∧ z.re ≤ 1)
    (hw : Summable fun z => ‖w z‖ / (1 + Complex.normSq (gammaOf z)))
    {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Summable fun z => ‖w z * pointImage f g z‖ := by
  obtain ⟨Cf, hCf, hF⟩ := _root_.RHTower.EvenSector.exists_norm_paperFT_le_of_compact hf hfc (1 / 2)
  obtain ⟨Cg, hCg, hG⟩ := _root_.RHTower.EvenSector.exists_norm_paperFT_le_of_compact hg hgc (1 / 2)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_)
    (hw.mul_left (Cf * Cg))
  by_cases hz : w z = 0
  · simp only [hz, zero_mul, norm_zero, zero_div, mul_zero, le_refl]
  have hzi := abs_im_gammaOf_le (hstrip z hz).1 (hstrip z hz).2
  have hFz := hF (gammaOf z) hzi
  have hGz := hG (conj (gammaOf z)) (by simpa only [Complex.conj_im, abs_neg] using hzi)
  rw [Complex.norm_conj] at hGz
  have hG0 : ‖paperFT g (conj (gammaOf z))‖ ≤ Cg :=
    hGz.trans (div_le_self hCg (by linarith only [sq_nonneg ‖gammaOf z‖]))
  rw [norm_mul, pointImage, norm_mul, Complex.norm_conj]
  calc ‖w z‖ * (‖paperFT f (gammaOf z)‖ * ‖paperFT g (conj (gammaOf z))‖)
      ≤ ‖w z‖ * (Cf / (1 + ‖gammaOf z‖ ^ 2) * Cg) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hFz hG0 (norm_nonneg _) (by positivity)) (norm_nonneg _)
    _ = (Cf * Cg) * (‖w z‖ / (1 + Complex.normSq (gammaOf z))) := by
      rw [Complex.normSq_eq_norm_sq]
      ring

private theorem onLine_weighted_pointImage {w : ℂ → ℝ}
    (hline : ∀ z, w z ≠ 0 → z.re = 1 / 2) (f : ℝ → ℂ) (z : ℂ) :
    (w z : ℂ) * pointImage f f z = (w z * ‖paperFT f z.im‖ ^ 2 : ℝ) := by
  by_cases hz : w z = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul]
  have hγ : gammaOf z = (z.im : ℂ) := by
    apply Complex.ext
    · rw [gammaOf_re_eq_im, Complex.ofReal_re]
    · rw [gammaOf_im_eq, hline z hz, sub_self, Complex.ofReal_im]
  rw [pointImage, hγ, Complex.conj_ofReal, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- An on-line real-weighted diagonal image is its ordinary weighted Fourier energy. -/
theorem weightedImage_onLine_diagonal {w : ℂ → ℝ}
    (hline : ∀ z, w z ≠ 0 → z.re = 1 / 2)
    (hw : Summable fun z => |w z| / (1 + Complex.normSq (gammaOf z)))
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (Summable fun z => w z * ‖paperFT f z.im‖ ^ 2) ∧
      (weightedImage (fun z => (w z : ℂ)) f f).re = ∑' z, w z * ‖paperFT f z.im‖ ^ 2 := by
  have hs : Summable fun z => (w z : ℂ) * pointImage f f z :=
    (summable_norm_weighted_pointImage (fun z hz => by
      have h := hline z (Complex.ofReal_ne_zero.mp hz)
      rw [h]
      norm_num)
      (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hw) hf hfc hf hfc).of_norm
  have hr : Summable fun z => w z * ‖paperFT f z.im‖ ^ 2 :=
    Complex.summable_ofReal.mp (hs.congr (onLine_weighted_pointImage hline f))
  refine ⟨hr, ?_⟩
  rw [weightedImage, Complex.re_tsum hs]
  apply tsum_congr
  intro z
  rw [onLine_weighted_pointImage hline f, Complex.ofReal_re]

/-- Every finite positive on-line weighted Fourier sum is bounded by the diagonal image. -/
theorem finite_sum_le_re_weightedImage_onLine {w : ℂ → ℝ}
    (hw0 : ∀ z, 0 ≤ w z) (hline : ∀ z, w z ≠ 0 → z.re = 1 / 2)
    (hw : Summable fun z => |w z| / (1 + Complex.normSq (gammaOf z)))
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (s : Finset ℂ) :
    (∑ z ∈ s, w z * ‖paperFT f z.im‖ ^ 2) ≤
      (weightedImage (fun z => (w z : ℂ)) f f).re := by
  obtain ⟨hs, he⟩ := weightedImage_onLine_diagonal hline hw hf hfc
  rw [he]
  exact hs.sum_le_tsum s (fun z _ => mul_nonneg (hw0 z) (sq_nonneg _))

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.summable_norm_weighted_pointImage
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.weightedImage_onLine_diagonal
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.finite_sum_le_re_weightedImage_onLine
