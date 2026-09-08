import GaloisForLFunctions.HTGeometry.GaussianSpectralGoldenRule
import GaloisForLFunctions.HTGeometry.BareGapPerturbativeReality

/-!
# Gaussian broadening versus finite bare-gap Born truncations

The spectral broadening in arXiv:2608.26494 is combined with the corpus's
self-energy boundary theorem and the finite matrix Born reality law. Every
fixed finite Born polynomial misses a strictly positive boundary rate.
The claim concerns these explicit finite matrix truncations; it is not an
identification of all electron-phonon diagrams with matrix Born words.
-/

open Filter MeasureTheory
open scoped Topology Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry


/-- Difference between the exact Gaussian spectral rate and a finite bare-gap Born rate. -/
def gaussianBareGapRateDefect {d k : ℕ} (e a x gap : ℝ)
    (addition : Fin d → Bool) (pairs : Fin d → ℕ) (excess : Fin d → Fin k → ℝ)
    (H : Matrix (Fin d) (Fin d) ℂ) (w : ℕ → ℝ) (N : ℕ) (i : Fin d) (eta : ℝ) : ℝ :=
  -2 * (levelSelfEnergy (displacedGaussianSpectralDensity e a) x eta).im +
    2 * (bareGapBornPolynomial x gap addition pairs excess H w N eta i i).im

/-- Every finite bare Born order misses the entire positive Gaussian boundary rate. -/
theorem tendsto_gaussianBareGapRateDefect {d k : ℕ} (e a x gap : ℝ)
    (addition : Fin d → Bool) (pairs : Fin d → ℕ) (excess : Fin d → Fin k → ℝ)
    (H : Matrix (Fin d) (Fin d) ℂ) (w : ℕ → ℝ) (N : ℕ) (i : Fin d) :
    Tendsto (gaussianBareGapRateDefect e a x gap addition pairs excess H w N i)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (𝓝 (displacedGaussianGoldenRuleRate e a x)) := by
  unfold gaussianBareGapRateDefect
  have hB := (tendsto_bareGapBornPolynomial_diag_im_zero x gap addition pairs excess H w N i).mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
  simpa only [mul_zero, add_zero] using
    (tendsto_displacedGaussian_selfEnergy_rate e a x).add (hB.const_mul 2)

/-- The boundary mismatch remains bounded away from zero for every fixed finite order. -/
theorem gaussianBareGapRateDefect_eventually_positive {d k : ℕ} (e a x gap : ℝ)
    (addition : Fin d → Bool) (pairs : Fin d → ℕ) (excess : Fin d → Fin k → ℝ)
    (H : Matrix (Fin d) (Fin d) ℂ) (w : ℕ → ℝ) (N : ℕ) (i : Fin d) :
    ∀ᶠ eta in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
      displacedGaussianGoldenRuleRate e a x / 2 <
        gaussianBareGapRateDefect e a x gap addition pairs excess H w N i eta := by
  apply (tendsto_gaussianBareGapRateDefect e a x gap addition pairs excess H w N i).eventually
  exact eventually_gt_nhds (by have := displacedGaussianGoldenRuleRate_pos e a x; linarith)

/-- No finite bare-gap truncation reproduces the Gaussian rate as the regulator vanishes. -/
theorem gaussianBareGapRateDefect_not_tendsto_zero {d k : ℕ} (e a x gap : ℝ)
    (addition : Fin d → Bool) (pairs : Fin d → ℕ) (excess : Fin d → Fin k → ℝ)
    (H : Matrix (Fin d) (Fin d) ℂ) (w : ℕ → ℝ) (N : ℕ) (i : Fin d) :
    ¬ Tendsto (gaussianBareGapRateDefect e a x gap addition pairs excess H w N i)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (𝓝 0) := by
  intro h
  have he := tendsto_nhds_unique
    (tendsto_gaussianBareGapRateDefect e a x gap addition pairs excess H w N i) h
  exact (ne_of_gt (displacedGaussianGoldenRuleRate_pos e a x)) he

end GaloisForLFunctions.HTGeometry
