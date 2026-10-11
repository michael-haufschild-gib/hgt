import GaloisForLFunctions.RHTower.WeilLogShiftRawLipschitzComparison

/-! Raw transport and uniform Lipschitz comparison vanish along every quadratic-width family. -/

open MeasureTheory Filter Topology

noncomputable section
namespace RHTower

theorem tendsto_finiteWeilCanonicalRawWasserstein_zero (t : ℕ → ℕ) :
    Tendsto (fun r => finiteWeilCanonicalRawWasserstein r (2 * (r + 1) ^ 2 + t r))
      atTop (𝓝 0) :=
  squeeze_zero (fun r => finiteWeilCanonicalRawWasserstein_nonneg r _)
    (fun r => finiteWeilCanonicalRawWasserstein_le_gap r _)
    (tendsto_finiteWeilCanonicalRawFluctuationGap_zero t)

theorem tendsto_finiteWeilCanonicalRawLipschitzDual_zero (t : ℕ → ℕ) :
    Tendsto (fun r => finiteWeilCanonicalRawLipschitzDual r (2 * (r + 1) ^ 2 + t r))
      atTop (𝓝 0) :=
  squeeze_zero (fun r => finiteWeilCanonicalRawLipschitzDual_nonneg r _)
    (fun r => finiteWeilCanonicalRawLipschitzDual_le_gap r _)
    (tendsto_finiteWeilCanonicalRawFluctuationGap_zero t)

theorem tendsto_finiteWeilCanonicalRawLipschitz_integral_gap_zero (t : ℕ → ℕ) (L : NNReal)
    (f : ℕ → {f : ℝ → ℝ // LipschitzWith L f}) :
    Tendsto (fun r =>
      |(∫ x, (f r : ℝ → ℝ) x ∂(finiteWeilCanonicalRawIndexLaw r (2 * (r + 1) ^ 2 + t r) : Measure ℝ)) -
        (∫ x, (f r : ℝ → ℝ) x ∂(finiteWeilCanonicalRawCorrectionLaw r (2 * (r + 1) ^ 2 + t r) : Measure ℝ))|)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun r => abs_nonneg _)
    (fun r => finiteWeilCanonicalRawLipschitz_integral_gap r _ L (f r : ℝ → ℝ) (f r).property)
  simpa only [mul_zero] using
    (tendsto_finiteWeilCanonicalRawFluctuationGap_zero t).const_mul (L : ℝ)

end RHTower
