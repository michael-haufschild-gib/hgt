import GaloisForLFunctions.RHTower.PaperEGCCompactifiedCorrection
import GaloisForLFunctions.HTGeometry.PaperSummableFourierCopies

/-!
# Paper Fourier reconstruction of the complete EGC correction

All prescribed shift scales, every multiplicity copy, and their complete correction share one
exceptional null set for literal Fourier convergence. The normal majorant also lets every
Fourier coefficient and every finite projection retain the full copy row.
-/

namespace RHTower

noncomputable section
open Filter MeasureTheory GaloisForLFunctions.HTGeometry
open scoped Topology BigOperators

/-- Continuous compactified profile of one actual Xi multiplicity copy. -/
def paperEGCCopyContinuous (eps x : PaperEGCSmallParameter) (q : XiZeroCopy) : C(ℝ, ℂ) :=
  ⟨fun θ => paperEGCCircleCopy eps x θ q, continuous_paperEGCCircleCopy eps x q⟩

/-- The complete correction occupies `none`; individual copies occupy `some q`. -/
def paperEGCFourierFamily : ℕ × Option XiZeroCopy → C(ℝ, ℂ)
  | (n, none) => ⟨paperEGCCompactifiedCorrection (paperEGCScale n) paperEGCZeroOffset,
      continuous_paperEGCCompactifiedCorrection _ _⟩
  | (n, some q) => paperEGCCopyContinuous (paperEGCScale n) paperEGCZeroOffset q

/-- The proven paper theorem supplies one null set for every finite complex span of the family. -/
theorem paperEGCFourier_common_span_convergence :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ θ ∈ Set.Ioc (0 : ℝ) 1, θ ∉ E →
      ∀ S : Finset (ℕ × Option XiZeroCopy), ∀ c : (ℕ × Option XiZeroCopy) → ℂ,
        Tendsto (fun N => fourierPartialSum
          (fun y => ∑ j ∈ S, c j * paperEGCFourierFamily j y) N θ) atTop
          (𝓝 (∑ j ∈ S, c j * paperEGCFourierFamily j θ)) :=
  paperUnitIntervalContinuous_common_span_convergence paperEGCFourierFamily

/-- In particular, all complete profiles and all individual copies converge on one common set. -/
theorem paperEGCFourier_common_convergence :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ θ ∈ Set.Ioc (0 : ℝ) 1, θ ∉ E → ∀ j : ℕ × Option XiZeroCopy,
        Tendsto (fun N => fourierPartialSum (paperEGCFourierFamily j) N θ) atTop
          (𝓝 (paperEGCFourierFamily j θ)) := by
  obtain ⟨E, hm, hz, hc⟩ := paperEGCFourier_common_span_convergence
  refine ⟨E, hm, hz, fun θ hθ he j => ?_⟩
  simpa using hc θ hθ he {j} (fun _ => 1)

/-- The complete correction coefficient is the sum over all native multiplicity-copy coefficients. -/
theorem paperEGCFourier_coefficient_allCopies (eps x : PaperEGCSmallParameter) (k : ℤ) :
    l2Pair (fourierChar k) (paperEGCCompactifiedCorrection eps x) =
      ∑' q : XiZeroCopy, l2Pair (fourierChar k) (paperEGCCopyContinuous eps x q) := by
  exact paperSummableFourierCopies_coefficient (paperEGCCopyContinuous eps x)
    (fun q => 8 / ‖xiSpectralPoint q‖^2)
    (by simpa only [mul_one_div] using xiSpectralPoint_inv_sq_summable.mul_left 8)
    (fun q θ => norm_paperEGCCircleCopy_le eps x θ q) k

/-- Every finite Fourier cutoff preserves the complete copy sum exactly. -/
theorem paperEGCFourier_partialSum_allCopies (eps x : PaperEGCSmallParameter) (N : ℕ) (θ : ℝ) :
    fourierPartialSum (paperEGCCompactifiedCorrection eps x) N θ =
      ∑' q : XiZeroCopy, fourierPartialSum (paperEGCCopyContinuous eps x q) N θ := by
  exact paperSummableFourierCopies_partialSum (paperEGCCopyContinuous eps x)
    (fun q => 8 / ‖xiSpectralPoint q‖^2)
    (by simpa only [mul_one_div] using xiSpectralPoint_inv_sq_summable.mul_left 8)
    (fun q y => norm_paperEGCCircleCopy_le eps x y q) N θ

end
end RHTower
