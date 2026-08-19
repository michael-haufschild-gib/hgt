import GaloisForLFunctions.HTGeometry.DigammaScaleShiftGauss

/-!
# The archimedean logarithmic derivative as a unit-scale digamma sum

Gauss multiplication turns the logarithmic derivative of a commensurable-scale Gamma product into a
plain sum of unit-scale shifted digammas plus a constant.  That is what places it inside a shifted
digamma jet field, where the boundary datum needs nothing beyond pairwise incongruence of the
shifts.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The scaled logarithmic derivative is a unit-scale digamma sum plus a constant.** -/
theorem sum_scaleShift_digamma_eq {d : ℕ} (n : Fin d → ℕ) (hn : ∀ j, 0 < n j) (μ : Fin d → ℂ)
    {w : ℂ} (hw : ∀ (j : Fin d) (m : ℕ), (n j : ℂ) * w + μ j ≠ -(m : ℂ)) :
    ∑ j : Fin d, (n j : ℂ) * Complex.digamma ((n j : ℂ) * w + μ j)
      = (∑ j : Fin d, ∑ k ∈ Finset.range (n j),
          Complex.digamma (w + (μ j + (k : ℂ)) / (n j : ℂ)))
        + ∑ j : Fin d, (n j : ℂ) * Complex.log (n j : ℂ) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => digamma_scale_shift_eq_sum (hn j) (hw j)

end

end GaloisForLFunctions.HTGeometry
