import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Main

/-!
# Almost everywhere convergence of Fourier series in `L log L`: paper statement

Restates the main theorem of the `FourierLLogL` development using only Mathlib vocabulary: for a
function `f` on the circle `ℝ/2πℤ` that is a.e. strongly measurable for normalized Haar measure and
satisfies `∫ |f| log(2 + |f|) < ∞`, the symmetric partial sums
`∑_{k=-N}^{N} f̂(k) e^{ikx}` converge to `f(x)` for every `x` outside a measurable Haar-null set.

## Main results

- `paperMain`: almost everywhere convergence of symmetric Fourier partial sums for `L log L`
  functions on the circle.

## Hypotheses

The statement takes only a.e. strong measurability of `f` and integrability of
`|f| log(2 + |f|)` with respect to normalized Haar measure; no further premise appears.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace GaloisForLFunctions.HTGeometry.FourierLLogL

/-- For measurable `f` on `ℝ/2πℤ` with `|f| log(2 + |f|)` integrable, the symmetric Fourier
partial sums `∑_{|k| ≤ N} f̂(k) e^{ikx}` converge to `f(x)` off a measurable Haar-null set. -/
theorem paperMain (f : AddCircle (2 * Real.pi) → ℂ)
    (hfm : AEStronglyMeasurable f AddCircle.haarAddCircle)
    (hfi : Integrable (fun x ↦ ‖f x‖ * Real.log (2 + ‖f x‖))
      AddCircle.haarAddCircle) :
    ∃ E : Set (AddCircle (2 * Real.pi)),
      MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧ ∀ x ∉ E,
        Tendsto
          (fun N : ℕ ↦
            ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f k * fourier k x)
          atTop (𝓝 (f x)) := by
  simpa only [circleMeasure, symmetricPartialSum] using
    (almost_everywhere_fourier_convergence f ⟨hfm, hfi⟩)

end GaloisForLFunctions.HTGeometry.FourierLLogL
