import GaloisForLFunctions.RHTower.VectorL2WeakDerivativeFourier

/-!
# Uniqueness of Hilbert-valued `L²` weak derivatives

Fourier transformation identifies every `L²` distributional derivative with the same exact
multiplier. Unitarity therefore makes the representing `L²` vector unique.
-/

noncomputable section

open MeasureTheory FourierTransform LineDeriv
open scoped ENNReal SchwartzMap LineDeriv

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An `L²` distributional derivative has at most one `L²` representative. -/
theorem l2_weakDerivative_unique (f g h : Lp H 2 (volume : Measure ℝ))
    (hg : ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, H)) = (g : 𝓢'(ℝ, H)))
    (hh : ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, H)) = (h : 𝓢'(ℝ, H))) :
    g = h := by
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  exact Lp.ext ((l2_fourier_weakDerivative_ae f g hg).trans
    (l2_fourier_weakDerivative_ae f h hh).symm)

end RHTower
