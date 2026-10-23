import GaloisForLFunctions.TransThresholdPairCorrelation.SmoothGridWeightKernel
import GaloisForLFunctions.TransThresholdPairCorrelation.PrimeSurplusAnatomyAndDirichletMeanValue
import GaloisForLFunctions.TransThresholdPairCorrelation.HeightAveragedCoalescentLocalization

/-!
# The Smooth-Window Continuous Form and the Exact Coalescent Kernel

For a weight `Ω` (compactly supported, continuous) put
`𝓜_Ω[u, v] = ∬ Ω(τ) Φ(τ − τ')² u(τ) v(τ') dτ dτ'`. Because the `τ'`-integral runs over all of `ℝ`
and `∫ Φ(x)² e^{ixy} dx = 2π g(y)`, the convolution `Φ² ⋆ P_X` is again a prime polynomial,
`(Φ² ⋆ P_X)(τ) = −2 Σ_m a_m g(log m) cos(τ log m)` (`integral_PhiSq_shift_mul_PX`), and

`𝓜_Ω[u, P_X] = −2 Σ_m a_m g(log m) ∫ Ω(τ) u(τ) cos(τ log m) dτ`   (`smoothForm_PX_right_eq`).

For `u = P_X` this is an exact pair sum with the **coalescent kernel**
`(1/π) a_n a_m g(log m) [Ω̂(log n − log m) + Ω̂(log n + log m)]`, `Ω̂(θ) = ∫ Ω(τ) cos(τθ) dτ`
(`smoothForm_PX_PX_eq`): no half-line moments, no window end effects. The diagonal is
`π⁻¹ (∫Ω) Σ a_n² g(log n)` plus a sum-frequency term, and pairs with `|log(n/m)| > θ₀` carry
`Ω̂(θ) ≤ ‖Ω^{(k)}‖₁ / θ^k`.
-/

open MeasureTheory Real Set Finset Filter
open scoped BigOperators ArithmeticFunction
open Zeta23 Zeta23.PrimeSide RHTower

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

variable {Φ : ℝ → ℝ}

/-- The smooth-window continuous form `𝓜_Ω[u, v] = ∬ Ω(τ) Φ(τ − τ')² u(τ) v(τ')`. -/
def smoothForm (Φ Ω u v : ℝ → ℝ) : ℝ :=
  ∫ q : ℝ × ℝ, Ω q.1 * Φ (q.1 - q.2) ^ 2 * u q.1 * v q.2

/-- The cosine transform `Ω̂(θ) = ∫ Ω(τ) cos(τθ) dτ` of the window. -/
def cosTransform (Ω : ℝ → ℝ) (θ : ℝ) : ℝ := ∫ τ, Ω τ * Real.cos (τ * θ)

end GaloisForLFunctions.TransThresholdPairCorrelation
