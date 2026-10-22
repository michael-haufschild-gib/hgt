import GaloisForLFunctions.HTGeometry.PolynomialGroupOneBlock
import GaloisForLFunctions.RHTower.Suzuki.SuzukiOnePrimeRoughPrimitiveHardyTail

/-!
# `(21)`: the concrete rank-one one-block estimate

Below the second visible prime the weighted valuation group has two-sided polynomial degree
`κ = 2/3`, the Gamma dimension theorem allows the height `σ = 3/4`, and the slow exponent is
`p = 1/2 + σ = 5/4`.  Three frequency integrations by parts are exactly enough: the far tail test
`κ < σ` and the depth test `κ + 3/2 < N` both hold strictly at `N = 3`, so the block profile is
square integrable on the line `Im z = 3/4`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The concrete rank-one parameters sit strictly inside the two-sided window. -/
theorem onePrimeCarrier_window : (2 / 3 : ℝ) < 3 / 4 ∧ (2 / 3 : ℝ) + 3 / 2 < 3 := by
  norm_num

/-- **`(21)`: the operator-valued polynomial-group one-block estimate at rank one.**  A block
profile assembled from the propagated lower endpoint, the Plancherel boundary term of the third
integration by parts, and the transported third remainder is square integrable on the frequency
line, for the concrete carrier `(κ, σ, N) = (2/3, 3/4, 3)`. -/
theorem lintegral_sq_onePrimeBlockProfile_ne_top
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {Φ : ℝ → ℝ → (X →L[ℂ] X)} {f B r : ℝ → X} {v : X} {K K' X₀ : ℝ}
    (hX₀ : 1 ≤ X₀) (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (htrans : ∀ x t : ℝ, X₀ ≤ t → t ≤ x →
      ‖Φ x t‖ ≤ K * ((t / x) ^ (5 / 4 : ℝ) * (1 + x - t) ^ (2 / 3 : ℝ)))
    (hr : ∀ t : ℝ, X₀ ≤ t → ‖r t‖ ≤ K' * t ^ (-(3 : ℝ)))
    (hrint : ∀ x : ℝ, X₀ ≤ x → IntervalIntegrable (fun t => Φ x t (r t)) volume X₀ x)
    (hB : (∫⁻ x in Ioi (2 * X₀), ‖B x‖ₑ ^ 2) ≠ ⊤)
    (hf : ∀ x : ℝ, 2 * X₀ ≤ x → f x = Φ x X₀ v + B x + ∫ t in X₀..x, Φ x t (r t)) :
    (∫⁻ x in Ioi (2 * X₀), ‖f x‖ₑ ^ 2) ≠ ⊤ := by
  refine lintegral_sq_polynomialTransportProfile_ne_top (κ := 2 / 3) (σ := 3 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hX₀ hK hK' ?_ hr hrint hB hf
  intro x t h1 h2
  have h := htrans x t h1 h2
  rwa [show (1 / 2 + 3 / 4 : ℝ) = 5 / 4 by norm_num]

/-- The same estimate, read through the already-certified tail window: the two exact squared-tail
tests of `(19)`--`(20)` are what the estimate consumes. -/
theorem lintegral_sq_onePrimeBlockProfile_ne_top_of_tails
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {Φ : ℝ → ℝ → (X →L[ℂ] X)} {f B r : ℝ → X} {v : X} {K K' X₀ : ℝ}
    (hX₀ : 1 ≤ X₀) (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (htrans : ∀ x t : ℝ, X₀ ≤ t → t ≤ x →
      ‖Φ x t‖ ≤ K * ((t / x) ^ (5 / 4 : ℝ) * (1 + x - t) ^ (2 / 3 : ℝ)))
    (hr : ∀ t : ℝ, X₀ ≤ t → ‖r t‖ ≤ K' * t ^ (-(3 : ℝ)))
    (hrint : ∀ x : ℝ, X₀ ≤ x → IntervalIntegrable (fun t => Φ x t (r t)) volume X₀ x)
    (hB : (∫⁻ x in Ioi (2 * X₀), ‖B x‖ₑ ^ 2) ≠ ⊤)
    (hf : ∀ x : ℝ, 2 * X₀ ≤ x → f x = Φ x X₀ v + B x + ∫ t in X₀..x, Φ x t (r t)) :
    (IntegrableAtFilter (suzukiPolynomialIBPFarTailNormSq (2 / 3) (3 / 4)) Filter.atTop volume ∧
        IntegrableAtFilter (suzukiPolynomialIBPNearTailNormSq (2 / 3) 3) Filter.atTop volume) ∧
      (∫⁻ x in Ioi (2 * X₀), ‖f x‖ₑ ^ 2) ≠ ⊤ :=
  ⟨suzukiOnePrimeThirdIBPTails,
    lintegral_sq_onePrimeBlockProfile_ne_top hX₀ hK hK' htrans hr hrint hB hf⟩

end GaloisForLFunctions.RHTower
