import GaloisForLFunctions.RHTower.ConnesSymbolPairing
import GaloisForLFunctions.RHTower.ConnesSymbolChart

/-!
# §V (25)–(27): the symbol of the scaling kernel is the transform of Connes' chart

§V (25)-(27) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The kernel (19) of `U(h)` is `k(x,y) = ∫ h(λ^{-1}) δ(y − λx) d^*λ`, and its symbol (25) is
`σ(x,ξ) = ∫ h(λ^{-1})(∫ δ(x+u−λx)α(uξ)du) d^*λ`.  The inner integral is `α((λ−1)xξ)` by (26) —
the graph `δ`-section of Appendix III, already Lean-owned as `ConnesGraphDelta`.  What remains is
(27): writing `d^*λ = ρ^{-1}dλ/|λ|` and substituting `μ = λ − 1` turns the result into

  `σ(x,ξ) = ρ^{-1} ∫ g(μ) α(μ x ξ) dμ = ρ^{-1} ĝ(xξ)`,   `g(μ) = h((μ+1)^{-1})|μ+1|^{-1}`,

with `g` Connes' chart (28), already Lean-owned as `ConnesSymbolChart.connesSymbolChart`.

The substitution is proved here for an arbitrary character-like weight, and then specialised to
the additive character, identifying the result with the inverse Fourier transform of the chart.
-/

open MeasureTheory Real
open scoped FourierTransform

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **§V (27), the substitution.**  The change of variable `μ = λ − 1` turns the scaling integral
into the chart integral, for an arbitrary weight. -/
theorem connes_symbol_scaling_substitution (h : ℝ → ℂ) (w : ℝ → ℂ) (t : ℝ) :
    (∫ lam : ℝ, h lam⁻¹ * w ((lam - 1) * t) * ((|lam| : ℝ) : ℂ)⁻¹)
      = ∫ mu : ℝ, connesSymbolChart h mu * w (mu * t) := by
  have hshift := MeasureTheory.integral_add_right_eq_self
    (μ := (volume : Measure ℝ))
    (fun lam : ℝ => h lam⁻¹ * w ((lam - 1) * t) * ((|lam| : ℝ) : ℂ)⁻¹) 1
  rw [← hshift]
  refine integral_congr_ae (Filter.Eventually.of_forall fun mu => ?_)
  show h (mu + 1)⁻¹ * w ((mu + 1 - 1) * t) * ((|mu + 1| : ℝ) : ℂ)⁻¹
    = connesSymbolChart h mu * w (mu * t)
  rw [connesSymbolChart, show mu + 1 - 1 = mu from by ring]
  ring

/-- **§V (27).**  With the additive character the symbol integral is the inverse Fourier transform
of Connes' chart. -/
theorem connes_symbol_scaling_eq_fourierInv (h : ℝ → ℂ) (t : ℝ) :
    (∫ lam : ℝ, h lam⁻¹ * ((Real.fourierChar ((lam - 1) * t) : Circle) : ℂ)
        * ((|lam| : ℝ) : ℂ)⁻¹)
      = 𝓕⁻ (connesSymbolChart h) t := by
  rw [connes_symbol_scaling_substitution h
    (fun u : ℝ => ((Real.fourierChar u : Circle) : ℂ)) t]
  rw [Real.fourierInv_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun mu => ?_)
  have hinner : (inner ℝ mu t : ℝ) = mu * t := by
    simp
    ring
  show connesSymbolChart h mu * ((Real.fourierChar (mu * t) : Circle) : ℂ)
    = ((Real.fourierChar (inner ℝ mu t : ℝ) : Circle)) • connesSymbolChart h mu
  rw [hinner, Circle.smul_def, smul_eq_mul, mul_comm]

end

end GaloisForLFunctions.RHTower
