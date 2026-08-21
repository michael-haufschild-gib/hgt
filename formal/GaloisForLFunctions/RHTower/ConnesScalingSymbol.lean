import GaloisForLFunctions.RHTower.ConnesSymbolChart
import Mathlib.MeasureTheory.Group.Integral

/-!
# The symbol of the scaling operator

§V (25)-(28) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The Schwartz kernel of `U(h)` is `k(x,y) = ∫ h(λ^{-1}) δ(y - λx) d^*λ`, so its symbol is

  `σ(x,ξ) = ∫ h(λ^{-1}) α((λ-1)xξ) d^*λ`   (25)-(26).

Because the multiplicative Haar measure is `ρ^{-1} dλ/|λ|`, translating `λ ↦ λ+1` — a symmetry of
the *additive* Haar measure — turns this into `ρ^{-1} ∫ g(λ) α(λ x ξ) dλ` with
`g(λ) = h((λ+1)^{-1})|λ+1|^{-1}` (28), i.e. `σ(x,ξ) = ρ^{-1} ĝ(xξ)` (27).  The whole step is the
translation invariance of Lebesgue measure; no property of the character is used.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **§V (25)-(27).**  The symbol of the scaling operator is the Fourier transform of the chart
function `g(λ) = h((λ+1)^{-1})|λ+1|^{-1}`, by translation invariance of the additive Haar
measure. -/
theorem connes_symbol_translate (h : ℝ → ℂ) (e : ℝ → ℂ) (t : ℝ) :
    (∫ lam : ℝ, h lam⁻¹ * ((|lam| : ℝ) : ℂ)⁻¹ * e ((lam - 1) * t))
      = ∫ lam : ℝ, ((connesSymbolChart h lam : ℂ)) * e (lam * t) := by
  have hshift := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun lam : ℝ => h lam⁻¹ * ((|lam| : ℝ) : ℂ)⁻¹ * e ((lam - 1) * t)) 1
  rw [← hshift]
  refine integral_congr_ae (Filter.Eventually.of_forall fun lam => ?_)
  simp only [connesSymbolChart, add_sub_cancel_right]

end

end GaloisForLFunctions.RHTower
