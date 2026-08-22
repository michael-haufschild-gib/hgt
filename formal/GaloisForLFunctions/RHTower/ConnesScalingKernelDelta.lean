import GaloisForLFunctions.RHTower.ConnesScalingSymbolChart

/-!
# §V (19), (20), (25), (26): the scaling kernel and its symbol

§V (19)-(26) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The Schwartz kernel of `T = U(h)` is written in (19) as `k(x,y) = ∫ h(λ^{-1})δ(y − λx) d^*λ`, a
*distribution* in `y`.  Here the `δ` is taken literally, as the Dirac measure at `λx`, so the
kernel is paired with a test function by

  `⟨k(x,·), φ⟩ = ∫ h(λ^{-1}) (∫ φ dδ_{λx}) dλ/|λ|`,

and (26) — `∫ δ(x+u−λx)α(uξ)du = α((λ−1)xξ)` — becomes the evaluation `∫ φ dδ_c = φ(c)`, i.e.
`MeasureTheory.integral_dirac`.  Feeding the character `u ↦ α((u−x)ξ)` of (20) then produces the
symbol integral of (25), which `ConnesScalingSymbolChart` identifies with the transform of Connes'
chart.  The chain (19) → (27) is therefore complete.
-/

open MeasureTheory Real
open scoped FourierTransform

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **§V (19).**  The distributional kernel of `U(h)`, paired against a test function in the
second variable.  The `δ` of (19) is the Dirac measure at `λx`. -/
def connesScalingKernelPairing (h : ℝ → ℂ) (x : ℝ) (φ : ℝ → ℂ) : ℂ :=
  ∫ lam : ℝ, h lam⁻¹ * (∫ y : ℝ, φ y ∂(Measure.dirac (lam * x))) * ((|lam| : ℝ) : ℂ)⁻¹

/-- **§V (26).**  The `δ`-evaluation collapses the inner integral. -/
theorem connesScalingKernelPairing_eq (h : ℝ → ℂ) (x : ℝ) (φ : ℝ → ℂ) :
    connesScalingKernelPairing h x φ
      = ∫ lam : ℝ, h lam⁻¹ * φ (lam * x) * ((|lam| : ℝ) : ℂ)⁻¹ := by
  rw [connesScalingKernelPairing]
  refine integral_congr_ae (Filter.Eventually.of_forall fun lam => ?_)
  show h lam⁻¹ * (∫ y : ℝ, φ y ∂(Measure.dirac (lam * x))) * ((|lam| : ℝ) : ℂ)⁻¹
    = h lam⁻¹ * φ (lam * x) * ((|lam| : ℝ) : ℂ)⁻¹
  rw [MeasureTheory.integral_dirac]

/-- **§V (20)+(25)+(26).**  Testing the kernel against the character of (20) gives the symbol
integral of (25). -/
theorem connes_scalingKernel_symbol_integral (h : ℝ → ℂ) (x ξ : ℝ) :
    connesScalingKernelPairing h x
        (fun y : ℝ => ((Real.fourierChar ((y - x) * ξ) : Circle) : ℂ))
      = ∫ lam : ℝ, h lam⁻¹ * ((Real.fourierChar ((lam - 1) * (x * ξ)) : Circle) : ℂ)
          * ((|lam| : ℝ) : ℂ)⁻¹ := by
  rw [connesScalingKernelPairing_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun lam => ?_)
  show h lam⁻¹ * ((Real.fourierChar ((lam * x - x) * ξ) : Circle) : ℂ)
      * ((|lam| : ℝ) : ℂ)⁻¹
    = h lam⁻¹ * ((Real.fourierChar ((lam - 1) * (x * ξ)) : Circle) : ℂ)
      * ((|lam| : ℝ) : ℂ)⁻¹
  rw [show (lam * x - x) * ξ = (lam - 1) * (x * ξ) from by ring]

/-- **§V (19)–(27).**  The symbol of the scaling kernel is the inverse Fourier transform of
Connes' chart, evaluated at `xξ`. -/
theorem connes_scalingKernel_symbol_eq_fourierInv (h : ℝ → ℂ) (x ξ : ℝ) :
    connesScalingKernelPairing h x
        (fun y : ℝ => ((Real.fourierChar ((y - x) * ξ) : Circle) : ℂ))
      = 𝓕⁻ (connesSymbolChart h) (x * ξ) := by
  rw [connes_scalingKernel_symbol_integral h x ξ,
    connes_symbol_scaling_eq_fourierInv h (x * ξ)]

end

end GaloisForLFunctions.RHTower
