import GaloisForLFunctions.RHTower.ConnesScalingKernelDelta

/-!
# §V (19): the scaling operator and its kernel

§V (19) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

`ConnesScalingKernelDelta` built the kernel of (19) as a Dirac-measure superposition and computed
its symbol.  What is added here is the operator itself — the superposition
`U(h) = ∫ h(λ^{-1}) U(λ) dλ/|λ|` of the scaling action `U(λ)ζ(x) = ζ(λx)` — together with the
identification that makes (19) a statement *about `U(h)`*: the value of the operator at `x` is
exactly the kernel paired with the input function.

With that, the whole of `§V (19)–(27)` is a statement about the operator: the symbol of `U(h)`,
computed by testing against the character of (20), is `ρ^{-1}ĝ(xξ)` with `g` Connes' chart (28).
-/

open MeasureTheory Real
open scoped FourierTransform

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The scaling action `U(λ)ζ(x) = ζ(λx)`. -/
def connesScalingAction (lam : ℝ) (ζ : ℝ → ℂ) (x : ℝ) : ℂ := ζ (lam * x)

/-- **§V (19), the operator.**  `U(h)` as a superposition of scalings against multiplicative
Haar measure. -/
def connesScalingOperator (h : ℝ → ℂ) (ζ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ lam : ℝ, h lam⁻¹ * connesScalingAction lam ζ x * ((|lam| : ℝ) : ℂ)⁻¹

/-- The scaling action is a representation of the multiplicative group. -/
theorem connesScalingAction_comp (a b : ℝ) (ζ : ℝ → ℂ) :
    connesScalingAction a (connesScalingAction b ζ) = connesScalingAction (a * b) ζ := by
  funext x
  show ζ (b * (a * x)) = ζ (a * b * x)
  congr 1
  ring

theorem connesScalingAction_one (ζ : ℝ → ℂ) : connesScalingAction 1 ζ = ζ := by
  funext x
  show ζ (1 * x) = ζ x
  rw [one_mul]

/-- **§V (19), the operator/kernel identification.**  The value of `U(h)` at `x` is the kernel of
(19) paired with the input function. -/
theorem connesScalingOperator_eq_kernelPairing (h ζ : ℝ → ℂ) (x : ℝ) :
    connesScalingOperator h ζ x = connesScalingKernelPairing h x ζ := by
  rw [connesScalingKernelPairing_eq]
  rfl

/-- **§V (19)–(27), at the level of the operator.**  The symbol of `U(h)`, obtained by testing
against the character of (20), is the inverse transform of Connes' chart. -/
theorem connes_scalingOperator_symbol (h : ℝ → ℂ) (x ξ : ℝ) :
    connesScalingOperator h
        (fun y : ℝ => ((Real.fourierChar ((y - x) * ξ) : Circle) : ℂ)) x
      = 𝓕⁻ (connesSymbolChart h) (x * ξ) := by
  rw [connesScalingOperator_eq_kernelPairing,
    connes_scalingKernel_symbol_eq_fourierInv]

/-- The operator is additive in the input function, whenever the two pieces are integrable. -/
theorem connesScalingOperator_add (h : ℝ → ℂ) (ζ η : ℝ → ℂ) (x : ℝ)
    (hζ : Integrable fun lam : ℝ => h lam⁻¹ * ζ (lam * x) * ((|lam| : ℝ) : ℂ)⁻¹)
    (hη : Integrable fun lam : ℝ => h lam⁻¹ * η (lam * x) * ((|lam| : ℝ) : ℂ)⁻¹) :
    connesScalingOperator h (fun y => ζ y + η y) x
      = connesScalingOperator h ζ x + connesScalingOperator h η x := by
  show (∫ lam : ℝ, h lam⁻¹ * (ζ (lam * x) + η (lam * x)) * ((|lam| : ℝ) : ℂ)⁻¹)
    = (∫ lam : ℝ, h lam⁻¹ * ζ (lam * x) * ((|lam| : ℝ) : ℂ)⁻¹)
      + ∫ lam : ℝ, h lam⁻¹ * η (lam * x) * ((|lam| : ℝ) : ℂ)⁻¹
  rw [← MeasureTheory.integral_add hζ hη]
  refine integral_congr_ae (Filter.Eventually.of_forall fun lam => ?_)
  ring

end

end GaloisForLFunctions.RHTower
