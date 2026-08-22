import GaloisForLFunctions.RHTower.ConnesScalingOperator

/-!
# §V (19)–(27) over an arbitrary local field

§V (19)-(27) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068, are stated for a general local field `K`.

`ConnesScalingKernelDelta`, `ConnesScalingSymbolChart` and `ConnesScalingOperator` proved them at
the archimedean place.  Nothing in that argument used anything about `ℝ` beyond three things: the
additive Haar measure is translation invariant, singletons are measurable (so `δ` is a Dirac
measure), and the field is commutative.  This module records the argument in exactly that
generality, so that the `p`-adic places — whose multiplicative Haar shell decomposition the corpus
already owns — are covered by the same theorems.

The absolute value and the additive character enter only as functions; no property of either is
used, which is why the statements are hypothesis-free in them.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {K : Type*} [Field K] [MeasurableSpace K] [MeasurableSingletonClass K]
  [MeasurableAdd K] {μ : Measure K} [μ.IsAddRightInvariant]

/-- **§V (28) over `K`.**  Connes' chart `g(μ) = h((μ+1)^{-1})|μ+1|^{-1}`. -/
def connesLocalChart (nrm : K → ℝ) (h : K → ℂ) (mu : K) : ℂ :=
  h (mu + 1)⁻¹ * ((nrm (mu + 1) : ℝ) : ℂ)⁻¹

/-- **§V (19) over `K`.**  The kernel of `U(h)`, paired against a test function; the `δ` is the
Dirac measure at `λx`. -/
def connesLocalKernelPairing (nrm : K → ℝ) (h : K → ℂ) (μ : Measure K) (x : K) (φ : K → ℂ) : ℂ :=
  ∫ lam : K, h lam⁻¹ * (∫ y : K, φ y ∂(Measure.dirac (lam * x)))
    * ((nrm lam : ℝ) : ℂ)⁻¹ ∂μ

/-- **§V (26) over `K`.**  The `δ`-evaluation. -/
theorem connesLocalKernelPairing_eq (nrm : K → ℝ) (h : K → ℂ) (x : K) (φ : K → ℂ) :
    connesLocalKernelPairing nrm h μ x φ
      = ∫ lam : K, h lam⁻¹ * φ (lam * x) * ((nrm lam : ℝ) : ℂ)⁻¹ ∂μ := by
  rw [connesLocalKernelPairing]
  refine integral_congr_ae (Filter.Eventually.of_forall fun lam => ?_)
  show h lam⁻¹ * (∫ y : K, φ y ∂(Measure.dirac (lam * x))) * ((nrm lam : ℝ) : ℂ)⁻¹
    = h lam⁻¹ * φ (lam * x) * ((nrm lam : ℝ) : ℂ)⁻¹
  rw [MeasureTheory.integral_dirac]

/-- **§V (27) over `K`, the substitution.**  The change of variable `μ = λ − 1` turns the scaling
integral into the chart integral.  Only translation invariance of the additive Haar measure is
used. -/
theorem connes_local_symbol_substitution (nrm : K → ℝ) (h : K → ℂ) (w : K → ℂ) (t : K) :
    (∫ lam : K, h lam⁻¹ * w ((lam - 1) * t) * ((nrm lam : ℝ) : ℂ)⁻¹ ∂μ)
      = ∫ mu : K, connesLocalChart nrm h mu * w (mu * t) ∂μ := by
  have hshift := MeasureTheory.integral_add_right_eq_self (μ := μ)
    (fun lam : K => h lam⁻¹ * w ((lam - 1) * t) * ((nrm lam : ℝ) : ℂ)⁻¹) 1
  rw [← hshift]
  refine integral_congr_ae (Filter.Eventually.of_forall fun mu => ?_)
  show h (mu + 1)⁻¹ * w ((mu + 1 - 1) * t) * ((nrm (mu + 1) : ℝ) : ℂ)⁻¹
    = connesLocalChart nrm h mu * w (mu * t)
  rw [connesLocalChart, show mu + 1 - 1 = mu from by ring]
  ring

/-- **§V (19)–(27) over `K`.**  Testing the kernel against the character of (20) gives the chart
integral of (27). -/
theorem connes_local_kernel_symbol (nrm : K → ℝ) (h : K → ℂ) (w : K → ℂ) (x t : K) :
    connesLocalKernelPairing nrm h μ x (fun y : K => w ((y - x) * t))
      = ∫ mu : K, connesLocalChart nrm h mu * w (mu * (x * t)) ∂μ := by
  rw [connesLocalKernelPairing_eq]
  have hpt : ∀ lam : K,
      h lam⁻¹ * w ((lam * x - x) * t) * ((nrm lam : ℝ) : ℂ)⁻¹
        = h lam⁻¹ * w ((lam - 1) * (x * t)) * ((nrm lam : ℝ) : ℂ)⁻¹ := by
    intro lam
    rw [show (lam * x - x) * t = (lam - 1) * (x * t) from by ring]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact connes_local_symbol_substitution nrm h w (x * t)

/-- **§V (19) over `K`, the operator.** -/
def connesLocalScalingOperator (nrm : K → ℝ) (h : K → ℂ) (μ : Measure K)
    (ζ : K → ℂ) (x : K) : ℂ :=
  ∫ lam : K, h lam⁻¹ * ζ (lam * x) * ((nrm lam : ℝ) : ℂ)⁻¹ ∂μ

/-- **§V (19) over `K`, the operator/kernel identification.** -/
theorem connesLocalScalingOperator_eq_kernelPairing (nrm : K → ℝ) (h ζ : K → ℂ) (x : K) :
    connesLocalScalingOperator nrm h μ ζ x = connesLocalKernelPairing nrm h μ x ζ := by
  rw [connesLocalKernelPairing_eq]
  rfl

/-- **§V (19)–(27) over `K`, at the level of the operator.** -/
theorem connes_local_scalingOperator_symbol (nrm : K → ℝ) (h : K → ℂ) (w : K → ℂ) (x t : K) :
    connesLocalScalingOperator nrm h μ (fun y : K => w ((y - x) * t)) x
      = ∫ mu : K, connesLocalChart nrm h mu * w (mu * (x * t)) ∂μ := by
  rw [connesLocalScalingOperator_eq_kernelPairing, connes_local_kernel_symbol]

end

end GaloisForLFunctions.RHTower
