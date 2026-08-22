import GaloisForLFunctions.RHTower.ConnesProductFibreDecay
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# §V (20)–(24): the kernel pairing is the symbol pairing

§V (20)-(24) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

`ConnesKernelTracePairing` closed (23), `Trace(R_Λ T) = ∫∫ k(x,y) r_Λ^t(x,y) dx dy`, and
`ConnesSymbolChangeOfVariables`/`ConnesLocalTraceCore` closed the analytic chain from (29) onwards.
The step between them is (24), which Connes justifies with the words *"using the Parseval
formula"*: with `r_Λ^t(x,y) = ρ_Λ(x)ρ̂_Λ(x−y)` of (21) and the symbol `σ` of (20), the kernel
pairing becomes the symbol pairing against `σ_Λ(x,ξ) = ρ_Λ(x)ρ_Λ(ξ)` of (22).

Two moves are involved and both are proved here: the substitution `y = x + u` that puts the kernel
in the diagonal form `(20)` uses, and the multiplication formula `∫ 𝓕f·g = ∫ f·𝓕g` applied in the
second variable.  The cutoff `ρ_Λ` is even, so the reflection `ρ̂_Λ(x−y)` costs nothing.
-/

open MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **§V (20).**  The symbol of a kernel: its partial Fourier transform along the diagonal. -/
def connesKernelSymbol (k : ℝ → ℝ → ℂ) (x ξ : ℝ) : ℂ := 𝓕 (fun u : ℝ => k x (x + u)) ξ

/-- The Fourier transform of an even function is even. -/
theorem connes_fourier_even {f : ℝ → ℂ} (hf : ∀ t : ℝ, f (-t) = f t) (ξ : ℝ) :
    𝓕 f (-ξ) = 𝓕 f ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  have hcomp := MeasureTheory.integral_neg_eq_self
    (fun v : ℝ => Complex.exp ((↑(-2 * π * v * ξ) : ℂ) * Complex.I) • f v)
    (volume : Measure ℝ)
  rw [← hcomp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show Complex.exp ((↑(-2 * π * v * -ξ) : ℂ) * Complex.I) • f v
    = Complex.exp ((↑(-2 * π * -v * ξ) : ℂ) * Complex.I) • f (-v)
  rw [hf v]
  congr 2
  push_cast
  ring

/-- The kernel pairing in diagonal form. -/
theorem connes_kernel_pairing_diagonal (k : ℝ → ℝ → ℂ) {ρ : ℝ → ℂ}
    (hρ : ∀ t : ℝ, ρ (-t) = ρ t) (x : ℝ) :
    (∫ y : ℝ, k x y * 𝓕 ρ (x - y)) = ∫ u : ℝ, k x (x + u) * 𝓕 ρ u := by
  have hshift := MeasureTheory.integral_add_right_eq_self
    (μ := (volume : Measure ℝ)) (fun y : ℝ => k x y * 𝓕 ρ (x - y)) x
  rw [← hshift]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show k x (u + x) * 𝓕 ρ (x - (u + x)) = k x (x + u) * 𝓕 ρ u
  have h1 : x - (u + x) = -u := by ring
  rw [h1, connes_fourier_even hρ u, add_comm u x]

/-- **§V (24), the Parseval step.**  The kernel pairing against `ρ̂_Λ` is the symbol pairing
against `ρ_Λ`. -/
theorem connes_symbol_pairing (k : ℝ → ℝ → ℂ) {ρ : ℝ → ℂ}
    (hρeven : ∀ t : ℝ, ρ (-t) = ρ t) (hρ : Integrable ρ) (x : ℝ)
    (hk : Integrable fun u : ℝ => k x (x + u)) :
    (∫ y : ℝ, k x y * 𝓕 ρ (x - y)) = ∫ ξ : ℝ, connesKernelSymbol k x ξ * ρ ξ := by
  rw [connes_kernel_pairing_diagonal k hρeven x]
  have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (L := (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ)) (f := fun u : ℝ => k x (x + u)) (g := ρ)
    Real.continuous_fourierChar ((innerSL ℝ (E := ℝ)).continuous₂) hk hρ
  have hflipeq : ((innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip) = (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) := by
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    simp only [LinearMap.flip_apply]
    exact real_inner_comm a b
  rw [hflipeq] at hflip
  simp only [smul_eq_mul] at hflip
  simp only [connesKernelSymbol]
  exact hflip.symm

/-- **§V (24).**  Integrating the Parseval step over `x` against the infrared cutoff. -/
theorem connes_symbol_pairing_integrated (k : ℝ → ℝ → ℂ) {ρ : ℝ → ℂ}
    (hρeven : ∀ t : ℝ, ρ (-t) = ρ t) (hρ : Integrable ρ)
    (hk : ∀ x : ℝ, Integrable fun u : ℝ => k x (x + u)) :
    (∫ x : ℝ, ρ x * ∫ y : ℝ, k x y * 𝓕 ρ (x - y))
      = ∫ x : ℝ, ρ x * ∫ ξ : ℝ, connesKernelSymbol k x ξ * ρ ξ := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ρ x * (∫ y : ℝ, k x y * 𝓕 ρ (x - y))
    = ρ x * ∫ ξ : ℝ, connesKernelSymbol k x ξ * ρ ξ
  rw [connes_symbol_pairing k hρeven hρ x (hk x)]

end

end GaloisForLFunctions.RHTower
