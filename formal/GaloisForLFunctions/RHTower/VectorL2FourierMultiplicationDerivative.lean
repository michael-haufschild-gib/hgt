import GaloisForLFunctions.RHTower.VectorL2WeakDerivativeFourier

/-!
# Multiplication by the variable becomes a weak derivative after the Fourier transform

If an `L²` function stays in `L²` after multiplication by the variable, then the Fourier transform
of the original has an `L²` weak derivative: the distributional identity
`∂(𝓕 f) = 𝓕(-2πi · (t f))` turns the multiplication hypothesis directly into a Sobolev conclusion.

This is the transfer a local `H¹` statement needs: a tail remainder with `t·r(t) ∈ L²` has a
transform in `H¹`, with no pointwise differentiability and no `L¹` hypothesis anywhere.
-/

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap LineDeriv

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The tempered distribution of `t ↦ t • f t` is the variable-multiplication of the distribution
of `f`. -/
theorem l2_smulLeft_toTemperedDistribution
    (f g : Lp H 2 (volume : Measure ℝ))
    (hg : (g : ℝ → H) =ᵐ[volume] fun t : ℝ => (t : ℂ) • (f : ℝ → H) t) :
    (g : 𝓢'(ℝ, H))
      = TemperedDistribution.smulLeftCLM H (fun ξ : ℝ => inner ℝ ξ (1 : ℝ)) (f : 𝓢'(ℝ, H)) := by
  ext ψ
  rw [MeasureTheory.Lp.toTemperedDistribution_apply,
    TemperedDistribution.smulLeftCLM_apply_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hg] with x hx
  rw [hx]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (by fun_prop : Function.HasTemperateGrowth (fun ξ : ℝ => ((inner ℝ ξ (1 : ℝ) : ℝ) : ℂ)))]
  simp only [smul_eq_mul]
  simp
  module

/-- **The Plancherel transfer.**  If `t ↦ t • f t` agrees a.e. with an `L²` function `g`, then the
Fourier transform of `f` has weak derivative `-(2πi) · 𝓕 g`, an `L²` function. -/
theorem l2_weakDerivative_fourier_of_mul
    (f g : Lp H 2 (volume : Measure ℝ))
    (hg : (g : ℝ → H) =ᵐ[volume] fun t : ℝ => (t : ℂ) • (f : ℝ → H) t) :
    ∂_{(1 : ℝ)} ((𝓕 f : Lp H 2 (volume : Measure ℝ)) : 𝓢'(ℝ, H))
      = (-(2 * Real.pi * Complex.I)) •
          ((𝓕 g : Lp H 2 (volume : Measure ℝ)) : 𝓢'(ℝ, H)) := by
  rw [← MeasureTheory.Lp.fourier_toTemperedDistribution_eq,
    ← MeasureTheory.Lp.fourier_toTemperedDistribution_eq,
    TemperedDistribution.lineDerivOp_fourier_eq,
    ← l2_smulLeft_toTemperedDistribution f g hg]
  exact map_smul _ _ _

end RHTower
