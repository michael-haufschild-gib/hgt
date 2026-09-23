import GaloisForLFunctions.HTGeometry.KleinGordonFreeSolution

/-!
# The multiplier as an inverse Fourier integral

The free evolution was built with the multiplier calculus, where the Klein–Gordon equation is an
identity of Schwartz functions. To read that identity pointwise — as a statement about `u(t, x)` — the
multiplier has to be written as an inverse Fourier transform of a product, and that is what this file
does.

`fourierInv_coe` turns the Schwartz-level inverse transform into the function-level one, which is an
integral; `smulLeftCLM_apply_apply` evaluates the product. The result is the bridge between the
operator identities of the previous files and the parametric integrals of the synthesis file.
-/

namespace GaloisForLFunctions.HTGeometry

open SchwartzMap Function FourierTransform

open scoped SchwartzMap Laplacian

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace F]

omit [CompleteSpace F] in
/-- **A Fourier multiplier is the inverse transform of the product of symbol and transform.** -/
theorem coe_fourierMultiplierCLM {g : E → ℂ} (hg : Function.HasTemperateGrowth g)
    (f : 𝓢(E, F)) :
    (fourierMultiplierCLM F g f : E → F) = 𝓕⁻ fun ξ : E => g ξ • (𝓕 f) ξ := by
  rw [fourierMultiplierCLM_apply, fourierInv_coe]
  congr 1
  funext ξ
  exact smulLeftCLM_apply_apply hg (𝓕 f) ξ

omit [CompleteSpace F] in
/-- The free evolution, as an inverse Fourier integral. -/
theorem coe_kgFree (f : 𝓢(E, F)) (t : ℝ) :
    (kgFree f t : E → F) = 𝓕⁻ fun ξ : E => kgCosSymbol t ξ • (𝓕 f) ξ :=
  coe_fourierMultiplierCLM (hasTemperateGrowth_kgCosSymbol t) f

omit [CompleteSpace F] in
/-- The velocity evolution, as an inverse Fourier integral. -/
theorem coe_kgFreeVel (f : 𝓢(E, F)) (t : ℝ) :
    (kgFreeVel f t : E → F) = 𝓕⁻ fun ξ : E => kgSinSymbol t ξ • (𝓕 f) ξ :=
  coe_fourierMultiplierCLM (hasTemperateGrowth_kgSinSymbol t) f

/-- **The Klein–Gordon operator applied to the free evolution, as an inverse Fourier integral.** -/
theorem coe_kgOperator_kgFree (f : 𝓢(E, F)) (t : ℝ) :
    ((kgFree f t - (((2 * Real.pi) ^ (2 : ℕ))⁻¹ : ℝ) • Δ (kgFree f t) : 𝓢(E, F)) : E → F)
      = 𝓕⁻ fun ξ : E => (((kgFreq ξ ^ (2 : ℕ) : ℝ) : ℂ) * kgCosSymbol t ξ) • (𝓕 f) ξ := by
  rw [kgOperator_kgFree]
  refine coe_fourierMultiplierCLM ?_ f
  have hfreq : Function.HasTemperateGrowth fun ξ : E => ((kgFreq ξ ^ (2 : ℕ) : ℝ) : ℂ) :=
    Complex.hasTemperateGrowth_ofReal.comp ((hasTemperateGrowth_kgFreq E).pow 2)
  exact hfreq.mul (hasTemperateGrowth_kgCosSymbol t)

end GaloisForLFunctions.HTGeometry
