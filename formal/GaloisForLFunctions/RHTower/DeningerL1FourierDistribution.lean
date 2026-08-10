import GaloisForLFunctions.RHTower.DeningerMobiusFourierCommutator
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The Fourier transform of an integrable density

Pairing the distribution of an integrable function against a Schwartz test function and moving the
transform across is exactly the multiplication formula `∫ (ℱf)·g = ∫ f·(ℱg)`, so the distributional
Fourier transform of an integrable density is computed by the classical Fourier integral — even
though that integral need not itself be integrable.

Two locally integrable densities defining the same distribution agree almost everywhere, so an
identity of distributions between integrable densities is an identity of functions.

* `deningerFourier_mul_formula` : **`∫ (ℱF)·G = ∫ F·(ℱG)`.**
* `deningerL1Distribution_fourier_apply` : **the distributional transform is the classical one.**
* `deningerL1Distribution_ae_eq` : distributions determine locally integrable densities.
-/

namespace RHTower

open MeasureTheory SchwartzMap FourierTransform

noncomputable section

/-- **The multiplication formula** for two integrable functions of the line. -/
theorem deningerFourier_mul_formula {F G : ℝ → ℂ} (hF : Integrable F) (hG : Integrable G) :
    (∫ ξ : ℝ, (𝓕 F) ξ • G ξ) = ∫ x : ℝ, F x • (𝓕 G) x := by
  have hcont : Continuous fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2 :=
    (innerSL ℝ (E := ℝ)).continuous₂
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (L := innerₗ ℝ) Real.continuous_fourierChar hcont hF hG
  rwa [flip_innerₗ] at h

/-- **The distributional Fourier transform of an integrable density is the classical one.** -/
theorem deningerL1Distribution_fourier_apply {F : ℝ → ℂ} (hF : Integrable F) (g : 𝓢(ℝ, ℂ)) :
    (𝓕 (deningerL1Distribution hF)) g = ∫ ξ : ℝ, g ξ • (𝓕 F) ξ := by
  have hstep : (𝓕 (deningerL1Distribution hF)) g = deningerL1Distribution hF (𝓕 g) := rfl
  rw [hstep, deningerL1Distribution_apply]
  have hcoe : ((𝓕 g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = 𝓕 ((g : ℝ → ℂ)) := SchwartzMap.fourier_coe g
  rw [hcoe]
  exact deningerFourier_mul_formula g.integrable hF

/-- The reflection of a Schwartz function is integrable. -/
theorem deningerSchwartzNeg_integrable (g : 𝓢(ℝ, ℂ)) :
    Integrable fun x : ℝ => (g : ℝ → ℂ) (-x) := by
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hme : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).measurableEmbedding
  exact (hmp.integrable_comp hme).mpr g.integrable

/-- **The distributional inverse transform of an integrable density is the classical one.** -/
theorem deningerL1Distribution_fourierInv_apply {G : ℝ → ℂ} (hG : Integrable G) (g : 𝓢(ℝ, ℂ)) :
    (𝓕⁻ (deningerL1Distribution hG)) g = ∫ ξ : ℝ, g ξ • (𝓕⁻ G) ξ := by
  have hstep : (𝓕⁻ (deningerL1Distribution hG)) g = deningerL1Distribution hG (𝓕⁻ g) := rfl
  rw [hstep, deningerL1Distribution_apply]
  have hcoe : ((𝓕⁻ g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = 𝓕⁻ ((g : ℝ → ℂ)) := SchwartzMap.fourierInv_coe g
  rw [hcoe, Real.fourierInv_eq_fourier_comp_neg ((g : ℝ → ℂ)),
    deningerFourier_mul_formula (deningerSchwartzNeg_integrable g) hG]
  have hrefl : ∀ x : ℝ, (g : ℝ → ℂ) (-x) • (𝓕 G) x
      = (fun y : ℝ => (g : ℝ → ℂ) y • (𝓕⁻ G) y) (-x) := by
    intro x
    rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  calc (∫ x : ℝ, (g : ℝ → ℂ) (-x) • (𝓕 G) x)
      = ∫ x : ℝ, (fun y : ℝ => (g : ℝ → ℂ) y • (𝓕⁻ G) y) (-x) :=
        integral_congr_ae (Filter.Eventually.of_forall hrefl)
    _ = ∫ y : ℝ, (g : ℝ → ℂ) y • (𝓕⁻ G) y :=
        integral_neg_eq_self (fun y : ℝ => (g : ℝ → ℂ) y • (𝓕⁻ G) y) volume

/-- **Pairing against every Schwartz function determines a locally integrable density.** -/
theorem deningerDensity_ae_eq {F G : ℝ → ℂ} (hF : LocallyIntegrable F)
    (hG : LocallyIntegrable G)
    (h : ∀ g : 𝓢(ℝ, ℂ), (∫ x : ℝ, g x • F x) = ∫ x : ℝ, g x • G x) :
    F =ᵐ[volume] G := by
  refine ae_eq_of_integral_contDiff_smul_eq hF hG fun u hu hsupp => ?_
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ u) := hsupp.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ u) := Complex.ofRealCLM.contDiff.comp hu
  have hpair := h (hg₁.toSchwartzMap hg₂)
  have hcoe : ∀ x : ℝ, ((hg₁.toSchwartzMap hg₂ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x = ((u x : ℝ) : ℂ) := fun _ => rfl
  simp only [hcoe, Complex.real_smul] at hpair
  simpa [Complex.real_smul] using hpair

end

end RHTower
