import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Sobolev admission on the real line supplies an actual continuous representative. -/
open MeasureTheory Set Filter Topology TemperedDistribution FourierTransform
open scoped SchwartzMap ContDiff
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem real_density_ae_eq {f g : ℝ → ℂ}
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (h : ∀ ψ : 𝓢(ℝ,ℂ), (∫ x : ℝ, ψ x • f x) = ∫ x : ℝ, ψ x • g x) : f =ᵐ[volume] g := by
  apply ae_eq_of_integral_contDiff_smul_eq hf hg
  intro u hu hsupp
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ u) := hsupp.comp_left rfl
  have hd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ u) := Complex.ofRealCLM.contDiff.comp hu
  have hp := h (hc.toSchwartzMap hd)
  have he (x : ℝ) : (hc.toSchwartzMap hd) x = (u x : ℂ) := rfl
  simp only [he] at hp
  simpa [Complex.real_smul] using hp

private theorem real_fourierInv_duality {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x : ℝ, (𝓕⁻ f) x • g x) = ∫ x : ℝ, f x • (𝓕⁻ g) x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (L := -(innerₗ ℝ)) Real.continuous_fourierChar continuous_inner.neg hf hg
  have he : (-(innerₗ ℝ)).flip = -(innerₗ ℝ) := by
    ext; rfl
  rw [he] at h
  exact h

/-- Sobolev order above one half yields a continuous representative of the original L² class. -/
theorem real_sobolev_continuous_representative (u : Lp ℂ 2 (volume : Measure ℝ))
    (s : ℝ) (hs : 1 < 2*s) (hu : MemSobolev s 2 (u : 𝓢'(ℝ,ℂ))) :
    ∃ f : ℝ → ℂ, Continuous f ∧ f =ᵐ[volume] u := by
  obtain ⟨v,hv⟩ := hu.fourier_memL1 (by simpa using hs)
  let f : ℝ → ℂ := 𝓕⁻ (v : ℝ → ℂ)
  have hc : Continuous f := by
    have he : f = fun x : ℝ => Real.Lp.fourierTransform v (-x) := by
      funext x
      exact Real.fourierInv_eq_fourier_neg _ x
    rw [he]
    exact (Real.Lp.fourierTransform v).continuous.comp continuous_neg
  refine ⟨f,hc,?_⟩
  apply real_density_ae_eq hc.locallyIntegrable ((Lp.memLp u).locallyIntegrable (by norm_num))
  intro ψ
  have hu' : (u : 𝓢'(ℝ,ℂ)) = 𝓕⁻ (v : 𝓢'(ℝ,ℂ)) := by
    rw [← hv,FourierTransform.fourierInv_fourier_eq]
  have hp := congrArg (fun T : 𝓢'(ℝ,ℂ) => T ψ) hu'
  simp only [TemperedDistribution.fourierInv_apply,Lp.toTemperedDistribution_apply] at hp
  rw [hp]
  simpa only [f,SchwartzMap.fourierInv_coe] using
    (real_fourierInv_duality ψ.integrable (L1.integrable_coeFn v)).symm

end
end GaloisForLFunctions.HTGeometry
