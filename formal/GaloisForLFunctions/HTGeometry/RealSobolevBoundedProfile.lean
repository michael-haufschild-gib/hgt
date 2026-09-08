import GaloisForLFunctions.HTGeometry.RealSobolevContinuousRepresentative
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The actual continuous representative of a Sobolev class has a global spatial bound. -/
open MeasureTheory Set Filter Topology TemperedDistribution FourierTransform
open scoped SchwartzMap ContDiff
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

/-- Sobolev admission bounds any continuous representative of the original L² class. -/
theorem continuous_sobolev_bounded (u : Lp ℂ 2 (volume : Measure ℝ))
    (s : ℝ) (hs : 1 < 2*s) (hu : MemSobolev s 2 (u : 𝓢'(ℝ,ℂ)))
    (f : ℝ → ℂ) (hf : Continuous f) (ha : f =ᵐ[volume] u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖f x‖ ≤ C := by
  obtain ⟨v,hv⟩ := hu.fourier_memL1 (by simpa using hs)
  let g : ℝ → ℂ := 𝓕⁻ (v : ℝ → ℂ)
  have he : g = fun x : ℝ => Real.Lp.fourierTransform v (-x) := by
    funext x
    exact Real.fourierInv_eq_fourier_neg _ x
  have hg : Continuous g := by rw [he]; exact (Real.Lp.fourierTransform v).continuous.comp continuous_neg
  have hfg : f =ᵐ[volume] g := by
    apply ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable hg.locallyIntegrable
    intro k hk hc
    let ψ := (hc.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hk)
    have ht : (u : 𝓢'(ℝ,ℂ)) = 𝓕⁻ (v : 𝓢'(ℝ,ℂ)) := by
      rw [← hv,FourierTransform.fourierInv_fourier_eq]
    have hp := congrArg (fun T : 𝓢'(ℝ,ℂ) => T ψ) ht
    simp only [TemperedDistribution.fourierInv_apply,Lp.toTemperedDistribution_apply] at hp
    have hi : (∫ x : ℝ, ψ x • f x) = ∫ x : ℝ, ψ x • u x := by
      apply integral_congr_ae
      filter_upwards [ha] with x hx
      rw [hx]
    have hd := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (e := Real.fourierChar) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (L := -(innerₗ ℝ)) Real.continuous_fourierChar continuous_inner.neg ψ.integrable (L1.integrable_coeFn v)
    have hflip : (-(innerₗ ℝ)).flip = -(innerₗ ℝ) := by ext; rfl
    rw [hflip] at hd
    have hd' : (∫ x : ℝ, (𝓕⁻ (ψ : ℝ → ℂ)) x • v x) = ∫ x : ℝ, ψ x • g x := hd
    have hψ : (∫ x : ℝ, ψ x • f x) = ∫ x : ℝ, ψ x • g x := by
      rw [hi,hp]
      simpa only [SchwartzMap.fourierInv_coe] using hd'
    change (∫ x : ℝ, (k x:ℂ) • f x) = ∫ x : ℝ, (k x:ℂ) • g x at hψ
    simpa only [Complex.real_smul,smul_eq_mul] using hψ
  have hpoint := Measure.eq_of_ae_eq hfg hf hg
  refine ⟨‖Real.Lp.fourierTransform v‖,norm_nonneg _,fun x => ?_⟩
  rw [hpoint,he]
  exact (Real.Lp.fourierTransform v).norm_coe_le_norm (-x)

end
end GaloisForLFunctions.HTGeometry
