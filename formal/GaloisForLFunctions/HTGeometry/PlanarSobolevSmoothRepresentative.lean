import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
Every planar L² distribution with all integer Sobolev orders has an actual smooth representative. Polynomial Bessel weights give every integrable Fourier moment; inverse Fourier duality and smooth-test separation identify the representative almost everywhere.
-/

open MeasureTheory Set Filter Topology TemperedDistribution FourierTransform
open scoped ContDiff ENNReal SchwartzMap
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem planar_density_ae_eq {f g : ℂ → ℂ}
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (h : ∀ ψ : 𝓢(ℂ,ℂ), (∫ z : ℂ, ψ z • f z) = ∫ z : ℂ, ψ z • g z) :
    f =ᵐ[volume] g := by
  apply ae_eq_of_integral_contDiff_smul_eq hf hg
  intro u hu hsupp
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ u) := hsupp.comp_left rfl
  have hd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ u) := Complex.ofRealCLM.contDiff.comp hu
  have hp := h (hc.toSchwartzMap hd)
  have he (z : ℂ) : (hc.toSchwartzMap hd) z = (u z : ℂ) := rfl
  simp only [he] at hp
  simpa [Complex.real_smul] using hp

private theorem planar_multiplier_ae (v w : Lp ℂ 1 (volume : Measure ℂ))
    (a : ℂ → ℂ) (ha : a.HasTemperateGrowth)
    (h : smulLeftCLM ℂ a (v : 𝓢'(ℂ,ℂ)) = (w : 𝓢'(ℂ,ℂ))) :
    (fun z : ℂ => a z * v z) =ᵐ[volume] w := by
  have hl : LocallyIntegrable (fun z : ℂ => a z * v z) := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    exact IntegrableOn.continuousOn_mul ha.1.continuous.continuousOn
      (L1.integrable_coeFn v).integrableOn hK
  apply planar_density_ae_eq hl (L1.integrable_coeFn w).locallyIntegrable
  intro ψ
  have he := congrArg (fun T : 𝓢'(ℂ,ℂ) => T ψ) h
  simp only [smulLeftCLM_apply_apply,Lp.toTemperedDistribution_apply,
    SchwartzMap.smulLeftCLM_apply_apply ha] at he
  convert he using 1
  apply integral_congr_ae
  filter_upwards with z
  simp only [smul_eq_mul]
  ring

private theorem planar_fourierInv_duality {f g : ℂ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ z : ℂ, (𝓕⁻ f) z • g z) = ∫ z : ℂ, f z • (𝓕⁻ g) z := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))
    (L := -(innerₗ ℂ)) Real.continuous_fourierChar continuous_inner.neg hf hg
  have he : (-(innerₗ ℂ)).flip = -(innerₗ ℂ) := by
    ext x y
    exact congrArg Neg.neg (real_inner_comm x y)
  rw [he] at h
  exact h

/-- All integer Sobolev orders of a planar tempered distribution yield a single
Fourier density with every integrable polynomial moment. -/
theorem planar_all_sobolev_fourier_moments (u : 𝓢'(ℂ,ℂ))
    (hu : ∀ n : ℕ, MemSobolev (n:ℝ) 2 u) :
    ∃ v : Lp ℂ 1 (volume : Measure ℂ), 𝓕 u = (v : 𝓢'(ℂ,ℂ)) ∧
      ∀ n : ℕ, Integrable (fun z : ℂ => ‖z‖^n * ‖v z‖) := by
  obtain ⟨v,hv⟩ := (hu 2).fourier_memL1 (by norm_num [Complex.finrank_real_complex])
  refine ⟨v,hv,?_⟩
  intro n
  have hb : MemSobolev 2 2 (besselPotential ℂ ℂ (2*(n:ℝ)) u) := by
    apply memSobolev_besselPotential_iff.mpr
    convert hu (2*n+2) using 1; push_cast; ring
  obtain ⟨w,hw⟩ := hb.fourier_memL1 (by norm_num [Complex.finrank_real_complex])
  rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply,hv] at hw
  have he : smulLeftCLM ℂ (fun z : ℂ => (((1+‖z‖^2)^n:ℝ):ℂ))
      (v : 𝓢'(ℂ,ℂ)) = (w : 𝓢'(ℂ,ℂ)) := by
    simpa only [mul_div_cancel_left₀ (n:ℝ) (show (2:ℝ) ≠ 0 by norm_num),
      Real.rpow_natCast] using hw
  have ha : (fun z : ℂ => (((1+‖z‖^2)^n:ℝ):ℂ)).HasTemperateGrowth := by fun_prop
  have hae := planar_multiplier_ae v w _ ha he
  have hi : Integrable (fun z : ℂ => (((1+‖z‖^2)^n:ℝ):ℂ) * v z) :=
    (L1.integrable_coeFn w).congr hae.symm
  have hnorm : Integrable (fun z : ℂ => (1+‖z‖^2)^n * ‖v z‖) := by
    convert hi.norm using 1
    ext z
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply hnorm.mono'
    ((continuous_norm.pow n).aestronglyMeasurable.mul (Lp.aestronglyMeasurable v).norm)
  filter_upwards with z
  change ‖‖z‖^n * ‖v z‖‖ ≤ (1+‖z‖^2)^n * ‖v z‖
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  gcongr
  nlinarith [sq_nonneg (‖z‖-1)]

/-- A planar L² class in every nonnegative integer Sobolev space has an actual
smooth representative. Equality is proved almost everywhere by distributional Fourier inversion. -/
theorem planar_all_sobolev_smooth_representative (u : Lp ℂ 2 (volume : Measure ℂ))
    (hu : ∀ n : ℕ, MemSobolev (n:ℝ) 2 (u : 𝓢'(ℂ,ℂ))) :
    ∃ f : ℂ → ℂ, ContDiff ℝ ∞ f ∧ f =ᵐ[volume] u := by
  obtain ⟨v,hv,hm⟩ := planar_all_sobolev_fourier_moments (u : 𝓢'(ℂ,ℂ)) hu
  let f : ℂ → ℂ := 𝓕⁻ (v : ℂ → ℂ)
  have hs : ContDiff ℝ ∞ f := by
    have hF := Real.contDiff_fourier (N := ⊤) (fun n _ => hm n)
    have he : f = fun z : ℂ => 𝓕 (v : ℂ → ℂ) (-z) := by
      funext z
      exact Real.fourierInv_eq_fourier_neg _ z
    rw [he]
    exact hF.comp contDiff_neg
  refine ⟨f,hs,?_⟩
  apply planar_density_ae_eq hs.continuous.locallyIntegrable
    ((Lp.memLp u).locallyIntegrable (by norm_num))
  intro ψ
  have hu' : (u : 𝓢'(ℂ,ℂ)) = 𝓕⁻ (v : 𝓢'(ℂ,ℂ)) := by
    rw [← hv,FourierTransform.fourierInv_fourier_eq]
  have hp := congrArg (fun T : 𝓢'(ℂ,ℂ) => T ψ) hu'
  simp only [TemperedDistribution.fourierInv_apply,Lp.toTemperedDistribution_apply] at hp
  rw [hp]
  simpa only [f,SchwartzMap.fourierInv_coe] using
    (planar_fourierInv_duality ψ.integrable (L1.integrable_coeFn v)).symm

end
end GaloisForLFunctions.HTGeometry
