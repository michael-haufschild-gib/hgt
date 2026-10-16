import GaloisForLFunctions.RHTower.EvenSectorSmoothSourceScalarization
import GaloisForLFunctions.RHTower.EvenSectorExactFibreRecovery
import GaloisForLFunctions.RHTower.WeilFullConeBochnerMeasure

/-!
# Exact arithmetic and energy moments of smooth scalarization

The whole-profile identity is compatible with the existing real coefficient
mixture spaces. Consequently scalarization preserves both the complete
integer trace and the actual archimedean cost.
-/

open Complex MeasureTheory Set Finsupp Zeta23
open scoped ContDiff NNReal
noncomputable section
namespace RHTower.EvenSector
open WeilOneSided WeilSpectral

def smoothMixtureProfile : (SmoothEvenPolarTestFn →₀ ℝ) →ₗ[ℝ] (ℝ → ℂ) :=
  linearCombination ℝ (fun f => EF.weilTest f.1.1.1 f.1.1.1)

def smoothMixtureTrace : (SmoothEvenPolarTestFn →₀ ℝ) →ₗ[ℝ] (LogIndex →₀ ℝ) :=
  linearCombination ℝ (fun f => logVector f.1.1)

def smoothMixtureEnergy : (SmoothEvenPolarTestFn →₀ ℝ) →ₗ[ℝ] ℝ :=
  linearCombination ℝ (fun f => weilArchRe (EF.weilTest f.1.1.1 f.1.1.1))

def realPolarMixtureProfile : (WeilEvenPolarTestFn →₀ ℝ) →ₗ[ℝ] (ℝ → ℂ) :=
  linearCombination ℝ (fun f => EF.weilTest f.1.1 f.1.1)

theorem exists_smooth_scalarization_profile (c : SmoothEvenPolarTestFn →₀ ℝ)
    (hc : ∀ f,0≤c f) :
    ∃ f : SmoothEvenPolarTestFn,EF.weilTest f.1.1.1 f.1.1.1=smoothMixtureProfile c := by
  let d : SmoothEvenPolarTestFn →₀ ℝ≥0 := c.mapRange Real.toNNReal Real.toNNReal_zero
  obtain ⟨f,hf⟩ := exists_smoothPolar_exact_autocorrelation d
  refine ⟨f,hf.trans ?_⟩
  funext u
  unfold polarMixtureProfile smoothPolarCoefficients
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ a b => by push_cast; ring)]
  dsimp only [d]
  erw [Finsupp.sum_mapRange_index (fun _ => by simp)]
  simp only [smoothMixtureProfile,linearCombination_apply,Finsupp.sum,
    Finset.sum_apply,Pi.smul_apply,Complex.real_smul]
  apply Finset.sum_congr rfl
  intro g _
  change (((Real.toNNReal (c g) : ℝ≥0) : ℝ) : ℂ)*_=(c g : ℂ)*_
  rw [Real.coe_toNNReal _ (hc g)]

theorem trace_eq_of_smooth_profile {f : SmoothEvenPolarTestFn}
    {c : SmoothEvenPolarTestFn →₀ ℝ}
    (h : EF.weilTest f.1.1.1 f.1.1.1=smoothMixtureProfile c) :
    logVector f.1.1=smoothMixtureTrace c := by
  classical
  ext j
  rw [logVector_apply]
  unfold logValue
  rw [h]
  simp only [smoothMixtureProfile,smoothMixtureTrace,linearCombination_apply,Finsupp.sum,
    Finset.sum_apply,Pi.smul_apply,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,
    Complex.real_smul,← Finset.sum_add_distrib,Complex.re_sum,Finset.sum_div,
    logVector_apply,logValue]
  apply Finset.sum_congr rfl
  intro g _
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.add_re]
  ring

theorem weilArchRe_smoothMixtureProfile (c : SmoothEvenPolarTestFn →₀ ℝ) :
    weilArchRe (smoothMixtureProfile c)=smoothMixtureEnergy c := by
  classical
  have he (k : ℝ → ℂ) : weilArchRe k=(weilFullFunctional 0 k).re := by
    simp [weilArchRe,weilFullFunctional]
  rw [he]
  change (weilFullFunctional 0
    (∑ f ∈ c.support,(c f : ℂ) • EF.weilTest f.1.1.1 f.1.1.1)).re=_
  rw [weilFullFunctional_sum 0 _ (fun f _ =>
    (admissible_weilTest f.1.1.2.1 f.1.1.2.2).smul _)]
  simp only [weilFullFunctional_smul,Complex.re_sum,smoothMixtureEnergy,
    linearCombination_apply,Finsupp.sum,smul_eq_mul,he,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

/-- Scalarization preserves the whole profile and both existing mixture
observables exactly. Nonnegative coefficients are data of the mixture. -/
theorem exists_smooth_scalarization_moments (c : SmoothEvenPolarTestFn →₀ ℝ)
    (hc : ∀ f,0≤c f) :
    ∃ f : SmoothEvenPolarTestFn,
      EF.weilTest f.1.1.1 f.1.1.1=smoothMixtureProfile c ∧
      logVector f.1.1=smoothMixtureTrace c ∧
      weilArchRe (EF.weilTest f.1.1.1 f.1.1.1)=smoothMixtureEnergy c := by
  obtain ⟨f,hf⟩ := exists_smooth_scalarization_profile c hc
  exact ⟨f,hf,trace_eq_of_smooth_profile hf,by rw [hf,weilArchRe_smoothMixtureProfile]⟩

end RHTower.EvenSector
