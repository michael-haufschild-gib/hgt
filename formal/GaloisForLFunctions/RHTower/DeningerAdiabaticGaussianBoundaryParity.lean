import GaloisForLFunctions.RHTower.DeningerAdiabaticTransgression
import GaloisForLFunctions.RHTower.DeningerCommutatorExactKernel
import GaloisForLFunctions.RHTower.RouteEDeningerVacuumCollarDecomposition
import GaloisForLFunctions.RHTower.DeningerFloquetPoissonSample
import GaloisForLFunctions.RHTower.DeningerMeyerLogGaussianUniversalOrbitCriterion

/-!
# Exact adiabatic balance and the reflected Gaussian boundary

Equality of the actual Gamma endpoint and cofinal Euler flux holds precisely for
literal Poisson sources. The reflected log Gaussian gives an actual Meyer source
fixed by collar exchange whose complete boundary is nonzero: its nonvanishing Xi
evaluations exclude the Poisson range.

The boundary is anti-Fourier. Every Fourier-fixed Schwartz test annihilates the
Gamma and flux values separately, while a test in the anti-Fourier sector detects
their difference. The detecting test is obtained by the four-term Fourier projection.
These statements concern the actual tempered-distribution pairing; they assert no
identification with a physical conormal reader.
-/

namespace RHTower

open SchwartzMap FourierTransform

noncomputable section


/-- Full Gamma/flux cancellation has exactly the literal Poisson source class. -/
theorem deningerAdiabaticGamma_eq_transgression_iff_poisson
    (h : DeningerMeyerSource) :
    deningerAdiabaticGammaBoundary h = deningerAdiabaticGreenStokesTransgression h ↔
      DeningerMeyerSource.toSource h ∈ Set.range deningerPoissonSource := by
  have hk : deningerMobiusCommutator (DeningerMeyerSource.toSource h) = 0 ↔
      DeningerMeyerSource.toSource h ∈ Set.range deningerPoissonSource := by
    change DeningerMeyerSource.toSource h ∈
      {u : DeningerExpSchwartz | deningerMobiusCommutator u = 0} ↔ _
    rw [deningerCommutator_exact_kernel]
  rw [← hk, XI_BV_GREEN_STOKES_STRICT_DESCENT, sub_eq_zero]

/-- The fixed reflected log Gaussian, in the actual Meyer source topology. -/
def deningerAdiabaticGaussianSource : DeningerMeyerSource :=
  DeningerMeyerSource.toSource.symm
    (deningerExpSchwartzOfStrongLogDecay
      (deningerMeyerReflectedLogGaussianSource : ℝ → ℂ)
      deningerMeyerReflectedLogGaussianSource.property)

theorem deningerAdiabaticGaussianSource_exchange_fixed :
    deningerMeyerCollarExchange deningerAdiabaticGaussianSource =
      deningerAdiabaticGaussianSource := by
  apply DeningerMeyerSource.toSource.injective
  rw [deningerMeyerCollarExchange_toSource]
  apply Subtype.ext
  ext t
  change (Real.exp (-t) : ℂ) *
      (deningerMeyerReflectedLogGaussianSource : ℝ → ℂ) (-t) =
    (deningerMeyerReflectedLogGaussianSource : ℝ → ℂ) t
  exact congrArg (fun u : DeningerMeyerStrongLogTarget => (u : ℝ → ℂ) t)
    deningerMeyerReflectedLogGaussianSource_J_fixed

theorem deningerAdiabaticGaussianSource_not_poisson :
    DeningerMeyerSource.toSource deningerAdiabaticGaussianSource ∉
      Set.range deningerPoissonSource := by
  rintro ⟨f, hf⟩
  have heq : deningerMeyerStrongLogSumLM f = deningerMeyerReflectedLogGaussianSource := by
    apply Subtype.ext
    funext t
    have ht := congrFun (deningerPoissonSource_coe_eq_strongLogSum f) t
    rw [hf] at ht
    exact ht.symm
  have hclass : (Submodule.Quotient.mk deningerMeyerReflectedLogGaussianSource :
      DeningerMeyerStrongLogCohomology) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 ⟨f, heq⟩
  have hne := deningerMeyerReflectedLogGaussianCohomologyClass_evaluation_ne_zero
    (Classical.arbitrary XiDivisorSupport)
  rw [deningerMeyerReflectedLogGaussianCohomologyClass, hclass, map_zero] at hne
  exact hne rfl

/-- The retained fixed source has a nonzero complete distributional boundary. -/
theorem deningerAdiabaticGaussianGamma_ne_transgression :
    deningerAdiabaticGammaBoundary deningerAdiabaticGaussianSource ≠
      deningerAdiabaticGreenStokesTransgression deningerAdiabaticGaussianSource := by
  exact fun h => deningerAdiabaticGaussianSource_not_poisson
    ((deningerAdiabaticGamma_eq_transgression_iff_poisson _).1 h)

/-- Collar fixedness puts the complete boundary in the anti-Fourier sector. -/
theorem deningerAdiabaticGaussianBoundary_fourier_neg :
    deningerMobiusCommutator
        (DeningerMeyerSource.toSource deningerAdiabaticGaussianSource) =
      -𝓕 (deningerMobiusCommutator
        (DeningerMeyerSource.toSource deningerAdiabaticGaussianSource)) := by
  have h := deningerMobiusCommutator_fourier_covariance
    (DeningerMeyerSource.toSource deningerAdiabaticGaussianSource)
  rw [← deningerMeyerCollarExchange_toSource,
    deningerAdiabaticGaussianSource_exchange_fixed] at h
  exact h

/-- On every Fourier-fixed test the actual Gamma endpoint and Euler flux agree. -/
theorem deningerAdiabaticGaussianGamma_eq_transgression_on_fourier_fixed
    (g : 𝓢(ℝ, ℂ)) (hg : 𝓕 g = g) :
    deningerAdiabaticGammaBoundary deningerAdiabaticGaussianSource g =
      deningerAdiabaticGreenStokesTransgression deningerAdiabaticGaussianSource g := by
  have hp := congrArg (fun D : 𝓢'(ℝ, ℂ) => D g)
    deningerAdiabaticGaussianBoundary_fourier_neg
  change deningerMobiusCommutator
      (DeningerMeyerSource.toSource deningerAdiabaticGaussianSource) g =
    -deningerMobiusCommutator
      (DeningerMeyerSource.toSource deningerAdiabaticGaussianSource) (𝓕 g) at hp
  rw [hg] at hp
  have hz : deningerMobiusCommutator
      (DeningerMeyerSource.toSource deningerAdiabaticGaussianSource) g = 0 := by
    linear_combination (1 / 2 : ℂ) * hp
  have hb := congrArg (fun D : 𝓢'(ℝ, ℂ) => D g)
    (XI_BV_GREEN_STOKES_STRICT_DESCENT deningerAdiabaticGaussianSource)
  change deningerMobiusCommutator
      (DeningerMeyerSource.toSource deningerAdiabaticGaussianSource) g =
    deningerAdiabaticGammaBoundary deningerAdiabaticGaussianSource g -
      deningerAdiabaticGreenStokesTransgression deningerAdiabaticGaussianSource g at hb
  rw [hz] at hb
  exact sub_eq_zero.mp hb.symm

/-- Each endpoint/flux value vanishes separately on Fourier-fixed tests. -/
theorem deningerAdiabaticGaussianGamma_transgression_zero_on_fourier_fixed
    (g : 𝓢(ℝ, ℂ)) (hg : 𝓕 g = g) :
    deningerAdiabaticGammaBoundary deningerAdiabaticGaussianSource g = 0 ∧
      deningerAdiabaticGreenStokesTransgression deningerAdiabaticGaussianSource g = 0 := by
  have hGamma : deningerAdiabaticGammaBoundary deningerAdiabaticGaussianSource g = 0 := by
    rw [deningerAdiabaticGammaBoundary, deningerAdiabaticGaussianSource_exchange_fixed]
    change deningerAdiabaticGammaDistribution deningerAdiabaticGaussianSource (𝓕 g) -
      deningerAdiabaticGammaDistribution deningerAdiabaticGaussianSource g = 0
    rw [hg, sub_self]
  exact ⟨hGamma,
    (deningerAdiabaticGaussianGamma_eq_transgression_on_fourier_fixed g hg).symm.trans hGamma⟩

/-- A Schwartz test detects the part of the actual boundary surviving this symmetry. -/
theorem deningerAdiabaticGaussian_exists_boundary_detecting_test :
    ∃ g : 𝓢(ℝ, ℂ),
      deningerAdiabaticGammaBoundary deningerAdiabaticGaussianSource g ≠
        deningerAdiabaticGreenStokesTransgression deningerAdiabaticGaussianSource g := by
  by_contra h
  push Not at h
  exact deningerAdiabaticGaussianGamma_ne_transgression (by ext g; exact h g)

/-- A test in the anti-Fourier sector detects the surviving complete boundary. -/
theorem deningerAdiabaticGaussian_exists_anti_fourier_detecting_test :
    ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = -g ∧
      deningerAdiabaticGammaBoundary deningerAdiabaticGaussianSource g ≠
        deningerAdiabaticGreenStokesTransgression deningerAdiabaticGaussianSource g := by
  obtain ⟨g, hg⟩ := deningerAdiabaticGaussian_exists_boundary_detecting_test
  let D := deningerMobiusCommutator
    (DeningerMeyerSource.toSource deningerAdiabaticGaussianSource)
  have hD (u : 𝓢(ℝ, ℂ)) : D (𝓕 u) = -D u := by
    have hp := congrArg (fun E : 𝓢'(ℝ, ℂ) => E u)
      deningerAdiabaticGaussianBoundary_fourier_neg
    change D u = -D (𝓕 u) at hp
    linear_combination hp
  have h4 : 𝓕 (𝓕 (𝓕 (𝓕 g))) = g := by
    ext x
    rw [deningerFourierSq_apply, deningerFourierSq_apply, neg_neg]
  let k := g - 𝓕 g + 𝓕 (𝓕 g) - 𝓕 (𝓕 (𝓕 g))
  refine ⟨k, ?_, ?_⟩
  · dsimp only [k]
    simp only [sub_eq_add_neg, FourierTransform.fourier_add,
      FourierTransform.fourier_neg, h4]
    abel
  · intro hk
    have hboundary (u : 𝓢(ℝ, ℂ)) : D u =
        deningerAdiabaticGammaBoundary deningerAdiabaticGaussianSource u -
          deningerAdiabaticGreenStokesTransgression deningerAdiabaticGaussianSource u :=
      congrArg (fun E : 𝓢'(ℝ, ℂ) => E u)
        (XI_BV_GREEN_STOKES_STRICT_DESCENT deningerAdiabaticGaussianSource)
    have hk0 : D k = 0 := by rw [hboundary, hk, sub_self]
    have hkm : D k = 4 * D g := by
      simp only [k, map_sub, map_add, hD]
      ring
    have hg0 : D g = 0 := by
      rw [hkm] at hk0
      linear_combination (1 / 4 : ℂ) * hk0
    apply hg
    exact sub_eq_zero.mp ((hboundary g).symm.trans hg0)

end

end RHTower
