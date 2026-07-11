import GaloisForLFunctions.MeromorphicTranslationFixedField
import GaloisForLFunctions.Bottcher.ModularLambda
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Jacobi theta in the meromorphic translation field

The two-variable Jacobi theta function at a fixed upper-half-plane
parameter is embedded as an analytic germ. Its logarithmic derivative is
an element of the global meromorphic fraction field, with its exact
periodic and quasiperiodic translation laws.
-/

open Filter Topology Set Function

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance thetaUnivDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

theorem jacobiTheta₂_analyticOnNhd_fst (τ : ℂ) (hτ : 0 < τ.im) :
    AnalyticOnNhd ℂ (jacobiTheta₂ · τ) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  exact fun z ↦ differentiableAt_jacobiTheta₂_fst z hτ

theorem jacobiTheta₂'_analyticOnNhd_fst (τ : ℂ) (hτ : 0 < τ.im) :
    AnalyticOnNhd ℂ (jacobiTheta₂' · τ) Set.univ := by
  have h := (jacobiTheta₂_analyticOnNhd_fst τ hτ).deriv
  have heq : (jacobiTheta₂' · τ) = deriv (jacobiTheta₂ · τ) := by
    funext z
    exact (hasDerivAt_jacobiTheta₂_fst z hτ).deriv.symm
  rw [heq]
  exact h

def thetaAnalytic (τ : ℂ) (hτ : 0 < τ.im) : analyticSubring Set.univ :=
  ⟨Germ.coeRingHom (𝓟 Set.univ) (jacobiTheta₂ · τ),
    ⟨fun z ↦ jacobiTheta₂ z τ, jacobiTheta₂_analyticOnNhd_fst τ hτ, rfl⟩⟩

def thetaPrimeAnalytic (τ : ℂ) (hτ : 0 < τ.im) : analyticSubring Set.univ :=
  ⟨Germ.coeRingHom (𝓟 Set.univ) (jacobiTheta₂' · τ),
    ⟨fun z ↦ jacobiTheta₂' z τ, jacobiTheta₂'_analyticOnNhd_fst τ hτ, rfl⟩⟩

def thetaQuasiFactorAnalytic (τ : ℂ) : analyticSubring Set.univ :=
  ⟨Germ.coeRingHom (𝓟 Set.univ)
      (fun z ↦ Complex.exp (-Real.pi * Complex.I * (τ + 2 * z))),
    ⟨_, by
      rw [Complex.analyticOnNhd_univ_iff_differentiable]
      fun_prop, rfl⟩⟩

theorem thetaAnalytic_ne_zero (τ : ℂ) (hτ : 0 < τ.im) :
    thetaAnalytic τ hτ ≠ 0 := by
  intro hzero
  have hv := congrArg Subtype.val hzero
  simp only [thetaAnalytic, ZeroMemClass.coe_zero] at hv
  change Germ.ofFun (l := 𝓟 Set.univ) (jacobiTheta₂ · τ) =
    Germ.ofFun (l := 𝓟 Set.univ) (fun _ : ℂ ↦ 0) at hv
  rw [Germ.coe_eq] at hv
  have hz := eventually_principal.mp hv (0 : ℂ) (Set.mem_univ _)
  exact thetaThree_ne_zero_of_im_pos hτ (by simpa [thetaThree] using hz)

theorem addTranslationAnalyticEquiv_theta_one (τ : ℂ) (hτ : 0 < τ.im) :
    addTranslationAnalyticEquiv 1 (thetaAnalytic τ hτ) = thetaAnalytic τ hτ := by
  apply Subtype.ext
  let htr : Tendsto (addTranslation 1) (𝓟 Set.univ) (𝓟 Set.univ) :=
    tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)
  change ((thetaAnalytic τ hτ : analyticSubring Set.univ) : Germ (𝓟 Set.univ) ℂ).compTendsto
      (addTranslation 1) htr = (thetaAnalytic τ hτ : Germ (𝓟 Set.univ) ℂ)
  simp only [thetaAnalytic]
  change Germ.ofFun (l := 𝓟 Set.univ) (fun z ↦ jacobiTheta₂ (z + 1) τ) =
    Germ.ofFun (l := 𝓟 Set.univ) (jacobiTheta₂ · τ)
  rw [Germ.coe_eq]
  exact eventually_principal.mpr fun z hz ↦ jacobiTheta₂_add_left z τ

theorem addTranslationAnalyticEquiv_thetaPrime_one (τ : ℂ) (hτ : 0 < τ.im) :
    addTranslationAnalyticEquiv 1 (thetaPrimeAnalytic τ hτ) = thetaPrimeAnalytic τ hτ := by
  apply Subtype.ext
  let htr : Tendsto (addTranslation 1) (𝓟 Set.univ) (𝓟 Set.univ) :=
    tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)
  change ((thetaPrimeAnalytic τ hτ : analyticSubring Set.univ) : Germ (𝓟 Set.univ) ℂ).compTendsto
      (addTranslation 1) htr = (thetaPrimeAnalytic τ hτ : Germ (𝓟 Set.univ) ℂ)
  simp only [thetaPrimeAnalytic]
  change Germ.ofFun (l := 𝓟 Set.univ) (fun z ↦ jacobiTheta₂' (z + 1) τ) =
    Germ.ofFun (l := 𝓟 Set.univ) (jacobiTheta₂' · τ)
  rw [Germ.coe_eq]
  exact eventually_principal.mpr fun z hz ↦ jacobiTheta₂'_add_left z τ

theorem addTranslationAnalyticEquiv_theta_tau (τ : ℂ) (hτ : 0 < τ.im) :
    addTranslationAnalyticEquiv τ (thetaAnalytic τ hτ) =
      thetaQuasiFactorAnalytic τ * thetaAnalytic τ hτ := by
  apply Subtype.ext
  let htr : Tendsto (addTranslation τ) (𝓟 Set.univ) (𝓟 Set.univ) :=
    tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)
  change ((thetaAnalytic τ hτ : analyticSubring Set.univ) : Germ (𝓟 Set.univ) ℂ).compTendsto
      (addTranslation τ) htr =
    (thetaQuasiFactorAnalytic τ : Germ (𝓟 Set.univ) ℂ) *
      (thetaAnalytic τ hτ : Germ (𝓟 Set.univ) ℂ)
  simp only [thetaAnalytic, thetaQuasiFactorAnalytic]
  change Germ.ofFun (l := 𝓟 Set.univ) (fun z ↦ jacobiTheta₂ (z + τ) τ) =
    Germ.ofFun (l := 𝓟 Set.univ)
      (fun z ↦ Complex.exp (-Real.pi * Complex.I * (τ + 2 * z)) * jacobiTheta₂ z τ)
  rw [Germ.coe_eq]
  exact eventually_principal.mpr fun z hz ↦ jacobiTheta₂_add_left' z τ

theorem addTranslationAnalyticEquiv_thetaPrime_tau (τ : ℂ) (hτ : 0 < τ.im) :
    addTranslationAnalyticEquiv τ (thetaPrimeAnalytic τ hτ) =
      thetaQuasiFactorAnalytic τ *
        (thetaPrimeAnalytic τ hτ -
          constToAnalytic Set.univ (2 * Real.pi * Complex.I) * thetaAnalytic τ hτ) := by
  apply Subtype.ext
  let htr : Tendsto (addTranslation τ) (𝓟 Set.univ) (𝓟 Set.univ) :=
    tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)
  change ((thetaPrimeAnalytic τ hτ : analyticSubring Set.univ) : Germ (𝓟 Set.univ) ℂ).compTendsto
      (addTranslation τ) htr =
    (thetaQuasiFactorAnalytic τ : Germ (𝓟 Set.univ) ℂ) *
      ((thetaPrimeAnalytic τ hτ : Germ (𝓟 Set.univ) ℂ) -
        (constToAnalytic Set.univ (2 * Real.pi * Complex.I) : Germ (𝓟 Set.univ) ℂ) *
          (thetaAnalytic τ hτ : Germ (𝓟 Set.univ) ℂ))
  simp only [thetaPrimeAnalytic, thetaQuasiFactorAnalytic, thetaAnalytic,
    constToAnalytic]
  change Germ.ofFun (l := 𝓟 Set.univ) (fun z ↦ jacobiTheta₂' (z + τ) τ) =
    Germ.ofFun (l := 𝓟 Set.univ)
      (fun z ↦ Complex.exp (-Real.pi * Complex.I * (τ + 2 * z)) *
        (jacobiTheta₂' z τ - 2 * Real.pi * Complex.I * jacobiTheta₂ z τ))
  rw [Germ.coe_eq]
  exact eventually_principal.mpr fun z hz ↦ jacobiTheta₂'_add_left' z τ

def thetaLogDerivMero (τ : ℂ) (hτ : 0 < τ.im) : meroField Set.univ :=
  algebraMap (analyticSubring Set.univ) (meroField Set.univ) (thetaPrimeAnalytic τ hτ) /
    algebraMap (analyticSubring Set.univ) (meroField Set.univ) (thetaAnalytic τ hτ)

theorem addTranslationMeroEquiv_thetaLogDeriv_one (τ : ℂ) (hτ : 0 < τ.im) :
    addTranslationMeroEquiv 1 (thetaLogDerivMero τ hτ) = thetaLogDerivMero τ hτ := by
  rw [thetaLogDerivMero, map_div₀, addTranslationMeroEquiv_algebraMap,
    addTranslationMeroEquiv_algebraMap, addTranslationAnalyticEquiv_thetaPrime_one,
    addTranslationAnalyticEquiv_theta_one]

theorem addTranslationMeroEquiv_thetaLogDeriv_tau (τ : ℂ) (hτ : 0 < τ.im) :
    addTranslationMeroEquiv τ (thetaLogDerivMero τ hτ) =
      thetaLogDerivMero τ hτ -
        algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (constToAnalytic Set.univ (2 * Real.pi * Complex.I)) := by
  rw [thetaLogDerivMero, map_div₀, addTranslationMeroEquiv_algebraMap,
    addTranslationMeroEquiv_algebraMap, addTranslationAnalyticEquiv_thetaPrime_tau,
    addTranslationAnalyticEquiv_theta_tau]
  have hE : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (thetaQuasiFactorAnalytic τ) ≠ 0 := by
    apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    intro hzero
    have hv := congrArg Subtype.val hzero
    change Germ.ofFun (l := 𝓟 Set.univ)
      (fun z ↦ Complex.exp (-Real.pi * Complex.I * (τ + 2 * z))) =
        Germ.ofFun (l := 𝓟 Set.univ) (fun _ : ℂ ↦ 0) at hv
    rw [Germ.coe_eq] at hv
    exact Complex.exp_ne_zero _ (eventually_principal.mp hv 0 (Set.mem_univ _))
  have hθ : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (thetaAnalytic τ hτ) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (thetaAnalytic_ne_zero τ hτ)
  simp only [map_mul, map_sub]
  field_simp

end

end GaloisForLFunctions
