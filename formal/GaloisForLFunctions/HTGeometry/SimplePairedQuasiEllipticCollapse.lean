import GaloisForLFunctions.HTGeometry.TranslatedThetaOnePole
import GaloisForLFunctions.HTGeometry.EllipticGammaPairedIncrement

/-!
# The simple paired quasi-elliptic primitives are the elliptic-gamma logarithmic derivative

A period-one meromorphic primitive whose two structural increments are one-pole quasi-elliptic
increments — the first with the theta divisor of `τ`, the second with the recentred theta divisor
of `σ` — differs from the elliptic-gamma logarithmic derivative by a complex constant.  Its
translation defects are therefore literally those of the elliptic gamma function, so its
differential-algebraic shift spectrum and period-coset matroid are the elliptic-gamma ones.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The collapse theorem.**  Every simple paired quasi-elliptic primitive equals the
elliptic-gamma logarithmic derivative up to one complex constant. -/
theorem exists_complex_sub_ellipticGammaLogDerivMero
    {σ τ : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im)
    (hv : LinearIndependent ℚ ![(1 : ℂ), σ, τ])
    {F : meroField (Set.univ : Set ℂ)} {uσ uτ : ℂ → ℂ}
    (hFone : addTranslationMeroEquiv 1 F = F)
    (hUσ : RealizesMero (addTranslationMeroEquiv σ F - F) uσ)
    (hσan : ∀ z ∉ thetaDivisor τ, AnalyticAt ℂ uσ z)
    (hσp : ∀ q ∈ thetaDivisor τ, HasPrincipalPart uσ q 1)
    (hσper : ∀ z, ∀ᶠ w in 𝓝[≠] z, uσ (w + 1) = uσ w)
    {kσ : ℂ} (hσinc : ∀ z, ∀ᶠ w in 𝓝[≠] z, uσ (w + τ) = uσ w + kσ)
    (hUτ : RealizesMero (addTranslationMeroEquiv τ F - F) uτ)
    (hτan : ∀ z ∉ shiftedThetaDivisor σ ((τ - σ) / 2), AnalyticAt ℂ uτ z)
    (hτp : ∀ q ∈ shiftedThetaDivisor σ ((τ - σ) / 2), HasPrincipalPart uτ q 1)
    (hτper : ∀ z, ∀ᶠ w in 𝓝[≠] z, uτ (w + 1) = uτ w)
    {kτ : ℂ} (hτinc : ∀ z, ∀ᶠ w in 𝓝[≠] z, uτ (w + σ) = uτ w + kτ) :
    ∃ c : ℂ, F - ellipticGammaLogDerivMero σ τ hσ hτ
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c := by
  obtain ⟨⟨c₁, hc₁⟩, -⟩ :=
    eq_thetaLogDerivMero_add_const_of_matching_principal_parts hτ hUσ hσan hσp hσper hσinc
  obtain ⟨⟨c₂, hc₂⟩, -⟩ :=
    eq_translate_thetaLogDerivMero_add_const_of_matching_principal_parts hσ hUτ hτan hτp hτper
      hτinc
  obtain ⟨d₁, hd₁⟩ := ellipticGammaExternalLogDerivDefectMero_sigma σ τ hσ hτ
  obtain ⟨d₂, hd₂⟩ := ellipticGammaExternalLogDerivDefectMero_tau σ τ hσ hτ
  rw [ellipticGammaExternalLogDerivDefectMero, algebraMap_complex_eq_constToAnalytic] at hd₁ hd₂
  refine (exists_complex_sub_of_structural_increments (a := c₁ - d₁) (b := c₂ - d₂)
    hv hFone (addTranslationMeroEquiv_ellipticGammaLogDerivMero_one σ τ hσ hτ) ?_ ?_).1
  · rw [hc₁, hd₁, map_sub]
    ring
  · rw [hc₂, hd₂, map_sub]
    ring

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The defect family of a simple paired quasi-elliptic primitive is the elliptic-gamma one.**
Every translation defect of such a primitive is literally the corresponding elliptic-gamma external
defect, so the elliptic-gamma differential-algebraic shift spectrum and period-coset matroid hold
for it verbatim. -/
theorem defect_eq_ellipticGammaExternalLogDerivDefectMero
    {σ τ : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im)
    (hv : LinearIndependent ℚ ![(1 : ℂ), σ, τ])
    {F : meroField (Set.univ : Set ℂ)} {uσ uτ : ℂ → ℂ}
    (hFone : addTranslationMeroEquiv 1 F = F)
    (hUσ : RealizesMero (addTranslationMeroEquiv σ F - F) uσ)
    (hσan : ∀ z ∉ thetaDivisor τ, AnalyticAt ℂ uσ z)
    (hσp : ∀ q ∈ thetaDivisor τ, HasPrincipalPart uσ q 1)
    (hσper : ∀ z, ∀ᶠ w in 𝓝[≠] z, uσ (w + 1) = uσ w)
    {kσ : ℂ} (hσinc : ∀ z, ∀ᶠ w in 𝓝[≠] z, uσ (w + τ) = uσ w + kσ)
    (hUτ : RealizesMero (addTranslationMeroEquiv τ F - F) uτ)
    (hτan : ∀ z ∉ shiftedThetaDivisor σ ((τ - σ) / 2), AnalyticAt ℂ uτ z)
    (hτp : ∀ q ∈ shiftedThetaDivisor σ ((τ - σ) / 2), HasPrincipalPart uτ q 1)
    (hτper : ∀ z, ∀ᶠ w in 𝓝[≠] z, uτ (w + 1) = uτ w)
    {kτ : ℂ} (hτinc : ∀ z, ∀ᶠ w in 𝓝[≠] z, uτ (w + σ) = uτ w + kτ) (k : ℂ) :
    addTranslationMeroEquiv k F - F
      = ellipticGammaExternalLogDerivDefectMero k σ τ hσ hτ := by
  obtain ⟨c, hc⟩ := exists_complex_sub_ellipticGammaLogDerivMero hσ hτ hv hFone hUσ hσan hσp
    hσper hσinc hUτ hτan hτp hτper hτinc
  rw [ellipticGammaExternalLogDerivDefectMero]
  exact defect_eq_of_sub_algebraMap hc k

end

end GaloisForLFunctions.HTGeometry
