import GaloisForLFunctions.HTGeometry.EllipticGammaConePresentationBridge
import GaloisForLFunctions.HTGeometry.MeromorphicRealizationAlgebra
import GaloisForLFunctions.HTGeometry.EllipticGammaSourceGermConstraint
import GaloisForLFunctions.HTGeometry.EllipticGammaTranslatePacket

/-!
# The gamma jets realize the germs of the translation packet

The meromorphic-field element of the elliptic gamma function is realized by the shifted cone
presentation, hence its logarithmic derivative by the shifted source, hence every translate of that
by a translated source, and every differential jet of a translate by the corresponding jet function.

* `realizesMero_ellipticGammaMero`, `realizesMero_ellipticGammaLogDerivMero`;
* `realizesMero_gammaJetSource`.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero

variable {σ τ : ℂ}

theorem analyticOnNhd_ellipticGammaForwardProduct (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    AnalyticOnNhd ℂ (ellipticGammaForwardProduct σ τ) (Set.univ : Set ℂ) := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  exact differentiable_ellipticGammaForwardProduct hσ hτ

theorem analyticOnNhd_ellipticGammaBackwardProduct (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    AnalyticOnNhd ℂ (ellipticGammaBackwardProduct σ τ) (Set.univ : Set ℂ) := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  exact differentiable_ellipticGammaBackwardProduct hσ hτ

/-- **The elliptic gamma germ is realized by the shifted cone presentation.** -/
theorem realizesMero_ellipticGammaMero (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    RealizesMero (ellipticGammaMero σ τ hσ hτ)
      (fun z ↦ ellipticGammaCone σ τ (z + gammaPresentationShift τ)) :=
  ⟨ellipticGammaForwardAnalytic σ τ hσ hτ, ellipticGammaBackwardAnalytic σ τ hσ hτ,
    ellipticGammaForwardProduct σ τ, ellipticGammaBackwardProduct σ τ,
    ellipticGammaBackwardAnalytic_ne_zero σ τ hσ hτ,
    analyticOnNhd_ellipticGammaForwardProduct hσ hτ,
    analyticOnNhd_ellipticGammaBackwardProduct hσ hτ, rfl, rfl, rfl,
    fun z _ ↦ ellipticGammaCone_shift_eq σ τ z⟩

/-- **The elliptic gamma source germ is realized by the shifted source function.** -/
theorem realizesMero_ellipticGammaLogDerivMero (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    RealizesMero (ellipticGammaLogDerivMero σ τ hσ hτ)
      (fun z ↦ ellipticGammaSource σ τ (z + gammaPresentationShift τ)) := by
  have h := realizesMero_logDeriv (realizesMero_ellipticGammaMero hσ hτ)
    (ellipticGammaMero_ne_zero σ τ hσ hτ)
  have hfun : logDeriv (fun z ↦ ellipticGammaCone σ τ (z + gammaPresentationShift τ))
      = fun z ↦ ellipticGammaSource σ τ (z + gammaPresentationShift τ) := by
    funext z
    rw [logDeriv_comp_add_const, ellipticGammaSource]
  rwa [hfun] at h

/-- **Every jet of a translated gamma source realizes the corresponding jet germ.** -/
theorem realizesMero_gammaJetSource (hσ : 0 < σ.im) (hτ : 0 < τ.im) (a : ℂ) (j : ℕ) :
    RealizesMero
      (differentialJet j (addTranslationMeroEquiv a (ellipticGammaLogDerivMero σ τ hσ hτ)))
      (gammaJetSource σ τ (-(gammaPresentationShift τ + a)) j) := by
  have htrans := realizesMero_translate (realizesMero_ellipticGammaLogDerivMero hσ hτ) a
  have hfun : (fun z ↦ ellipticGammaSource σ τ (z + a + gammaPresentationShift τ))
      = logDeriv (ellipticGammaConeTranslate σ τ (-(gammaPresentationShift τ + a))) := by
    rw [logDeriv_ellipticGammaConeTranslate]
    funext z
    congr 1
    ring
  rw [hfun] at htrans
  exact realizesMero_iteratedDeriv htrans j

end

end GaloisForLFunctions.HTGeometry
