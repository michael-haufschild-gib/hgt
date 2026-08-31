import GaloisForLFunctions.HTGeometry.PairedQuasiEllipticCollapse
import GaloisForLFunctions.HTGeometry.PuncturedQuasiPeriodRigidity
import GaloisForLFunctions.HTGeometry.MeromorphicRealizationAlgebra

/-!
# The recentred theta source

The second structural face of the elliptic-gamma logarithmic derivative is a translate of the
theta source, so the one-pole classification is needed in translated form.  Translating a
principal part moves its pole, and the period and quasiperiod identities travel with it.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-- The pole set of the recentred theta source. -/
def shiftedThetaDivisor (τ p : ℂ) : Set ℂ := {z : ℂ | z + p ∈ thetaDivisor τ}

theorem analyticAt_translate_thetaSource_of_notMem {τ p : ℂ} (hτ : 0 < τ.im) {z : ℂ}
    (hz : z ∉ shiftedThetaDivisor τ p) :
    AnalyticAt ℂ (fun w => thetaSource τ (w + p)) z := by
  have h := analyticAt_thetaSource_of_notMem hτ (z := z + p) hz
  exact h.comp (f := fun w : ℂ => w + p) (by fun_prop)

theorem hasPrincipalPart_translate_thetaSource {τ p : ℂ} (hτ : 0 < τ.im) {q : ℂ}
    (hq : q ∈ shiftedThetaDivisor τ p) :
    HasPrincipalPart (fun w => thetaSource τ (w + p)) q 1 := by
  have h := (hasPrincipalPart_thetaSource hτ hq).comp_sub (-p)
  have hfun : (fun w : ℂ => thetaSource τ (w - -p)) = fun w : ℂ => thetaSource τ (w + p) := by
    funext w
    rw [sub_neg_eq_add]
  have hpt : q + p + -p = q := by ring
  rwa [hfun, hpt] at h

theorem eventually_translate_thetaSource_shift {τ p : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z,
      thetaSource τ (w + τ + p) = thetaSource τ (w + p) + -(2 * (Real.pi : ℂ) * Complex.I) := by
  have hpull := (tendsto_nhdsNE_add_const z p).eventually (eventually_thetaSource_shift hτ (z + p))
  filter_upwards [hpull] with w hw
  have hcomm : w + τ + p = w + p + τ := by ring
  rw [hcomm]
  exact hw

/-- **The one-pole classification against the recentred theta source.** -/
theorem const_sub_translate_thetaSource_of_matching_principal_parts
    {τ p : ℂ} (hτ : 0 < τ.im) {U : ℂ → ℂ}
    (hUan : ∀ z ∉ shiftedThetaDivisor τ p, AnalyticAt ℂ U z)
    (hUp : ∀ q ∈ shiftedThetaDivisor τ p, HasPrincipalPart U q 1)
    (hUper : ∀ z, ∀ᶠ w in 𝓝[≠] z, U (w + 1) = U w)
    {k : ℂ} (hUinc : ∀ z, ∀ᶠ w in 𝓝[≠] z, U (w + τ) = U w + k) :
    (∀ x y, toMeromorphicNFOn (fun w => U w - thetaSource τ (w + p)) Set.univ x
        = toMeromorphicNFOn (fun w => U w - thetaSource τ (w + p)) Set.univ y)
      ∧ k = -(2 * (Real.pi : ℂ) * Complex.I) := by
  refine const_sub_of_matching_principal_parts hτ (shiftedThetaDivisor τ p) 1 hUan
    (fun z hz => analyticAt_translate_thetaSource_of_notMem hτ hz) hUp
    (fun q hq => hasPrincipalPart_translate_thetaSource hτ hq) hUper ?_ hUinc ?_
  · intro z
    filter_upwards with w
    have hcomm : w + 1 + p = w + p + 1 := by ring
    rw [hcomm]
    exact thetaSource_periodic τ (w + p)
  · intro z
    exact eventually_translate_thetaSource_shift hτ z

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- **The recentred one-pole classification in the meromorphic field.** -/
theorem eq_translate_thetaLogDerivMero_add_const_of_matching_principal_parts
    {τ p : ℂ} (hτ : 0 < τ.im) {U : meroField (Set.univ : Set ℂ)} {u : ℂ → ℂ}
    (hU : RealizesMero U u)
    (huan : ∀ z ∉ shiftedThetaDivisor τ p, AnalyticAt ℂ u z)
    (hup : ∀ q ∈ shiftedThetaDivisor τ p, HasPrincipalPart u q 1)
    (huper : ∀ z, ∀ᶠ w in 𝓝[≠] z, u (w + 1) = u w)
    {k : ℂ} (huinc : ∀ z, ∀ᶠ w in 𝓝[≠] z, u (w + τ) = u w + k) :
    (∃ c : ℂ, U = addTranslationMeroEquiv p (thetaLogDerivMero τ hτ)
        + algebraMap ℂ (meroField (Set.univ : Set ℂ)) c)
      ∧ k = -(2 * (Real.pi : ℂ) * Complex.I) := by
  obtain ⟨hconst, hk⟩ :=
    const_sub_translate_thetaSource_of_matching_principal_parts hτ huan hup huper huinc
  have hVan : ∀ z ∉ shiftedThetaDivisor τ p,
      AnalyticAt ℂ (fun w => thetaSource τ (w + p)) z :=
    fun z hz => analyticAt_translate_thetaSource_of_notMem hτ hz
  have hVp : ∀ q ∈ shiftedThetaDivisor τ p,
      HasPrincipalPart (fun w => thetaSource τ (w + p)) q 1 :=
    fun q hq => hasPrincipalPart_translate_thetaSource hτ hq
  have hdm : MeromorphicOn (fun w => u w - thetaSource τ (w + p)) Set.univ := by
    intro z hz
    exact ((meromorphicOn_of_principal_parts huan hup) z hz).sub
      ((meromorphicOn_of_principal_parts hVan hVp) z hz)
  have hev := eventually_eq_const_of_constant_toMeromorphicNFOn hdm hconst
  have hsub : RealizesMero (U - addTranslationMeroEquiv p (thetaLogDerivMero τ hτ))
      (fun w => u w - thetaSource τ (w + p)) :=
    realizesMero_sub hU (realizesMero_translate (realizesMero_thetaLogDerivMero τ hτ) p)
  have heq : U - addTranslationMeroEquiv p (thetaLogDerivMero τ hτ)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ))
        (toMeromorphicNFOn (fun w => u w - thetaSource τ (w + p)) Set.univ 0) :=
    realizesMero_eq_of_eventuallyEq hsub (realizesMero_algebraMap_complex _) hev
  exact ⟨⟨_, by linear_combination heq⟩, hk⟩

end

end GaloisForLFunctions.HTGeometry
