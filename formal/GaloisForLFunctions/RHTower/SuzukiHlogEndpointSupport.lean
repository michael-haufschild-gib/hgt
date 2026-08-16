import GaloisForLFunctions.RHTower.L2FourierEndpointOrthogonality
import GaloisForLFunctions.RHTower.SuzukiHlogHilbertFormDomain

/-!
# Endpoint support for Suzuki's logarithmic form domain

Membership in Suzuki's exact aperture form domain is stated using compact support of the inverse
Fourier transform. Endpoint orthogonality uses compact support of the forward transform.
Fourier-squared reflection identifies these support conditions without any regularity upgrade:
reflection preserves the symmetric aperture interval.
-/

noncomputable section

open MeasureTheory Set FourierTransform

namespace RHTower

/-- Every vector in Suzuki's aperture form domain has forward Fourier transform supported in the
same symmetric aperture interval. -/
theorem suzukiHlogFormDomain_fourier_bandSupport
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    ∀ᵐ ξ : ℝ, a.1 < |ξ| →
      (𝓕 (suzukiHlogWeightedToL2 f.1) : Lp ℂ 2 (volume : Measure ℝ)) ξ = 0 := by
  let v : Lp ℂ 2 (volume : Measure ℝ) := suzukiHlogWeightedToL2 f.1
  let t : Lp ℂ 2 (volume : Measure ℝ) := suzukiHlogFourierToTime f.1
  have ht : t = 𝓕⁻ v := by rfl
  have hfix := indicatorCutoff_suzukiHlogFormEmbedding a f
  have hfixae : ((indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) t : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] t := by
    change ((indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) (suzukiHlogFormEmbedding a f) :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      suzukiHlogFormEmbedding a f
    rw [hfix]
  have hsupport : ∀ᵐ x : ℝ, a.1 < |x| → t x = 0 := by
    filter_upwards [
      indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) t,
      hfixae] with x hcut hfixx hout
    have hxnot : x ∉ centralInterval a.1 := by
      intro hx
      exact (not_le_of_gt hout) (abs_le.mpr hx)
    rw [hcut, Set.indicator_of_notMem hxnot] at hfixx
    exact hfixx.symm
  have hsupportNeg : ∀ᵐ x : ℝ, a.1 < |-x| → t (-x) = 0 := by
    simpa [Function.comp_def] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hsupport
  have hreflect : 𝓕 v = l2Reflection t := by
    rw [ht]
    exact (MellinL2.l2Reflection_fourierInv v).symm
  rw [show suzukiHlogWeightedToL2 f.1 = v by rfl, hreflect]
  filter_upwards [hsupportNeg,
    Lp.coeFn_compMeasurePreserving t
      (Measure.measurePreserving_neg (volume : Measure ℝ))] with x hs hr hout
  have hr' : (l2Reflection t : ℝ → ℂ) x = t (-x) := by
    simpa [l2Reflection, l2ReflectionIsometry, Function.comp_def] using hr
  rw [hr', hs]
  simpa using hout

end RHTower
