import GaloisForLFunctions.HTGeometry.RelativeAdmissionSpectrumNaturalityLaw

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K L : Type*}

/-- Covariant coface of a rank-one difference source with shift `σ` and connection coefficient
`c`. -/
def sourceGaugeCovariantCoface [CommRing K]
    (σ : K →+* K) (c g : K) : K :=
  σ g - c * g

/-- A source section satisfying `σ h = c h` is horizontal for its covariant coface. -/
theorem sourceGaugeCovariantCoface_horizontal [CommRing K]
    (σ : K →+* K) (c h : K) (hh : σ h = c * h) :
    sourceGaugeCovariantCoface σ c h = 0 := by
  rw [sourceGaugeCovariantCoface, hh, sub_self]

/-- **Source-factor transgression.**  The covariant coface converts multiplication by a horizontal
source section into the ordinary difference of the remaining factor. -/
theorem sourceGaugeCovariantCoface_mul_horizontal [CommRing K]
    (σ : K →+* K) (c h f : K) (hh : σ h = c * h) :
    sourceGaugeCovariantCoface σ c (f * h) =
      σ h * (σ f - f) := by
  rw [sourceGaugeCovariantCoface, map_mul, hh]
  ring

/-- After division by the shifted source section, covariant transgression is exactly ordinary
difference. -/
theorem sourceGaugeCovariantCoface_div_shift [Field K]
    (σ : K →+* K) (c h f : K) (hh : σ h = c * h)
    (hshift : σ h ≠ 0) :
    sourceGaugeCovariantCoface σ c (f * h) / σ h = σ f - f := by
  rw [sourceGaugeCovariantCoface_mul_horizontal σ c h f hh]
  exact mul_div_cancel_left₀ (σ f - f) hshift

/-- A nonzero horizontal source section determines its rank-one connection coefficient uniquely. -/
theorem sourceGaugeCovariantCoface_coefficient_unique [Field K]
    (σ : K →+* K) (c q h : K) (hh : h ≠ 0)
    (hc : sourceGaugeCovariantCoface σ c h = 0)
    (hq : sourceGaugeCovariantCoface σ q h = 0) :
    c = q := by
  rw [sourceGaugeCovariantCoface, sub_eq_zero] at hc hq
  have hmul : c * h = q * h := hc.symm.trans hq
  exact mul_right_cancel₀ hh hmul

/-- Covariant cofaces are natural under ring maps intertwining the source shifts. -/
theorem sourceGaugeCovariantCoface_natural
    [CommRing K] [CommRing L]
    (σ : K →+* K) (τ : L →+* L) (φ : K →+* L)
    (hintertwine : φ.comp σ = τ.comp φ) (c g : K) :
    φ (sourceGaugeCovariantCoface σ c g) =
      sourceGaugeCovariantCoface τ (φ c) (φ g) := by
  rw [sourceGaugeCovariantCoface, sourceGaugeCovariantCoface,
    map_sub, map_mul]
  have h := RingHom.congr_fun hintertwine g
  simpa only [RingHom.comp_apply] using congrArg (fun z => z - φ c * φ g) h

end

end GaloisForLFunctions.HTGeometry
