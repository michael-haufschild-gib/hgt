import GaloisForLFunctions.HTGeometry.FokasLenellsSignedOrigin

/-!
# Both weighted original reflection channels on one origin window

The exact nonlocal reverse-channel symmetry makes the two-channel norm
identical to the forward-channel norm. Consequently both conclusions in
Proposition 3.9 have one common sharp compatibility criterion.
-/

open Complex Matrix MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def signedOriginWeightedChannels (q : SchwartzMap ℝ ℂ) (z : ℝ) : ℂ × ℂ :=
  (signedOriginWeightedReflection q z,-signedOriginWeightedReflection q z)

/-- The two components are the actual forward and reverse weighted scattering amplitudes. -/
theorem signedOriginWeightedChannels_eq_contour (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) (κ : ℝ) :
    signedOriginWeightedChannels q (contourSquaredParameter vertical κ) =
      (contourReflectionAmplitude q vertical negative κ/(contourParameter vertical negative κ)^(5 : ℕ),
       contourReverseReflectionAmplitude q vertical negative κ/(contourParameter vertical negative κ)^(5 : ℕ)) := by
  rw [signedOriginWeightedChannels,signedOriginWeightedReflection_eq_contour,
    contourReverseReflectionAmplitude_eq_neg,neg_div]

@[simp] theorem signedOriginWeightedChannels_norm (q : SchwartzMap ℝ ℂ) (z : ℝ) :
    ‖signedOriginWeightedChannels q z‖ = ‖signedOriginWeightedReflection q z‖ := by
  simp [signedOriginWeightedChannels,Prod.norm_def]

theorem signedOriginWeightedChannels_measurable (q : SchwartzMap ℝ ℂ) :
    Measurable (signedOriginWeightedChannels q) :=
  (signedOriginWeightedReflection_measurable q).prodMk
    (signedOriginWeightedReflection_measurable q).neg

/-- Every L^p seminorm sees precisely the same integrability for the paired and forward channels. -/
theorem signedOriginWeightedChannels_memLp_iff (q : SchwartzMap ℝ ℂ)
    (p : ℝ≥0∞) (μ : Measure ℝ) :
    MemLp (signedOriginWeightedChannels q) p μ ↔ MemLp (signedOriginWeightedReflection q) p μ := by
  apply memLp_congr_norm (signedOriginWeightedChannels_measurable q).aestronglyMeasurable
    (signedOriginWeightedReflection_measurable q).aestronglyMeasurable
  exact Filter.Eventually.of_forall (signedOriginWeightedChannels_norm q)

/-- Both actual weighted channels lie in L^(2 : ℕ) on one symmetric window exactly when the moment vanishes. -/
theorem signedOriginWeightedChannels_locally_memLp_two_iff (q : SchwartzMap ℝ ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ MemLp (signedOriginWeightedChannels q) 2
      (volume.restrict (Ioo (-δ) δ))) ↔ compatibilityMoment q = 0 := by
  simp only [signedOriginWeightedChannels_memLp_iff]
  exact signedOriginWeightedReflection_locally_memLp_two_iff q

/-- Compatibility controls all exponents and both channels simultaneously on one common interval. -/
theorem signedOriginWeightedChannels_locally_memLp_all_iff (q : SchwartzMap ℝ ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞, MemLp (signedOriginWeightedChannels q) p
      (volume.restrict (Ioo (-δ) δ))) ↔ compatibilityMoment q = 0 := by
  simp only [signedOriginWeightedChannels_memLp_iff]
  exact signedOriginWeightedReflection_locally_memLp_all_iff q

/-- The explicitly small Gaussian obstructs the paired assertion on every origin window. -/
theorem signedOriginWeightedChannels_globalSmallGaussian_not_memLp_two (a r : ℝ) :
    ¬ MemLp (signedOriginWeightedChannels (globalSmallScatteringPotential (compatibilityGaussian a))) 2
      (volume.restrict (Ioo (-(Real.exp r)) (Real.exp r))) := by
  rw [signedOriginWeightedChannels_memLp_iff]
  exact signedOriginWeightedReflection_globalSmallGaussian_not_memLp_two a r

end
end GaloisForLFunctions.HTGeometry.FokasLenells
