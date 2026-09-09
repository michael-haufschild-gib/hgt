import GaloisForLFunctions.HTGeometry.FokasLenellsSignedOrigin

/-!
# Concrete compatibility classes for weighted scattering at the origin

The local L^2 criterion is applied mechanically to existing parity
projections, Schwartz derivatives, amplitude rescalings, spatial reflection,
and the corpus's explicit globally small scattering normalization.
-/

open Complex Matrix MeasureTheory Filter Topology Asymptotics Set
open scoped ENNReal NNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The two origin assertions in Propositions 3.8 and 3.9 have exactly the same sharp boundary. -/
theorem signedOriginWeightedReflection_memLp_two_iff_uniform_fifth (q : SchwartzMap ℝ ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ MemLp (signedOriginWeightedReflection q) 2
      (volume.restrict (Ioo (-δ) δ))) ↔
    ((fun κ : ℝ => fun vertical negative : Bool => contourReflectionAmplitude q vertical negative κ)
      =O[atBot] fun κ => (Real.exp κ : ℂ)^5) := by
  rw [signedOriginWeightedReflection_locally_memLp_two_iff,contourReflections_uniform_isBigO_fifth_iff]

/-- General profiles obey the nonlinear balance between their mass and even/odd coupling. -/
theorem signedOriginWeightedReflection_memLp_two_iff_parity_balance (q : SchwartzMap ℝ ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ MemLp (signedOriginWeightedReflection q) 2
      (volume.restrict (Ioo (-δ) δ))) ↔ (∫ x : ℝ, q x) = I*parityCoupling q := by
  rw [signedOriginWeightedReflection_locally_memLp_two_iff,compatibilityMoment_zero_iff_parity_balance]

/-- Odd projection supplies an unconditional family satisfying every local weighted L^p bound. -/
theorem signedOriginWeightedReflection_oddInitialPart_memLp_all (q : SchwartzMap ℝ ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞,
      MemLp (signedOriginWeightedReflection (oddInitialPart q)) p
        (volume.restrict (Ioo (-δ) δ)) :=
  (signedOriginWeightedReflection_locally_memLp_all_iff _).2 (compatibilityMoment_oddInitialPart q)

/-- For even profiles the complete weighted L^2 obstruction reduces to their ordinary mass. -/
theorem signedOriginWeightedReflection_evenInitialPart_memLp_two_iff (q : SchwartzMap ℝ ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ MemLp (signedOriginWeightedReflection (evenInitialPart q)) 2
      (volume.restrict (Ioo (-δ) δ))) ↔ (∫ x : ℝ, q x) = 0 := by
  rw [signedOriginWeightedReflection_locally_memLp_two_iff,compatibilityMoment_evenInitialPart]

/-- Even projections of Schwartz derivatives form another unconditional compatible family. -/
theorem signedOriginWeightedReflection_evenDerivative_memLp_all (q : SchwartzMap ℝ ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ≥0∞,
      MemLp (signedOriginWeightedReflection (evenInitialPart (SchwartzMap.derivCLM ℂ ℂ q))) p
        (volume.restrict (Ioo (-δ) δ)) := by
  apply (signedOriginWeightedReflection_locally_memLp_all_iff _).2
  exact (rawReflection_isBigO_fifth_iff _).1 (rawReflections_evenDerivative_isBigO_fifth q).1

/-- The allowed complex amplitude scales solve one exact quadratic balance. -/
theorem signedOriginWeightedReflection_scaling_memLp_two_iff (q : SchwartzMap ℝ ℂ) (c : ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ MemLp (signedOriginWeightedReflection (c • q)) 2
      (volume.restrict (Ioo (-δ) δ))) ↔
      c = 0 ∨ (∫ x : ℝ, q x) = I*c^2*parityCoupling q := by
  rw [signedOriginWeightedReflection_locally_memLp_two_iff,← rawReflection_isBigO_fifth_iff]
  exact rawReflection_scaling_isBigO_fifth_iff q c

/-- Scaling stability requires separate cancellation of mass and nonlinear parity coupling. -/
theorem signedOriginWeightedReflection_all_scalings_memLp_two_iff (q : SchwartzMap ℝ ℂ) :
    (∀ c : ℂ, ∃ δ : ℝ, 0 < δ ∧ MemLp (signedOriginWeightedReflection (c • q)) 2
      (volume.restrict (Ioo (-δ) δ))) ↔
      ((∫ x : ℝ, q x) = 0 ∧ parityCoupling q = 0) := by
  simp only [signedOriginWeightedReflection_locally_memLp_two_iff,← rawReflection_isBigO_fifth_iff]
  exact rawReflection_all_scalings_isBigO_fifth_iff q

/-- Requiring the property for both spatial orientations detects the same stronger pair of cancellations. -/
theorem signedOriginWeightedReflection_both_reflections_memLp_two_iff (q : SchwartzMap ℝ ℂ) :
    ((∃ δ : ℝ, 0 < δ ∧ MemLp (signedOriginWeightedReflection q) 2
      (volume.restrict (Ioo (-δ) δ))) ∧
     (∃ δ : ℝ, 0 < δ ∧ MemLp (signedOriginWeightedReflection (RHTower.negSchwartz' q)) 2
      (volume.restrict (Ioo (-δ) δ)))) ↔
      ((∫ x : ℝ, q x) = 0 ∧ parityCoupling q = 0) := by
  rw [signedOriginWeightedReflection_locally_memLp_two_iff,
    signedOriginWeightedReflection_locally_memLp_two_iff,compatibilityMoment_both_zero_iff]

/-- The actual global smallness normalization does not automatically remove the compatibility pole. -/
theorem signedOriginWeightedReflection_globalSmall_memLp_two_iff (q : SchwartzMap ℝ ℂ) :
    (∃ δ : ℝ, 0 < δ ∧ MemLp (signedOriginWeightedReflection (globalSmallScatteringPotential q)) 2
      (volume.restrict (Ioo (-δ) δ))) ↔
      (∫ x : ℝ, q x) = I*(globalScatteringScale q : ℂ)^2*parityCoupling q := by
  rw [signedOriginWeightedReflection_locally_memLp_two_iff,← rawReflection_isBigO_fifth_iff]
  exact rawReflection_globalSmall_isBigO_fifth_iff q

/-- Simultaneous compatibility before and after normalization has a complete moment classification. -/
theorem signedOriginWeightedReflection_and_globalSmall_memLp_two_iff (q : SchwartzMap ℝ ℂ) :
    ((∃ δ : ℝ, 0 < δ ∧ MemLp (signedOriginWeightedReflection q) 2
      (volume.restrict (Ioo (-δ) δ))) ∧
     (∃ δ : ℝ, 0 < δ ∧ MemLp (signedOriginWeightedReflection (globalSmallScatteringPotential q)) 2
      (volume.restrict (Ioo (-δ) δ)))) ↔
      ((∫ x : ℝ, q x) = 0 ∧ parityCoupling q = 0) := by
  simp only [signedOriginWeightedReflection_locally_memLp_two_iff,← rawReflection_isBigO_fifth_iff]
  exact rawReflection_and_globalSmall_isBigO_fifth_iff q

end
end GaloisForLFunctions.HTGeometry.FokasLenells
