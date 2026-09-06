import GaloisForLFunctions.HilbertMetric.FivePointFiniteDifferenceCusp
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedEighthHankelClosure

/-!
# Unconditional five-point cusp of the literal center-mixed theta source

At every critical aperture, the actual five-node equispaced Gram matrix is positive definite
throughout a punctured neighborhood of coalescence. Every jet sign is supplied by the proved
source and mixture theorems, and the existing eighth-order regularity suffices.
-/

open Filter Topology Set
namespace RHTower
noncomputable section

/-- Actual center-mixed theta Gram matrix on `0,h,2h,3h,4h`. -/
def thetaCuspCenterMixedGramFiveEquispaced (a h : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  HilbertMetric.fivePointSampleMatrix (thetaCuspCenterMixedDensity a) h

/-- No unproved source-sign or regularity premise remains in the five-point cusp. -/
theorem eventually_thetaCuspCenterMixedGramFiveEquispaced_posDef
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    ∀ᶠ h in 𝓝[≠] 0, (thetaCuspCenterMixedGramFiveEquispaced a h).PosDef := by
  let f := thetaCuspCenterMixedDensity a
  have hf : ContDiff ℝ 8 f := contDiff_eight_thetaCuspCenterMixedDensity ha0.le ha
  have heven : Function.Even f := thetaCuspCenterMixedDensity_even a
  have hodd (n : ℕ) (hn : Odd n) : iteratedDeriv n f 0 = 0 :=
    iteratedDeriv_zero_of_even_real_of_odd heven hn
  have h2 : iteratedDeriv 2 f 0 < 0 := by
    rw [iteratedDeriv_two_thetaCuspCenterMixedDensity ha0.le ha]
    exact thetaCuspCenterMixedDensitySecondJet_zero_neg ha0 ha
  have h4 : 0 < f 0*iteratedDeriv 4 f 0-(iteratedDeriv 2 f 0)^2 := by
    rw [iteratedDeriv_four_thetaCuspCenterMixedDensity ha0.le ha,
      iteratedDeriv_two_thetaCuspCenterMixedDensity ha0.le ha]
    exact thetaCuspCenterMixedDensity_fourthHankel_pos ha0 ha
  exact HilbertMetric.eventually_fivePointSampleMatrix_posDef hf
    (hodd 1 (by norm_num)) (hodd 3 (by norm_num))
    (hodd 5 (by norm_num)) (hodd 7 (by norm_num))
    (thetaCuspCenterMixedDensity_pos ha0 ha 0) h2 h4
    (thetaCuspCenterMixedDensity_iteratedDeriv_secondSixthHankel_pos ha0 ha)
    (thetaCuspCenterMixedDensity_iteratedDeriv_eighthHankel_pos ha0 ha)

/-- The physical five-point matrix is strictly positive throughout one punctured neighborhood. -/
theorem exists_thetaCuspCenterMixedGramFiveEquispaced_posDef_punctured
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ →
      (thetaCuspCenterMixedGramFiveEquispaced a h).PosDef := by
  have hev := eventually_thetaCuspCenterMixedGramFiveEquispaced_posDef ha0 ha
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨δ, hδ, fun h hh hsmall => hball ?_⟩
  exact ⟨by simpa [Metric.mem_ball, Real.dist_eq] using hsmall, by simpa using hh⟩

/-- In particular, every sufficiently small positive spacing gives a strict five-node Gram form. -/
theorem exists_thetaCuspCenterMixedGramFiveEquispaced_posDef_right
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      (thetaCuspCenterMixedGramFiveEquispaced a h).PosDef := by
  obtain ⟨δ, hδ, hpos⟩ := exists_thetaCuspCenterMixedGramFiveEquispaced_posDef_punctured ha0 ha
  exact ⟨δ, hδ, fun h hh hsmall => hpos h hh.ne' (by simpa [abs_of_pos hh] using hsmall)⟩

end
end RHTower
