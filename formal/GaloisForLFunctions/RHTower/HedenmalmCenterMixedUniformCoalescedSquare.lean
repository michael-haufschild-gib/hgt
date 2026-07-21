import GaloisForLFunctions.HilbertMetric.UniformCoalescedThreePointSquare
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedRaywiseCoalescedCone

/-!
# Unconditional uniform coalesced square for the center-mixed theta density

The source fourth Hankel sign controls all three mixed sixth jets at the doubly coalesced
three-node corner.  Consequently one radius works simultaneously for both positive adjacent
gaps, including aspect ratios tending to either coordinate axis.
-/

namespace RHTower

noncomputable section

/-- **Uniform coalesced square.**  At every critical aperture, the actual center-mixed theta
three-point matrix is positive definite throughout one full positive square at the coalesced
corner. -/
theorem exists_thetaCuspCenterMixed_uniformCoalescedSquare_posDef
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ x y : ℝ,
      0 < x → x < delta → 0 < y → y < delta →
        Matrix.PosDef (thetaCuspCenterMixedThreePointMatrix a x y) := by
  let f := thetaCuspCenterMixedDensity a
  let f₁ := thetaCuspCenterMixedDensityFirstJet a
  let f₂ := thetaCuspCenterMixedDensitySecondJet a
  let f₃ := thetaCuspCenterMixedDensityThirdJet a
  let f₄ := thetaCuspCenterMixedDensityFourthJet a
  let f₅ := thetaCuspCenterMixedDensityFifthJet a
  let f₆ := thetaCuspCenterMixedDensitySixthJet a
  rcases HilbertMetric.exists_threePointCorrelationDeterminantPath_pos_uniform_square
      (f := f) (f₁ := f₁) (f₂ := f₂) (f₃ := f₃) (f₄ := f₄) (f₅ := f₅) (f₆ := f₆)
      (fun t => hasDerivAt_thetaCuspCenterMixedDensity ha0.le ha t)
      (fun t => hasDerivAt_thetaCuspCenterMixedDensityFirstJet ha0.le ha t)
      (fun t => hasDerivAt_thetaCuspCenterMixedDensitySecondJet ha0.le ha t)
      (fun t => hasDerivAt_thetaCuspCenterMixedDensityThirdJet ha0.le ha t)
      (fun t => hasDerivAt_thetaCuspCenterMixedDensityFourthJet ha0.le ha t)
      (fun t => hasDerivAt_thetaCuspCenterMixedDensityFifthJet ha0.le ha t)
      (continuous_thetaCuspCenterMixedDensitySixthJet ha0.le ha)
      (thetaCuspCenterMixedDensityFirstJet_zero ha0.le ha)
      (thetaCuspCenterMixedDensityThirdJet_zero a)
      (thetaCuspCenterMixedDensitySecondJet_zero_neg ha0 ha)
      (thetaCuspCenterMixedDensity_fourthHankel_pos ha0 ha) with
    ⟨delta, hdelta, hdet⟩
  refine ⟨delta, hdelta, fun x y hx hxδ hy hyδ => ?_⟩
  have hdetpos :
      0 < HilbertMetric.threePointCorrelationDeterminant
        (f 0) (f x) (f y) (f (x + y)) := by
    simpa [HilbertMetric.threePointCorrelationDeterminantPath] using
      hdet x y hx hxδ hy hyδ
  have hposdef := (HilbertMetric.threePointCorrelationMatrix_posDef_iff
    (thetaCuspCenterMixedDensity_pos ha0 ha 0)
    (thetaCuspCenterMixedDensity_pos ha0 ha x).le
    (thetaCuspCenterMixedDensity_lt_zero ha0 ha hx)).2 hdetpos
  simpa [thetaCuspCenterMixedThreePointMatrix, f] using hposdef

end

end RHTower
