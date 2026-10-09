import GaloisForLFunctions.HTGeometry.ConformalClockScaleBlindness

/-!
# Exact scale information in a single conformal clock channel

The algebraic channel is `m * s - w * L - w² * G`. With the gradient channel fixed,
nonzero weight lets the Laplace channel compensate every prescribed scale and
data value. At zero weight, nonzero mass determines scale exactly. This separates
failure to identify the full channel pair from failure to identify scale alone.

The classification concerns independent algebraic channels. It does not assume
that arbitrary channel assignments are derivatives of an actual conformal factor.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The exact data fiber at a prescribed scale, allowing the Laplace channel to vary. -/
theorem conformalPotentialData_laplace_fiber_iff
    (weight massSq scale defectGradient value : ℝ) :
    (∃ defectLaplace : ℝ,
      conformalPotentialData weight massSq scale defectLaplace defectGradient = value) ↔
      weight ≠ 0 ∨ massSq * scale = value := by
  by_cases hw : weight = 0
  · simp [conformalPotentialData, hw]
  · constructor
    · intro _
      exact Or.inl hw
    · intro _
      refine ⟨(massSq * scale - weight ^ 2 * defectGradient - value) / weight, ?_⟩
      have hcancel := div_mul_cancel₀
        (massSq * scale - weight ^ 2 * defectGradient - value) hw
      dsimp [conformalPotentialData]
      nlinarith [hcancel]

/-- One species identifies scale exactly at zero weight and nonzero mass, even
though the full scale/defect pair is never identifiable. -/
theorem conformalPotentialData_scale_identifiable_iff
    (weight massSq defectGradient : ℝ) :
    (∀ scale₁ defectLaplace₁ scale₂ defectLaplace₂ : ℝ,
      conformalPotentialData weight massSq scale₁ defectLaplace₁ defectGradient =
        conformalPotentialData weight massSq scale₂ defectLaplace₂ defectGradient →
      scale₁ = scale₂) ↔ weight = 0 ∧ massSq ≠ 0 := by
  constructor
  · intro h
    have hw : weight = 0 := by
      have hscale := h 0 0 weight massSq (by simp only [conformalPotentialData]; ring)
      exact hscale.symm
    refine ⟨hw, ?_⟩
    intro hm
    have hscale := h 0 0 1 0 (by simp [conformalPotentialData, hw, hm])
    exact zero_ne_one hscale
  · rintro ⟨hw, hm⟩ scale₁ defectLaplace₁ scale₂ defectLaplace₂ h
    simpa [conformalPotentialData, hw, hm] using h

/-- Requiring positive scales does not remove ambiguity: its exact parameter
boundary is still nonzero weight or zero mass. -/
theorem conformalPotentialData_positive_scale_ambiguity_iff
    (weight massSq defectGradient : ℝ) :
    (∃ scale₁ defectLaplace₁ scale₂ defectLaplace₂ : ℝ,
      0 < scale₁ ∧ 0 < scale₂ ∧ scale₁ ≠ scale₂ ∧
      conformalPotentialData weight massSq scale₁ defectLaplace₁ defectGradient =
        conformalPotentialData weight massSq scale₂ defectLaplace₂ defectGradient) ↔
      weight ≠ 0 ∨ massSq = 0 := by
  constructor
  · rintro ⟨scale₁, defectLaplace₁, scale₂, defectLaplace₂, _, _, hne, hdata⟩
    by_cases hw : weight = 0
    · right
      by_contra hm
      exact hne ((conformalPotentialData_scale_identifiable_iff weight massSq defectGradient).mpr
        ⟨hw, hm⟩ scale₁ defectLaplace₁ scale₂ defectLaplace₂ hdata)
    · exact Or.inl hw
  · intro h
    have hrealize : ∀ scale : ℝ, ∃ defectLaplace : ℝ,
        conformalPotentialData weight massSq scale defectLaplace defectGradient = 0 := by
      intro scale
      apply (conformalPotentialData_laplace_fiber_iff weight massSq scale defectGradient 0).mpr
      rcases h with hw | hm
      · exact Or.inl hw
      · exact Or.inr (by rw [hm, zero_mul])
    obtain ⟨L₁, h₁⟩ := hrealize 1
    obtain ⟨L₂, h₂⟩ := hrealize 2
    exact ⟨1, L₁, 2, L₂, by positivity, by positivity, by linarith, h₁.trans h₂.symm⟩

end GaloisForLFunctions.HTGeometry
