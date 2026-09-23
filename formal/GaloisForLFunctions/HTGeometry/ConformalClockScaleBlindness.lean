import GaloisForLFunctions.HTGeometry.ConformalClockTwoSpeciesScaleLaw

/-!
# Scale blindness: the exact boundary of two-species conformal reconstruction

The two-species scale law recovers `e^{2σ}` from the difference of two effective clock potentials.
Two hypotheses carry it — distinct calibrated squared masses, and one conjugation weight shared by
both species — and this file proves both sharp.

* **Distinct masses are necessary.** A single species, or two species with equal calibrated masses,
  determines only the combination `μ e^{2σ} - D_σ`. Explicit distinct pairs `(scale, defect)` give
  the same potential, so the conformal scale is invisible. This is the exact content of the audit
  lines about conformally coupled massless scalars and about mass renormalization.
* **A shared conjugation weight is necessary.** If the two species are conjugated with different
  weights, the geometric defect no longer cancels: the potential difference is a pure scale term
  for all geometric data precisely when the two weights agree.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Effective clock potential as a function of its independent algebraic channels: conjugation
weight, calibrated squared mass, conformal scale, and the two geometric defect channels. -/
def conformalPotentialData (weight massSq scale defectLaplace defectGradient : ℝ) : ℝ :=
  massSq * scale - weight * defectLaplace - weight ^ (2 : ℕ) * defectGradient

/-- The chart potential is the algebraic potential evaluated on its geometric channels. -/
theorem SmoothMetricChart.conformalPotential_eq_data {d : ℕ} (M : SmoothMetricChart d)
    (weight massSq : ℝ) (sigma : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    M.conformalPotential weight massSq sigma x =
      conformalPotentialData weight massSq (Real.exp (2 * sigma x))
        (M.dalembert sigma x) (M.gradPair sigma sigma x) := by
  simp only [SmoothMetricChart.conformalPotential, SmoothMetricChart.conformalDefect,
    conformalPotentialData]
  ring

/-! ## Distinct masses are necessary -/

/-- With a shared conjugation weight the potential difference is the pure scale term of the
two-species law. -/
theorem conformalPotentialData_difference (weight massSq₁ massSq₂ scale defectLaplace
    defectGradient : ℝ) :
    conformalPotentialData weight massSq₁ scale defectLaplace defectGradient -
        conformalPotentialData weight massSq₂ scale defectLaplace defectGradient =
      (massSq₁ - massSq₂) * scale := by
  simp only [conformalPotentialData]
  ring

/-- **Equal calibrated masses are scale blind.** The two-species difference vanishes identically,
whatever the conformal scale. -/
theorem conformalPotentialData_difference_eq_zero_of_eq_mass (weight massSq scale defectLaplace
    defectGradient : ℝ) :
    conformalPotentialData weight massSq scale defectLaplace defectGradient -
        conformalPotentialData weight massSq scale defectLaplace defectGradient = 0 := by
  simp

/-- **One species cannot separate scale from the geometric defect.** For every weight and mass
there are two distinct scale/defect states with the same effective potential, so a single
calibrated species determines neither. -/
theorem exists_ne_scaleDefect_with_eq_conformalPotentialData (weight massSq defectGradient : ℝ) :
    ∃ scale₁ defectLaplace₁ scale₂ defectLaplace₂ : ℝ,
      (scale₁, defectLaplace₁) ≠ (scale₂, defectLaplace₂) ∧
        conformalPotentialData weight massSq scale₁ defectLaplace₁ defectGradient =
          conformalPotentialData weight massSq scale₂ defectLaplace₂ defectGradient := by
  by_cases hw : weight = 0
  · refine ⟨0, 0, 0, 1, ?_, ?_⟩
    · intro hEq
      exact zero_ne_one (congrArg Prod.snd hEq)
    · simp [conformalPotentialData, hw]
  · refine ⟨0, 0, weight, massSq, ?_, ?_⟩
    · intro hEq
      exact hw (congrArg Prod.fst hEq).symm
    · simp only [conformalPotentialData]
      ring

/-- **Two species with equal masses are exactly as blind as one.** Their potentials coincide, so
the pair carries no information beyond a single channel. -/
theorem conformalPotentialData_eq_of_eq_mass (weight scale defectLaplace
    defectGradient : ℝ) {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ = massSq₂) :
    conformalPotentialData weight massSq₁ scale defectLaplace defectGradient =
      conformalPotentialData weight massSq₂ scale defectLaplace defectGradient := by
  rw [hmass]

/-! ## A shared conjugation weight is necessary -/

/-- Potential difference when the two species are conjugated with different weights. -/
theorem conformalPotentialData_difference_of_weights (weight₁ weight₂ massSq₁ massSq₂ scale
    defectLaplace defectGradient : ℝ) :
    conformalPotentialData weight₁ massSq₁ scale defectLaplace defectGradient -
        conformalPotentialData weight₂ massSq₂ scale defectLaplace defectGradient =
      (massSq₁ - massSq₂) * scale - (weight₁ - weight₂) * defectLaplace -
        (weight₁ ^ (2 : ℕ) - weight₂ ^ (2 : ℕ)) * defectGradient := by
  simp only [conformalPotentialData]
  ring

/-- **The geometric defect cancels exactly when the two species share a conjugation weight.**

If the reporter normalization differs between species, the difference of effective potentials
retains the geometric defect and is no longer a scale datum. -/
theorem conformalPotentialData_difference_pure_iff_weight_eq (weight₁ weight₂ massSq₁ massSq₂
    scale : ℝ) :
    (∀ defectLaplace defectGradient : ℝ,
        conformalPotentialData weight₁ massSq₁ scale defectLaplace defectGradient -
            conformalPotentialData weight₂ massSq₂ scale defectLaplace defectGradient =
          (massSq₁ - massSq₂) * scale) ↔
      weight₁ = weight₂ := by
  constructor
  · intro hpure
    have h := hpure 1 0
    rw [conformalPotentialData_difference_of_weights] at h
    have hzero : weight₁ - weight₂ = 0 := by linarith
    linarith [sub_eq_zero.mp hzero]
  · intro hw defectLaplace defectGradient
    rw [hw]
    exact conformalPotentialData_difference weight₂ massSq₁ massSq₂ scale defectLaplace
      defectGradient

/-- **Different conjugation weights really do destroy the scale channel.** -/
theorem exists_conformalPotentialData_difference_ne_scale :
    ∃ weight₁ weight₂ massSq₁ massSq₂ scale defectLaplace defectGradient : ℝ,
      weight₁ ≠ weight₂ ∧
        conformalPotentialData weight₁ massSq₁ scale defectLaplace defectGradient -
            conformalPotentialData weight₂ massSq₂ scale defectLaplace defectGradient ≠
          (massSq₁ - massSq₂) * scale := by
  refine ⟨0, 1, 0, 0, 0, 1, 0, by norm_num, ?_⟩
  simp [conformalPotentialData]

end GaloisForLFunctions.HTGeometry
