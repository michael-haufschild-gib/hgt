import GaloisForLFunctions.HTGeometry.ConformalMetricClockCalculus

/-!
# Two-species conformal clock scale law for a smooth metric

For a smooth nondegenerate metric field `g` in a coordinate chart, a conformal factor `e^{2σ}` and
the conjugation weight `a = (d-2)/2`, the conjugated Klein–Gordon operator of a clock species of
calibrated squared mass `μ` is

`e^{(a+2)σ} (□_{e^{2σ}g} + μ) e^{-aσ} = □_g + V_μ^σ`,
`V_μ^σ = μ e^{2σ} - a □_g σ - a² Γ_g(σ,σ)`.

Two species with distinct calibrated squared masses reconstruct the conformal scale pointwise and
algebraically:

`e^{2σ} = (V_{μ₁}^σ - V_{μ₂}^σ) / (μ₁ - μ₂)`,

and jointly determine both the scale and the species-independent geometric defect
`D_σ = a □_g σ + a² Γ_g(σ,σ)`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ContDiff

namespace SmoothMetricChart

variable {d : ℕ} (M : SmoothMetricChart d)

/-- Species-independent geometric defect `D_σ = a □σ + a² Γ(σ,σ)` of a conformal factor. -/
noncomputable def conformalDefect (a : ℝ) (sigma : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  a * M.dalembert sigma x + a ^ 2 * M.gradPair sigma sigma x

/-- Effective zeroth-order potential `V_μ^σ = μ e^{2σ} - D_σ` of a clock species. -/
noncomputable def conformalPotential (a massSq : ℝ) (sigma : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  massSq * Real.exp (2 * sigma x) - M.conformalDefect a sigma x

/-- **Exact conformal conjugation of the clock Klein–Gordon operator.**

Conjugating the d'Alembertian of the conformally rescaled chart by `e^{-aσ}` and multiplying by
`e^{(a+2)σ}` restores the original d'Alembertian plus the scalar potential `V_μ^σ`. -/
theorem conformalKleinGordon_conjugation
    {sigma u : (Fin d → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma) (hu : ContDiff ℝ ∞ u)
    (massSq : ℝ) (x : Fin d → ℝ) :
    Real.exp ((ExponentialSecondOrderClockCalculus.conformalDimensionWeight d + 2) * sigma x) *
        ((M.conformalRescale sigma hsigma).dalembert
            (fun y => Real.exp
              (-ExponentialSecondOrderClockCalculus.conformalDimensionWeight d * sigma y) * u y)
            x +
          massSq * (Real.exp
            (-ExponentialSecondOrderClockCalculus.conformalDimensionWeight d * sigma x) * u x)) =
      M.dalembert u x +
        M.conformalPotential
          (ExponentialSecondOrderClockCalculus.conformalDimensionWeight d) massSq sigma x * u x := by
  have habs := M.expClockCalculus.conformalKleinGordonSigma_conjugation
    (ExponentialSecondOrderClockCalculus.conformalDimensionWeight d) massSq
    (⟨sigma, hsigma⟩ : ↥(smoothScalarAlgebra d)) (⟨u, hu⟩ : ↥(smoothScalarAlgebra d))
  have hx := congrFun (congrArg Subtype.val habs) x
  simp only [smoothScalarAlgebra_coe_mul, smoothScalarAlgebra_coe_add,
    smoothScalarAlgebra_coe_sub, smoothScalarAlgebra_coe_smul, Pi.mul_apply, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hx
  rw [M.conformalWaveSigma_eq_dalembert_conformalRescale] at hx
  simp only [expClockCalculus_expSmul, expClockCalculus_toSecondOrder,
    secondOrderCalculus_laplacian, secondOrderCalculus_gamma, clockLaplacian_coe,
    clockGamma_coe, smoothExpSmul_coe, smoothScalarAlgebra_coe_mul] at hx
  have hRHS : M.dalembert u x +
      M.conformalPotential
        (ExponentialSecondOrderClockCalculus.conformalDimensionWeight d) massSq sigma x * u x =
      M.dalembert u x +
        (massSq * Real.exp (2 * sigma x) +
            -ExponentialSecondOrderClockCalculus.conformalDimensionWeight d *
              M.dalembert sigma x -
          ExponentialSecondOrderClockCalculus.conformalDimensionWeight d ^ 2 *
            M.gradPair sigma sigma x) * u x := by
    simp only [conformalPotential, conformalDefect]
    ring
  rw [hRHS]
  exact hx

/-- Literal `d ≥ 3` form of the conformal clock conjugation law. -/
theorem conformalKleinGordon_dimension_conjugation
    (_hd : 3 ≤ d) {sigma u : (Fin d → ℝ) → ℝ}
    (hsigma : ContDiff ℝ ∞ sigma) (hu : ContDiff ℝ ∞ u)
    (massSq : ℝ) (x : Fin d → ℝ) :
    Real.exp ((((d : ℝ) - 2) / 2 + 2) * sigma x) *
        ((M.conformalRescale sigma hsigma).dalembert
            (fun y => Real.exp (-(((d : ℝ) - 2) / 2) * sigma y) * u y) x +
          massSq * (Real.exp (-(((d : ℝ) - 2) / 2) * sigma x) * u x)) =
      M.dalembert u x + M.conformalPotential (((d : ℝ) - 2) / 2) massSq sigma x * u x :=
  M.conformalKleinGordon_conjugation hsigma hu massSq x

/-- **Two clock species cancel the shared geometric defect.** -/
theorem conformalPotential_difference (a massSq₁ massSq₂ : ℝ)
    (sigma : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    M.conformalPotential a massSq₁ sigma x - M.conformalPotential a massSq₂ sigma x =
      (massSq₁ - massSq₂) * Real.exp (2 * sigma x) := by
  simp only [conformalPotential]
  ring

/-- **Two-species conformal scale reconstruction.**

Distinct calibrated squared masses determine `e^{2σ}` pointwise and algebraically. -/
theorem conformalScale_reconstruction (a massSq₁ massSq₂ : ℝ) (hmass : massSq₁ ≠ massSq₂)
    (sigma : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    Real.exp (2 * sigma x) =
      (M.conformalPotential a massSq₁ sigma x - M.conformalPotential a massSq₂ sigma x) /
        (massSq₁ - massSq₂) := by
  rw [M.conformalPotential_difference a massSq₁ massSq₂ sigma x]
  field_simp [sub_ne_zero.mpr hmass]

/-- The shared geometric defect is recovered from a single potential together with the scale. -/
theorem conformalDefect_reconstruction (a massSq : ℝ) (sigma : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) :
    M.conformalDefect a sigma x =
      massSq * Real.exp (2 * sigma x) - M.conformalPotential a massSq sigma x := by
  simp only [conformalPotential]
  ring

/-- **Joint identifiability of conformal scale and geometric defect.**

The pair of effective potentials of two distinct clock species determines both the conformal scale
and the species-independent geometric defect. -/
theorem conformalPotentialPair_injective (massSq₁ massSq₂ : ℝ) (hmass : massSq₁ ≠ massSq₂)
    {scale₁ defect₁ scale₂ defect₂ : ℝ}
    (h₁ : massSq₁ * scale₁ - defect₁ = massSq₁ * scale₂ - defect₂)
    (h₂ : massSq₂ * scale₁ - defect₁ = massSq₂ * scale₂ - defect₂) :
    scale₁ = scale₂ ∧ defect₁ = defect₂ := by
  have hdiff : (massSq₁ - massSq₂) * (scale₁ - scale₂) = 0 := by linarith
  have hscale : scale₁ = scale₂ := by
    rcases mul_eq_zero.mp hdiff with h | h
    · exact absurd (sub_eq_zero.mp h) hmass
    · exact sub_eq_zero.mp h
  refine ⟨hscale, ?_⟩
  rw [hscale] at h₁
  linarith

end SmoothMetricChart

namespace SmoothPseudoMetric

variable {d : ℕ} (g : SmoothPseudoMetric d)

/-- **Conformal clock conjugation for a literally rescaled smooth metric field.**

For `g̃ = e^{2σ} g` and `a = (d-2)/2`, the conjugated Klein–Gordon operator of a clock species of
calibrated squared mass `μ` equals `□_g` plus the scalar potential
`μ e^{2σ} - a □_g σ - a² Γ_g(σ,σ)`. -/
theorem conformalKleinGordon_conjugation
    {sigma u : (Fin d → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma) (hu : ContDiff ℝ ∞ u)
    (massSq : ℝ) (x : Fin d → ℝ) :
    Real.exp ((ExponentialSecondOrderClockCalculus.conformalDimensionWeight d + 2) * sigma x) *
        ((g.conformal sigma hsigma).chart.dalembert
            (fun y => Real.exp
              (-ExponentialSecondOrderClockCalculus.conformalDimensionWeight d * sigma y) * u y)
            x +
          massSq * (Real.exp
            (-ExponentialSecondOrderClockCalculus.conformalDimensionWeight d * sigma x) * u x)) =
      g.chart.dalembert u x +
        g.chart.conformalPotential
          (ExponentialSecondOrderClockCalculus.conformalDimensionWeight d) massSq sigma x *
          u x := by
  rw [g.chart_conformal sigma hsigma]
  exact g.chart.conformalKleinGordon_conjugation hsigma hu massSq x

/-- **Two-species conformal scale reconstruction for a smooth metric field.** -/
theorem conformalScale_reconstruction (massSq₁ massSq₂ : ℝ) (hmass : massSq₁ ≠ massSq₂)
    (sigma : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    Real.exp (2 * sigma x) =
      (g.chart.conformalPotential
          (ExponentialSecondOrderClockCalculus.conformalDimensionWeight d) massSq₁ sigma x -
        g.chart.conformalPotential
          (ExponentialSecondOrderClockCalculus.conformalDimensionWeight d) massSq₂ sigma x) /
        (massSq₁ - massSq₂) :=
  g.chart.conformalScale_reconstruction _ massSq₁ massSq₂ hmass sigma x

end SmoothPseudoMetric

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ContDiff

theorem conformalDimensionWeight_four :
    ExponentialSecondOrderClockCalculus.conformalDimensionWeight 4 = 1 := by
  rw [ExponentialSecondOrderClockCalculus.conformalDimensionWeight]
  norm_num

namespace SmoothMetricChart

/-- Four-dimensional form of the effective clock potential:
`V_μ^σ = μ e^{2σ} - □σ - Γ(σ,σ)`. -/
theorem conformalPotential_four (M : SmoothMetricChart 4) (massSq : ℝ)
    (sigma : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) :
    M.conformalPotential 1 massSq sigma x =
      massSq * Real.exp (2 * sigma x) - M.dalembert sigma x - M.gradPair sigma sigma x := by
  simp only [conformalPotential, conformalDefect]
  ring

end SmoothMetricChart

namespace SmoothPseudoMetric

/-- **Four-dimensional conformal clock conjugation for a smooth metric field.**

At `d = 4` the conjugation weight is `a = 1`, so
`e^{3σ}(□_{e^{2σ}g} + μ)e^{-σ} = □_g + μ e^{2σ} - □_g σ - Γ_g(σ,σ)`. -/
theorem conformalKleinGordon_four (g : SmoothPseudoMetric 4)
    {sigma u : (Fin 4 → ℝ) → ℝ} (hsigma : ContDiff ℝ ∞ sigma) (hu : ContDiff ℝ ∞ u)
    (massSq : ℝ) (x : Fin 4 → ℝ) :
    Real.exp (3 * sigma x) *
        ((g.conformal sigma hsigma).chart.dalembert
            (fun y => Real.exp (-1 * sigma y) * u y) x +
          massSq * (Real.exp (-1 * sigma x) * u x)) =
      g.chart.dalembert u x +
        (massSq * Real.exp (2 * sigma x) - g.chart.dalembert sigma x -
          g.chart.gradPair sigma sigma x) * u x := by
  have hgen := g.conformalKleinGordon_conjugation hsigma hu massSq x
  rw [conformalDimensionWeight_four] at hgen
  rw [g.chart.conformalPotential_four massSq sigma x] at hgen
  norm_num at hgen ⊢
  exact hgen

end SmoothPseudoMetric

end GaloisForLFunctions.HTGeometry
