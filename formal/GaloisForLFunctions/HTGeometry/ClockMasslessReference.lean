import GaloisForLFunctions.HTGeometry.ClockTwoSpeciesFoliation

/-!
# The massless species is free, so one species carries the whole inverse step

The effective potential of a clock species of squared mass `μ` is `V_μ^σ = μ e^{2σ} - D_σ` with
`D_σ = a□σ + a²Γ(σ,σ)`. At `μ = 0` the defect is all that is left, and it is exactly a Riccati
potential:

`D_σ = □(aσ) + Γ(aσ, aσ)`,  so  `V_0^σ = -(□(aσ) + Γ(aσ,aσ))`.

Hence `e^{aσ}` is a globally nonvanishing probe of the massless species on **any** chart and for
**any** smooth conformal factor — it is the conjugate of the constant solution of the massless wave
equation. The massless potential, and with it the shared geometric defect, is therefore determined
outright, with no hypothesis at all.

Consequently the two-species law needs only one genuinely massive species: taking the massless one
as reference, `e^{2σ} = (V_μ^σ - V_0^σ)/μ`. The whole remaining content of the inverse step is a
probe family for a single massive species.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

variable {d : ℕ}

/-! ## Scalar multiples in the carré du champ -/

theorem gradPair_const_mul (M : SmoothMetricChart d) (x : Fin d → ℝ)
    {f h : (Fin d → ℝ) → ℝ} (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x)
    (c e : ℝ) :
    M.gradPair (fun y => c * f y) (fun y => e * h y) x = c * e * M.gradPair f h x := by
  simp only [SmoothMetricChart.gradPair]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordPartial_const_mul hf c i, coordPartial_const_mul hh e j]
  ring

/-! ## The geometric defect is a Riccati potential -/

/-- **The defect is the Riccati expression of the weighted conformal factor.** -/
theorem conformalDefect_eq_riccati (M : SmoothMetricChart d) (a : ℝ)
    {σ : (Fin d → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) (x : Fin d → ℝ) :
    M.conformalDefect a σ x
      = M.dalembert (fun y => a * σ y) x
        + M.gradPair (fun y => a * σ y) (fun y => a * σ y) x := by
  rw [SmoothMetricChart.conformalDefect, M.dalembert_const_mul hσ a x,
    gradPair_const_mul M x (differentiableAt_of_contDiff_infty hσ x)
      (differentiableAt_of_contDiff_infty hσ x) a a]
  ring

/-- **The massless effective potential is a Riccati potential.** -/
theorem conformalPotential_zero_eq_chartRiccati (M : SmoothMetricChart d) (a : ℝ)
    {σ : (Fin d → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) :
    M.conformalPotential a 0 σ = chartRiccatiPotential M (fun y => a * σ y) := by
  funext x
  rw [SmoothMetricChart.conformalPotential, chartRiccatiPotential,
    conformalDefect_eq_riccati M a hσ x]
  ring

/-- **The massless species carries a globally nonvanishing probe**, namely `e^{aσ}`. -/
theorem solvesPotentialWave_masslessProbe (M : SmoothMetricChart d) (a : ℝ)
    {σ : (Fin d → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) :
    SolvesPotentialWave M.dalembert (M.conformalPotential a 0 σ)
      (chartExpProbe fun y => a * σ y) := by
  rw [conformalPotential_zero_eq_chartRiccati M a hσ]
  exact solvesPotentialWave_chartExpProbe M (contDiff_const.mul hσ)

theorem masslessProbe_ne_zero (a : ℝ) (σ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    (chartExpProbe fun y => a * σ y) x ≠ 0 := chartExpProbe_ne_zero _ x

/-- **The massless effective potential is determined, unconditionally.** -/
theorem noCommonZero_conformalPotential_zero (M : SmoothMetricChart d) (a : ℝ)
    {σ : (Fin d → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) :
    NoCommonZero M.dalembert (M.conformalPotential a 0 σ) := by
  rw [conformalPotential_zero_eq_chartRiccati M a hσ]
  exact noCommonZero_chartRiccatiPotential M (contDiff_const.mul hσ)

/-- **The shared geometric defect is recovered from a massless species alone.** -/
theorem conformalDefect_determined (M : SmoothMetricChart d) (a : ℝ)
    {σ : (Fin d → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) {other : (Fin d → ℝ) → ℝ}
    (hother : ∀ u ∈ solutionSet M.dalembert (M.conformalPotential a 0 σ),
      SolvesPotentialWave M.dalembert other u) :
    other = fun x => -(M.conformalDefect a σ x) := by
  rw [potential_eq_of_noCommonZero (noCommonZero_conformalPotential_zero M a hσ) hother]
  funext x
  rw [SmoothMetricChart.conformalPotential]
  ring

/-! ## One massive species suffices -/

/-- **The scale from a single massive species against the massless reference.** -/
theorem scale_of_one_massive_species (M : SmoothMetricChart d) (a massSq : ℝ)
    (hmass : massSq ≠ 0) (σ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    Real.exp (2 * σ x)
      = (M.conformalPotential a massSq σ x - M.conformalPotential a 0 σ x) / massSq := by
  rw [M.conformalPotential_difference a massSq 0 σ x, sub_zero]
  field_simp

/-- **The two-species reconstruction with the massless species as reference.** Only the massive
species contributes a hypothesis; the massless side is discharged by the probe `e^{aσ}`. -/
theorem twoSpecies_reconstruction_massless_reference (M : SmoothMetricChart d) (a : ℝ)
    {σ : (Fin d → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) {massSq : ℝ} (hmass : massSq ≠ 0)
    {other₁ other₂ : (Fin d → ℝ) → ℝ}
    (hno₁ : NoCommonZero M.dalembert (M.conformalPotential a massSq σ))
    (h₁ : ∀ u ∈ solutionSet M.dalembert (M.conformalPotential a massSq σ),
      SolvesPotentialWave M.dalembert other₁ u)
    (h₂ : ∀ u ∈ solutionSet M.dalembert (M.conformalPotential a 0 σ),
      SolvesPotentialWave M.dalembert other₂ u)
    (x : Fin d → ℝ) :
    reconstructedScale other₁ other₂ massSq 0 x = Real.exp (2 * σ x) := by
  rw [potential_eq_of_noCommonZero hno₁ h₁,
    potential_eq_of_noCommonZero (noCommonZero_conformalPotential_zero M a hσ) h₂,
    reconstructedScale, M.conformalPotential_difference a massSq 0 σ x]
  field_simp

/-- **The remaining input of the inverse step, isolated.** Given a probe family without a common
zero for one massive species, the conformal scale is recovered on any chart and for any smooth
conformal factor. -/
theorem scale_reconstruction_of_one_massive_probe_family (M : SmoothMetricChart d) (a : ℝ)
    {σ : (Fin d → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) {massSq : ℝ} (hmass : massSq ≠ 0)
    (hno₁ : NoCommonZero M.dalembert (M.conformalPotential a massSq σ))
    {other₁ other₂ : (Fin d → ℝ) → ℝ}
    (h₁ : ∀ u ∈ solutionSet M.dalembert (M.conformalPotential a massSq σ),
      SolvesPotentialWave M.dalembert other₁ u)
    (h₂ : ∀ u ∈ solutionSet M.dalembert (M.conformalPotential a 0 σ),
      SolvesPotentialWave M.dalembert other₂ u) :
    ∀ x : Fin d → ℝ, (other₁ x - other₂ x) / massSq = Real.exp (2 * σ x) := by
  intro x
  have h := twoSpecies_reconstruction_massless_reference M a hσ hmass hno₁ h₁ h₂ x
  rw [reconstructedScale, sub_zero] at h
  exact h

end GaloisForLFunctions.HTGeometry
