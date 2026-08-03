import GaloisForLFunctions.HTGeometry.ClockConformalTwoDimensional
import GaloisForLFunctions.HTGeometry.ClockMasslessReference

/-!
# The two-species scale law from local probes, and its unconditional two-dimensional case

The two-species reconstruction was stated with a probe family without a common zero, that is, with
*global* solutions of the clock equation. Determination never needs that much: a probe solving the
equation at one event and nonvanishing there already pins the potential at that event, so a family
of purely local probes suffices. This file restates the reconstruction in that form.

In dimension two the local form is unconditional. The conformal weight is `(d-2)/2 = 0`, so the
effective potential of a species of squared mass `μ` is exactly `μ e^{2σ}`, and the two-dimensional
existence theorem produces a probe normalised to `1` at every event. The remaining input of the
inverse step therefore disappears in that dimension: the conformal scale is reconstructed from the
two species' probe families with no hypothesis beyond smoothness of the conformal factor.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

universe v

variable {X : Type v}

/-- **Local probes turn a probe inclusion into an identity of potentials.** -/
theorem potential_eq_of_localProbesOn {wave : (X → ℝ) → (X → ℝ)}
    {potential other : X → ℝ} (hlocal : LocalProbesOn wave potential Set.univ)
    (h : ∀ (u : X → ℝ) (x : X), SolvesPotentialWaveAt wave potential u x →
      SolvesPotentialWaveAt wave other u x) :
    other = potential :=
  potential_eq_of_localProbes_univ fun x => by
    obtain ⟨u, hu, hux⟩ := hlocal x (Set.mem_univ x)
    exact ⟨u, hu, h u x hu, hux⟩

/-- A probe family without a common zero is in particular a family of local probes. -/
theorem localProbesOn_of_noCommonZero {wave : (X → ℝ) → (X → ℝ)} {potential : X → ℝ}
    (h : NoCommonZero wave potential) : LocalProbesOn wave potential Set.univ := by
  intro x _
  obtain ⟨u, hu, hux⟩ := h x
  exact ⟨u, hu x, hux⟩

/-- **The two-species scale law from local probes.** The massless species needs no hypothesis: its
effective potential is of Riccati type, with the globally nonvanishing probe `e^{aσ}`. -/
theorem scale_reconstruction_of_local_probes {d : ℕ} (M : SmoothMetricChart d) (a : ℝ)
    {σ : (Fin d → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) {massSq : ℝ} (hmass : massSq ≠ 0)
    (hloc₁ : LocalProbesOn M.dalembert (M.conformalPotential a massSq σ) Set.univ)
    {other₁ other₂ : (Fin d → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ),
      SolvesPotentialWaveAt M.dalembert (M.conformalPotential a massSq σ) u x →
        SolvesPotentialWaveAt M.dalembert other₁ u x)
    (h₂ : ∀ (u : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ),
      SolvesPotentialWaveAt M.dalembert (M.conformalPotential a 0 σ) u x →
        SolvesPotentialWaveAt M.dalembert other₂ u x)
    (x : Fin d → ℝ) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * σ x) := by
  have e₁ : other₁ = M.conformalPotential a massSq σ := potential_eq_of_localProbesOn hloc₁ h₁
  have e₂ : other₂ = M.conformalPotential a 0 σ :=
    potential_eq_of_localProbesOn
      (localProbesOn_of_noCommonZero (noCommonZero_conformalPotential_zero M a hσ)) h₂
  rw [e₁, e₂, M.conformalPotential_difference a massSq 0 σ x, sub_zero]
  field_simp

/-! ## The unconditional two-dimensional case -/

/-- The flat Minkowski chart of a two-dimensional clock spacetime. -/
noncomputable def flatChartTwo : SmoothMetricChart (1 + 1) :=
  (SmoothPseudoMetric.ofSignature nullEps nullEps_ne_zero).chart

/-- At the two-dimensional conformal weight the effective potential is the bare rescaled mass. -/
theorem conformalPotential_weight_zero {d : ℕ} (M : SmoothMetricChart d) (massSq : ℝ)
    (σ : (Fin d → ℝ) → ℝ) :
    M.conformalPotential 0 massSq σ = fun y => massSq * Real.exp (2 * σ y) := by
  funext y
  simp [SmoothMetricChart.conformalPotential, SmoothMetricChart.conformalDefect]

/-- **A two-dimensional clock species has local probes at every event, unconditionally.** -/
theorem localProbesOn_conformalPotential_two {σ : (Fin (1 + 1) → ℝ) → ℝ}
    (hσ : ContDiff ℝ ∞ σ) (massSq : ℝ) :
    LocalProbesOn flatChartTwo.dalembert (flatChartTwo.conformalPotential 0 massSq σ)
      Set.univ := by
  have hσ1 : ContDiff ℝ 1 σ := hσ.of_le (by exact_mod_cast le_top)
  have hV : ContDiff ℝ 1 fun y : Fin (1 + 1) → ℝ => massSq * Real.exp (2 * σ y) :=
    contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul hσ1))
  rw [conformalPotential_weight_zero]
  exact localProbesOn_univ_two_dimensional hV

/-- **The two-species conformal clock scale law, unconditionally, in two dimensions.**

The conformal scale of a two-dimensional clock spacetime is reconstructed from the effective
potentials of one massive and one massless species, with no hypothesis whatever on the probe
families: the required probes exist. -/
theorem twoSpecies_scale_reconstruction_two_dimensional {σ : (Fin (1 + 1) → ℝ) → ℝ}
    (hσ : ContDiff ℝ ∞ σ) {massSq : ℝ} (hmass : massSq ≠ 0)
    {other₁ other₂ : (Fin (1 + 1) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (1 + 1) → ℝ) → ℝ) (x : Fin (1 + 1) → ℝ),
      SolvesPotentialWaveAt flatChartTwo.dalembert
          (flatChartTwo.conformalPotential 0 massSq σ) u x →
        SolvesPotentialWaveAt flatChartTwo.dalembert other₁ u x)
    (h₂ : ∀ (u : (Fin (1 + 1) → ℝ) → ℝ) (x : Fin (1 + 1) → ℝ),
      SolvesPotentialWaveAt flatChartTwo.dalembert (flatChartTwo.conformalPotential 0 0 σ) u x →
        SolvesPotentialWaveAt flatChartTwo.dalembert other₂ u x)
    (x : Fin (1 + 1) → ℝ) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * σ x) :=
  scale_reconstruction_of_local_probes flatChartTwo 0 hσ hmass
    (localProbesOn_conformalPotential_two hσ massSq) h₁ h₂ x

/-- The same statement in the packaged form of the reconstruction: the reconstructed scale of the
two species is the conformal scale. -/
theorem twoSpecies_reconstructedScale_two_dimensional {σ : (Fin (1 + 1) → ℝ) → ℝ}
    (hσ : ContDiff ℝ ∞ σ) {massSq : ℝ} (hmass : massSq ≠ 0)
    {other₁ other₂ : (Fin (1 + 1) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (1 + 1) → ℝ) → ℝ) (x : Fin (1 + 1) → ℝ),
      SolvesPotentialWaveAt flatChartTwo.dalembert
          (flatChartTwo.conformalPotential 0 massSq σ) u x →
        SolvesPotentialWaveAt flatChartTwo.dalembert other₁ u x)
    (h₂ : ∀ (u : (Fin (1 + 1) → ℝ) → ℝ) (x : Fin (1 + 1) → ℝ),
      SolvesPotentialWaveAt flatChartTwo.dalembert (flatChartTwo.conformalPotential 0 0 σ) u x →
        SolvesPotentialWaveAt flatChartTwo.dalembert other₂ u x)
    (x : Fin (1 + 1) → ℝ) :
    reconstructedScale other₁ other₂ massSq 0 x = Real.exp (2 * σ x) := by
  rw [reconstructedScale, sub_zero]
  exact twoSpecies_scale_reconstruction_two_dimensional hσ hmass h₁ h₂ x

end GaloisForLFunctions.HTGeometry
