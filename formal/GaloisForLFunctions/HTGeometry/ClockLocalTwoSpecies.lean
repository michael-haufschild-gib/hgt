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

/-- **In dimension two the conformal conjugation weight vanishes**, so the weight `0` used
throughout this section is the physical one and no conjugation is needed. -/
theorem conformalDimensionWeight_two :
    ExponentialSecondOrderClockCalculus.conformalDimensionWeight (1 + 1) = 0 := by
  rw [ExponentialSecondOrderClockCalculus.conformalDimensionWeight]
  norm_num

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

/-! ## Probes on open regions

A probe solving the equation at a single event is not a clock: the equation at one point is one
linear relation between the second derivatives there, and a quadratic polynomial satisfies it. The
physical notion is a solution on an open region, and the determination hypothesis should quantify
over those. Everything above transports to that reading, and the two-dimensional construction
supplies it, because its probe solves on a whole neighbourhood and is nonvanishing throughout.
-/

section OpenProbes

variable {Y : Type v} [TopologicalSpace Y]

/-- A family of clock probes, one for each event, each solving the equation on an open neighbourhood
of its event and nonvanishing throughout it. -/
def OpenProbes (wave : (Y → ℝ) → (Y → ℝ)) (potential : Y → ℝ) : Prop :=
  ∀ x : Y, ∃ W : Set Y, IsOpen W ∧ x ∈ W ∧ ∃ u : Y → ℝ,
    SolvesPotentialWaveOn wave potential u W ∧ ∀ y ∈ W, u y ≠ 0

/-- **Probes on open regions determine the potential.** -/
theorem potential_eq_of_openProbes {wave : (Y → ℝ) → (Y → ℝ)} {potential other : Y → ℝ}
    (hopen : OpenProbes wave potential)
    (h : ∀ (u : Y → ℝ) (W : Set Y), IsOpen W →
      SolvesPotentialWaveOn wave potential u W → SolvesPotentialWaveOn wave other u W) :
    other = potential := by
  funext x
  obtain ⟨W, hWopen, hxW, u, hu, hune⟩ := hopen x
  exact potential_eqOn_of_solvesOn hu (h u W hWopen hu) hune hxW

/-- A single globally nonvanishing global solution already gives probes on open regions. -/
theorem openProbes_of_solves {wave : (Y → ℝ) → (Y → ℝ)} {potential u : Y → ℝ}
    (hu : SolvesPotentialWave wave potential u) (hune : ∀ y, u y ≠ 0) :
    OpenProbes wave potential :=
  fun x => ⟨Set.univ, isOpen_univ, Set.mem_univ x, u, fun y _ => hu y, fun y _ => hune y⟩

end OpenProbes

/-- **The two-species scale law from probes on open regions.** -/
theorem scale_reconstruction_of_openProbes {d : ℕ} (M : SmoothMetricChart d) (a : ℝ)
    {σ : (Fin d → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ) {massSq : ℝ} (hmass : massSq ≠ 0)
    (hop₁ : OpenProbes M.dalembert (M.conformalPotential a massSq σ))
    {other₁ other₂ : (Fin d → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)), IsOpen W →
      SolvesPotentialWaveOn M.dalembert (M.conformalPotential a massSq σ) u W →
        SolvesPotentialWaveOn M.dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)), IsOpen W →
      SolvesPotentialWaveOn M.dalembert (M.conformalPotential a 0 σ) u W →
        SolvesPotentialWaveOn M.dalembert other₂ u W)
    (x : Fin d → ℝ) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * σ x) := by
  have e₁ : other₁ = M.conformalPotential a massSq σ := potential_eq_of_openProbes hop₁ h₁
  have e₂ : other₂ = M.conformalPotential a 0 σ :=
    potential_eq_of_openProbes
      (openProbes_of_solves (solvesPotentialWave_masslessProbe M a hσ)
        (masslessProbe_ne_zero a σ)) h₂
  rw [e₁, e₂, M.conformalPotential_difference a massSq 0 σ x, sub_zero]
  field_simp

/-- **A two-dimensional clock species has probes on open regions at every event,
unconditionally.** -/
theorem openProbes_conformalPotential_two {σ : (Fin (1 + 1) → ℝ) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    (massSq : ℝ) :
    OpenProbes flatChartTwo.dalembert (flatChartTwo.conformalPotential 0 massSq σ) := by
  have hσ1 : ContDiff ℝ 1 σ := hσ.of_le (by exact_mod_cast le_top)
  have hV : ContDiff ℝ 1 fun y : Fin (1 + 1) → ℝ => massSq * Real.exp (2 * σ y) :=
    contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul hσ1))
  rw [conformalPotential_weight_zero]
  intro x
  obtain ⟨W, hWopen, hxW, U, hUon, hUne, _⟩ := exists_clockProbe_on_two_dimensional hV x
  exact ⟨W, hWopen, hxW, U, hUon, hUne⟩

/-- **The two-species conformal clock scale law in two dimensions, from probes on open regions,
unconditionally.**

This is the physical form of the reconstruction: the probe families quantified over are genuine
solutions on open regions, and the massive family required as input is proved to exist rather than
assumed. -/
theorem twoSpecies_scale_reconstruction_open_two_dimensional {σ : (Fin (1 + 1) → ℝ) → ℝ}
    (hσ : ContDiff ℝ ∞ σ) {massSq : ℝ} (hmass : massSq ≠ 0)
    {other₁ other₂ : (Fin (1 + 1) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (1 + 1) → ℝ) → ℝ) (W : Set (Fin (1 + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn flatChartTwo.dalembert
          (flatChartTwo.conformalPotential 0 massSq σ) u W →
        SolvesPotentialWaveOn flatChartTwo.dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (1 + 1) → ℝ) → ℝ) (W : Set (Fin (1 + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn flatChartTwo.dalembert (flatChartTwo.conformalPotential 0 0 σ) u W →
        SolvesPotentialWaveOn flatChartTwo.dalembert other₂ u W)
    (x : Fin (1 + 1) → ℝ) :
    (other₁ x - other₂ x) / massSq = Real.exp (2 * σ x) :=
  scale_reconstruction_of_openProbes flatChartTwo 0 hσ hmass
    (openProbes_conformalPotential_two hσ massSq) h₁ h₂ x

/-- The packaged form: the reconstructed scale of the two species is the conformal scale. -/
theorem twoSpecies_reconstructedScale_open_two_dimensional {σ : (Fin (1 + 1) → ℝ) → ℝ}
    (hσ : ContDiff ℝ ∞ σ) {massSq : ℝ} (hmass : massSq ≠ 0)
    {other₁ other₂ : (Fin (1 + 1) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (1 + 1) → ℝ) → ℝ) (W : Set (Fin (1 + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn flatChartTwo.dalembert
          (flatChartTwo.conformalPotential 0 massSq σ) u W →
        SolvesPotentialWaveOn flatChartTwo.dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (1 + 1) → ℝ) → ℝ) (W : Set (Fin (1 + 1) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn flatChartTwo.dalembert (flatChartTwo.conformalPotential 0 0 σ) u W →
        SolvesPotentialWaveOn flatChartTwo.dalembert other₂ u W)
    (x : Fin (1 + 1) → ℝ) :
    reconstructedScale other₁ other₂ massSq 0 x = Real.exp (2 * σ x) := by
  rw [reconstructedScale, sub_zero]
  exact twoSpecies_scale_reconstruction_open_two_dimensional hσ hmass h₁ h₂ x

end GaloisForLFunctions.HTGeometry
