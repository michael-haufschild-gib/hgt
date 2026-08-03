import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import GaloisForLFunctions.HTGeometry.ClockPotentialDetermination

/-!
# Where two clock species reconstruct the conformal scale

The two-species scale law needs both effective potentials at an event. Each potential is pinned
exactly on its own probe determination set, so the reconstructed scale is unambiguous precisely on
the **intersection** of the two species' determination sets, and is genuinely ambiguous off it.

This locates the whole continuum-gravity bridge in one condition: the two clock species must have
probe families with no common zero at the events where the scale is wanted. Nothing else about the
geometry, the wave operators, or the coupling enters.

The determination locus is open whenever the probes are continuous, so the condition is stable: it
is enough to secure one nonvanishing probe per species at each event of interest.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

variable {X : Type u}

/-! ## Structure of the determination locus -/

theorem potentialDeterminationSet_mono {probes₁ probes₂ : Set (X → ℝ)}
    (h : probes₁ ⊆ probes₂) :
    potentialDeterminationSet probes₁ ⊆ potentialDeterminationSet probes₂ := by
  rintro x ⟨u, hu, hux⟩
  exact ⟨u, h hu, hux⟩

theorem potentialDeterminationSet_eq_iUnion (probes : Set (X → ℝ)) :
    potentialDeterminationSet probes = ⋃ u ∈ probes, {x | u x ≠ 0} := by
  ext x
  simp [potentialDeterminationSet]

/-- **The determination locus is open for continuous probes.** One nonvanishing probe at an event
determines the potential on a whole neighbourhood. -/
theorem isOpen_potentialDeterminationSet [TopologicalSpace X] {probes : Set (X → ℝ)}
    (hcont : ∀ u ∈ probes, Continuous u) :
    IsOpen (potentialDeterminationSet probes) := by
  rw [potentialDeterminationSet_eq_iUnion]
  refine isOpen_biUnion fun u hu => ?_
  exact isOpen_compl_singleton.preimage (hcont u hu)

/-! ## The scale determination locus -/

/-- Conformal scale reconstructed from two measured clock potentials. -/
noncomputable def reconstructedScale (potential₁ potential₂ : X → ℝ) (massSq₁ massSq₂ : ℝ)
    (x : X) : ℝ :=
  (potential₁ x - potential₂ x) / (massSq₁ - massSq₂)

/-- **The reconstructed scale is unambiguous exactly on the common determination locus.**

Any two pairs of potentials explaining the two species' probe families give the same scale at every
event where both families have a nonvanishing probe. -/
theorem reconstructedScale_eqOn_inter
    {wave₁ wave₂ : (X → ℝ) → (X → ℝ)} {probes₁ probes₂ : Set (X → ℝ)}
    {potential₁ potential₂ other₁ other₂ : X → ℝ} {massSq₁ massSq₂ : ℝ}
    (h₁ : ∀ u ∈ probes₁, SolvesPotentialWave wave₁ potential₁ u)
    (hother₁ : ∀ u ∈ probes₁, SolvesPotentialWave wave₁ other₁ u)
    (h₂ : ∀ u ∈ probes₂, SolvesPotentialWave wave₂ potential₂ u)
    (hother₂ : ∀ u ∈ probes₂, SolvesPotentialWave wave₂ other₂ u) :
    Set.EqOn (reconstructedScale potential₁ potential₂ massSq₁ massSq₂)
      (reconstructedScale other₁ other₂ massSq₁ massSq₂)
      (potentialDeterminationSet probes₁ ∩ potentialDeterminationSet probes₂) := by
  rintro x ⟨hx₁, hx₂⟩
  have e₁ : potential₁ x = other₁ x :=
    potential_eqOn_potentialDeterminationSet h₁ hother₁ hx₁
  have e₂ : potential₂ x = other₂ x :=
    potential_eqOn_potentialDeterminationSet h₂ hother₂ hx₂
  simp only [reconstructedScale, e₁, e₂]

/-- **Off the determination locus of either species the reconstructed scale is ambiguous.** -/
theorem exists_ne_reconstructedScale_of_notMem [DecidableEq X]
    {wave₁ : (X → ℝ) → (X → ℝ)} {probes₁ : Set (X → ℝ)}
    {potential₁ potential₂ : X → ℝ} {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂)
    (h₁ : ∀ u ∈ probes₁, SolvesPotentialWave wave₁ potential₁ u)
    {x₀ : X} (hx₀ : x₀ ∉ potentialDeterminationSet probes₁) :
    ∃ other₁ : X → ℝ,
      (∀ u ∈ probes₁, SolvesPotentialWave wave₁ other₁ u) ∧
        reconstructedScale other₁ potential₂ massSq₁ massSq₂ x₀ ≠
          reconstructedScale potential₁ potential₂ massSq₁ massSq₂ x₀ := by
  obtain ⟨other₁, hne, hsolve⟩ :=
    exists_ne_potential_with_same_probeSolutions h₁ hx₀
  refine ⟨other₁, hsolve, ?_⟩
  simp only [reconstructedScale]
  intro hEq
  have hden : massSq₁ - massSq₂ ≠ 0 := sub_ne_zero.mpr hmass
  rw [div_eq_div_iff hden hden] at hEq
  have hnum : other₁ x₀ - potential₂ x₀ = potential₁ x₀ - potential₂ x₀ :=
    mul_right_cancel₀ hden hEq
  exact hne (by linarith)

/-- **The bridge condition.** The conformal scale is reconstructible on a set exactly when both
species have a nonvanishing probe at each of its events. -/
theorem reconstructedScale_wellDefined_of_subset_inter
    {wave₁ wave₂ : (X → ℝ) → (X → ℝ)} {probes₁ probes₂ : Set (X → ℝ)}
    {potential₁ potential₂ other₁ other₂ : X → ℝ} {massSq₁ massSq₂ : ℝ}
    {region : Set X}
    (hregion : region ⊆ potentialDeterminationSet probes₁ ∩ potentialDeterminationSet probes₂)
    (h₁ : ∀ u ∈ probes₁, SolvesPotentialWave wave₁ potential₁ u)
    (hother₁ : ∀ u ∈ probes₁, SolvesPotentialWave wave₁ other₁ u)
    (h₂ : ∀ u ∈ probes₂, SolvesPotentialWave wave₂ potential₂ u)
    (hother₂ : ∀ u ∈ probes₂, SolvesPotentialWave wave₂ other₂ u) :
    Set.EqOn (reconstructedScale potential₁ potential₂ massSq₁ massSq₂)
      (reconstructedScale other₁ other₂ massSq₁ massSq₂) region :=
  (reconstructedScale_eqOn_inter h₁ hother₁ h₂ hother₂).mono hregion

/-- The bridge condition is stable: for continuous probes the common determination locus is
open. -/
theorem isOpen_scaleDeterminationLocus [TopologicalSpace X] {probes₁ probes₂ : Set (X → ℝ)}
    (hcont₁ : ∀ u ∈ probes₁, Continuous u) (hcont₂ : ∀ u ∈ probes₂, Continuous u) :
    IsOpen (potentialDeterminationSet probes₁ ∩ potentialDeterminationSet probes₂) :=
  (isOpen_potentialDeterminationSet hcont₁).inter (isOpen_potentialDeterminationSet hcont₂)

end GaloisForLFunctions.HTGeometry
