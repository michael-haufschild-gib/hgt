import GaloisForLFunctions.HTGeometry.ClockScaleDeterminationLocus

/-!
# One nonvanishing probe suffices for a repeatable experiment

The determination locus of a probe family is where some probe is nonvanishing. Securing it
pointwise looks like an infinite family of separate demands. It is not, for the family a laboratory
actually produces.

A laboratory repeats its intervention at translated events, so its probe family is closed under the
action that moves events. For such a family the determination locus is a union of orbits, and if the
action is transitive it is all-or-nothing: **one nonvanishing observation anywhere determines the
potential everywhere.**

Applied to both clock species, one nonvanishing probe per species reconstructs the conformal scale
on the whole event set.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

variable {X : Type u} {G : Type v}

/-- A probe family is closed under an action on events when every translated probe is again a
probe. This is the family produced by repeating an intervention at moved events. -/
def ProbeActionClosed (act : G → X → X) (probes : Set (X → ℝ)) : Prop :=
  ∀ (g : G), ∀ u ∈ probes, (fun x => u (act g x)) ∈ probes

/-- **The determination locus is a union of orbits.** -/
theorem mem_potentialDeterminationSet_of_act {act : G → X → X} {probes : Set (X → ℝ)}
    (hclosed : ProbeActionClosed act probes) {x y : X}
    (hx : x ∈ potentialDeterminationSet probes) (g : G) (hg : act g y = x) :
    y ∈ potentialDeterminationSet probes := by
  obtain ⟨u, hu, hux⟩ := hx
  refine ⟨fun z => u (act g z), hclosed g u hu, ?_⟩
  show u (act g y) ≠ 0
  rw [hg]
  exact hux

/-- **All or nothing for a transitively repeatable experiment.** If the events can all be reached
from one another, a probe family closed under the action either determines the potential nowhere or
determines it everywhere. -/
theorem potentialDeterminationSet_eq_univ_of_transitive {act : G → X → X}
    {probes : Set (X → ℝ)} (hclosed : ProbeActionClosed act probes)
    (htrans : ∀ x y : X, ∃ g : G, act g y = x)
    (hne : (potentialDeterminationSet probes).Nonempty) :
    potentialDeterminationSet probes = Set.univ := by
  obtain ⟨x₀, hx₀⟩ := hne
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨g, hg⟩ := htrans x₀ y
  exact mem_potentialDeterminationSet_of_act hclosed hx₀ g hg

/-- **One nonvanishing observation determines the whole potential.** -/
theorem potentialDeterminationSet_eq_univ_of_exists_ne_zero {act : G → X → X}
    {probes : Set (X → ℝ)} (hclosed : ProbeActionClosed act probes)
    (htrans : ∀ x y : X, ∃ g : G, act g y = x)
    {u : X → ℝ} (hu : u ∈ probes) {x₀ : X} (hux : u x₀ ≠ 0) :
    potentialDeterminationSet probes = Set.univ :=
  potentialDeterminationSet_eq_univ_of_transitive hclosed htrans ⟨x₀, u, hu, hux⟩

/-- **A repeatable experiment pins the potential globally.** -/
theorem potential_eq_of_repeatable {wave : (X → ℝ) → (X → ℝ)} {act : G → X → X}
    {probes : Set (X → ℝ)} {potential₁ potential₂ : X → ℝ}
    (hclosed : ProbeActionClosed act probes)
    (htrans : ∀ x y : X, ∃ g : G, act g y = x)
    {u : X → ℝ} (hu : u ∈ probes) {x₀ : X} (hux : u x₀ ≠ 0)
    (h₁ : ∀ v ∈ probes, SolvesPotentialWave wave potential₁ v)
    (h₂ : ∀ v ∈ probes, SolvesPotentialWave wave potential₂ v) :
    potential₁ = potential₂ := by
  funext x
  refine potential_eqOn_potentialDeterminationSet h₁ h₂ ?_
  rw [potentialDeterminationSet_eq_univ_of_exists_ne_zero hclosed htrans hu hux]
  trivial

/-- **The bridge closes for two repeatable species.** One nonvanishing probe per species
reconstructs the conformal scale unambiguously at every event. -/
theorem reconstructedScale_eq_of_repeatable
    {wave₁ wave₂ : (X → ℝ) → (X → ℝ)} {act : G → X → X}
    {probes₁ probes₂ : Set (X → ℝ)}
    {potential₁ potential₂ other₁ other₂ : X → ℝ} {massSq₁ massSq₂ : ℝ}
    (htrans : ∀ x y : X, ∃ g : G, act g y = x)
    (hclosed₁ : ProbeActionClosed act probes₁) (hclosed₂ : ProbeActionClosed act probes₂)
    {u₁ : X → ℝ} (hu₁ : u₁ ∈ probes₁) {x₁ : X} (hux₁ : u₁ x₁ ≠ 0)
    {u₂ : X → ℝ} (hu₂ : u₂ ∈ probes₂) {x₂ : X} (hux₂ : u₂ x₂ ≠ 0)
    (h₁ : ∀ v ∈ probes₁, SolvesPotentialWave wave₁ potential₁ v)
    (hother₁ : ∀ v ∈ probes₁, SolvesPotentialWave wave₁ other₁ v)
    (h₂ : ∀ v ∈ probes₂, SolvesPotentialWave wave₂ potential₂ v)
    (hother₂ : ∀ v ∈ probes₂, SolvesPotentialWave wave₂ other₂ v) :
    reconstructedScale potential₁ potential₂ massSq₁ massSq₂ =
      reconstructedScale other₁ other₂ massSq₁ massSq₂ := by
  funext x
  refine reconstructedScale_eqOn_inter h₁ hother₁ h₂ hother₂ ?_
  constructor
  · rw [potentialDeterminationSet_eq_univ_of_exists_ne_zero hclosed₁ htrans hu₁ hux₁]
    trivial
  · rw [potentialDeterminationSet_eq_univ_of_exists_ne_zero hclosed₂ htrans hu₂ hux₂]
    trivial

/-! ### The hypothesis class is inhabited -/

/-- Nonzero constant probes form a translation-closed family. -/
def constantProbes (X : Type u) : Set (X → ℝ) :=
  {u | ∃ c : ℝ, c ≠ 0 ∧ u = fun _ => c}

theorem probeActionClosed_constantProbes (act : G → X → X) :
    ProbeActionClosed act (constantProbes X) := by
  rintro g u ⟨c, hc, rfl⟩
  exact ⟨c, hc, rfl⟩

theorem potentialDeterminationSet_constantProbes [Nonempty X] :
    potentialDeterminationSet (constantProbes X) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  exact ⟨fun _ => 1, ⟨1, one_ne_zero, rfl⟩, one_ne_zero⟩

end GaloisForLFunctions.HTGeometry
