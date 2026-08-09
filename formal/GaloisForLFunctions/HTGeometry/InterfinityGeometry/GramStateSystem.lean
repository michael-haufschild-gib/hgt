import GaloisForLFunctions.HTGeometry.InterfinityGeometry.GramNerve

/-!
# Periodic source systems and their realizable Gram labels

A *state system* drives the clocked overlaps of a family of experiments through a finite set of
states, each of which recurs cofinally.  Allowed synchronizations are the subnets of the clock,
that is the nonempty filters refining the tail filter.

For such a system a labelled tuple is realized exactly when one single state reproduces the whole
Gram label.  The forward direction is a pigeonhole on the finite state set followed by uniqueness
of limits; the backward direction restricts the clock to the recurrences of that state.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open Filter Topology

universe u

/-- The allowed source synchronizations: nonempty subnets of the clock. -/
def clockSubnets : Set (Filter ℕ) := {σ | σ.NeBot ∧ σ ≤ atTop}

/-- The overlap datum of a finite-state source system. -/
def stateOverlapDatum {A : Type u} {S : Type} (stable : A → Prop) (st : ℕ → S)
    (w : S → A → A → ℂ) : GramNerveDatum A :=
  overlapDatum stable (fun a b i => w (st i) a b) clockSubnets

variable {A : Type u} {S : Type} [Fintype S]

omit [Fintype S] in
/-- A recurring state produces a synchronization on which the overlaps are constant. -/
theorem realized_of_state {stable : A → Prop} {st : ℕ → S} {w : S → A → A → ℂ}
    (hcof : ∀ (s : S) (N : ℕ), ∃ n, N ≤ n ∧ st n = s) {n : ℕ} (p : GramSimplex A n) (s : S)
    (hp : ∀ r r', p.2 r r' = w s (p.1 r) (p.1 r')) :
    (stateOverlapDatum stable st w).realized n p := by
  refine ⟨atTop ⊓ Filter.principal {i | st i = s}, ⟨?_, inf_le_left⟩, ?_⟩
  · rw [Filter.inf_principal_neBot_iff]
    intro U hU
    obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.1 hU
    obtain ⟨m, hmN, hm⟩ := hcof s N
    exact ⟨m, hN m hmN, hm⟩
  · intro r r'
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self _)] with i hi
    rw [hp r r']
    exact congrArg (fun t => w t (p.1 r) (p.1 r')) hi.symm

/-- Some state of a finite state system recurs along every synchronization. -/
theorem exists_state_neBot {st : ℕ → S} {σ : Filter ℕ} (hσ : σ.NeBot) :
    ∃ s : S, (σ ⊓ Filter.principal {i | st i = s}).NeBot := by
  by_contra hcon
  have hmem : ∀ s : S, {i | st i = s}ᶜ ∈ σ := by
    intro s
    have h1 : ¬ (σ ⊓ Filter.principal {i | st i = s}).NeBot := fun hne => hcon ⟨s, hne⟩
    rw [Filter.not_neBot] at h1
    exact Filter.inf_principal_eq_bot.1 h1
  have hall : (⋂ s : S, {i : ℕ | st i = s}ᶜ) ∈ σ := Filter.iInter_mem.2 hmem
  have hempty : (⋂ s : S, {i : ℕ | st i = s}ᶜ) = (∅ : Set ℕ) := by
    ext i
    simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false, not_forall, not_not]
    exact ⟨st i, rfl⟩
  rw [hempty] at hall
  exact hσ.ne (Filter.empty_mem_iff_bot.1 hall)

/-- **Realizable labels of a finite-state system.**  A labelled tuple is realized exactly when one
single state reproduces its whole Gram label. -/
theorem realized_stateOverlapDatum_iff {stable : A → Prop} {st : ℕ → S} {w : S → A → A → ℂ}
    (hcof : ∀ (s : S) (N : ℕ), ∃ n, N ≤ n ∧ st n = s) {n : ℕ} (p : GramSimplex A n) :
    (stateOverlapDatum stable st w).realized n p ↔
      ∃ s : S, ∀ r r', p.2 r r' = w s (p.1 r) (p.1 r') := by
  constructor
  · rintro ⟨σ, ⟨hne, -⟩, h⟩
    obtain ⟨s, hs⟩ := exists_state_neBot (st := st) hne
    refine ⟨s, fun r r' => ?_⟩
    have h1 : Tendsto (fun i => w (st i) (p.1 r) (p.1 r'))
        (σ ⊓ Filter.principal {i | st i = s}) (𝓝 (p.2 r r')) :=
      (h r r').mono_left inf_le_left
    have h2 : Tendsto (fun i => w (st i) (p.1 r) (p.1 r'))
        (σ ⊓ Filter.principal {i | st i = s}) (𝓝 (w s (p.1 r) (p.1 r'))) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self _)] with i hi
      exact congrArg (fun t => w t (p.1 r) (p.1 r')) hi.symm
    exact tendsto_nhds_unique h1 h2
  · rintro ⟨s, hs⟩
    exact realized_of_state hcof p s hs

/-- Realizability of a labelled tuple by a finite-state system, unfolded. -/
theorem realizes_stateOverlapDatum_iff {stable : A → Prop} {st : ℕ → S} {w : S → A → A → ℂ}
    (hcof : ∀ (s : S) (N : ℕ), ∃ n, N ≤ n ∧ st n = s) {n : ℕ} (p : GramSimplex A n) :
    (stateOverlapDatum stable st w).Realizes p ↔
      (∀ r, stable (p.1 r)) ∧ ∃ s : S, ∀ r r', p.2 r r' = w s (p.1 r) (p.1 r') := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (realized_stateOverlapDatum_iff hcof p).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (realized_stateOverlapDatum_iff hcof p).2 h2⟩

end GaloisForLFunctions.HTGeometry.Interfinity
