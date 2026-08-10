import Mathlib.Topology.Sequences
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Native sequential repair heredity

This module constructs the classical Arens two-storey topology and certifies a non-rewriting
endogenous-completion mechanism.  One native sequential-closure operation generates two strict
repair layers, the second witnessed entirely by outputs of the first, while ordinary closure is
already stationary at the initial leaf set.

Paper source:
`docs/drafts/pipeline/2-fully-proven/universal-law-field/endogenous-completion-mechanics/
arens-native-sequential-repair-heredity-and-stationary-closure-law.md`.
-/

open Filter Set Topology

namespace ConstitutiveSequentialRepairHeredity

/-- Root, branch points, and row leaves of the Arens completion laboratory. -/
inductive ArensPoint
  | root
  | branch (n : ℕ)
  | leaf (n m : ℕ)
  deriving DecidableEq, Repr

open ArensPoint

/-- Native open-set law: branch points admit row tails and the root admits a branch tail. -/
def ArensOpen (U : Set ArensPoint) : Prop :=
  (∀ n, branch n ∈ U → ∃ M, ∀ m, M ≤ m → leaf n m ∈ U) ∧
  (root ∈ U → ∃ N, ∀ n, N ≤ n → branch n ∈ U)

/-- The actual Arens topology used by the sequential-repair mechanism. -/
instance : TopologicalSpace ArensPoint where
  IsOpen := ArensOpen
  isOpen_univ := by
    constructor
    · intro n hn
      exact ⟨0, fun m hm => Set.mem_univ _⟩
    · intro hr
      exact ⟨0, fun n hn => Set.mem_univ _⟩
  isOpen_inter := by
    intro U V hU hV
    constructor
    · intro n hn
      rcases hU.1 n hn.1 with ⟨M, hM⟩
      rcases hV.1 n hn.2 with ⟨K, hK⟩
      exact ⟨max M K, fun m hm => ⟨hM m (le_trans (le_max_left _ _) hm),
        hK m (le_trans (le_max_right _ _) hm)⟩⟩
    · intro hr
      rcases hU.2 hr.1 with ⟨N, hN⟩
      rcases hV.2 hr.2 with ⟨K, hK⟩
      exact ⟨max N K, fun n hn => ⟨hN n (le_trans (le_max_left _ _) hn),
        hK n (le_trans (le_max_right _ _) hn)⟩⟩
  isOpen_sUnion := by
    intro S hS
    constructor
    · intro n hn
      rcases hn with ⟨U, hUS, hnU⟩
      rcases (hS U hUS).1 n hnU with ⟨M, hM⟩
      exact ⟨M, fun m hm => ⟨U, hUS, hM m hm⟩⟩
    · intro hr
      rcases hr with ⟨U, hUS, hrU⟩
      rcases (hS U hUS).2 hrU with ⟨N, hN⟩
      exact ⟨N, fun n hn => ⟨U, hUS, hN n hn⟩⟩

theorem isOpen_iff_arensOpen {U : Set ArensPoint} : IsOpen U ↔ ArensOpen U := Iff.rfl

/-- Initial operationally incomplete set: every row leaf and no limit point. -/
def leaves : Set ArensPoint := {x | match x with | leaf _ _ => True | _ => False}

/-- First repair layer: branch limits. -/
def branches : Set ArensPoint := {x | match x with | branch _ => True | _ => False}

@[simp] theorem leaf_mem_leaves (n m : ℕ) : leaf n m ∈ leaves := by simp [leaves]
@[simp] theorem branch_not_mem_leaves (n : ℕ) : branch n ∉ leaves := by simp [leaves]
@[simp] theorem root_not_mem_leaves : root ∉ leaves := by simp [leaves]

@[simp] theorem branch_mem_branches (n : ℕ) : branch n ∈ branches := by simp [branches]
@[simp] theorem leaf_not_mem_branches (n m : ℕ) : leaf n m ∉ branches := by simp [branches]
@[simp] theorem root_not_mem_branches : root ∉ branches := by simp [branches]

/-- Every fixed leaf row converges to its native branch point. -/
theorem leafRow_tendsto (n : ℕ) :
    Tendsto (fun m => leaf n m) atTop (𝓝 (branch n)) := by
  rw [Filter.tendsto_atTop']
  intro s hs
  rcases mem_nhds_iff.mp hs with ⟨U, hUs, hU, hnU⟩
  rcases hU.1 n hnU with ⟨M, hM⟩
  exact ⟨M, fun m hm => hUs (hM m hm)⟩

/-- The sequence of first repair outputs converges to the second repair point. -/
theorem branch_tendsto_root : Tendsto branch atTop (𝓝 root) := by
  rw [Filter.tendsto_atTop']
  intro s hs
  rcases mem_nhds_iff.mp hs with ⟨U, hUs, hU, hrU⟩
  rcases hU.2 hrU with ⟨N, hN⟩
  exact ⟨N, fun n hn => hUs (hN n hn)⟩

def row : ArensPoint → ℕ
  | root => 0
  | branch n => n
  | leaf n _ => n

def col : ArensPoint → ℕ
  | root => 0
  | branch _ => 0
  | leaf _ m => m

/-- Root neighborhood omitting one whole branch and its leaf row. -/
def omitRow (n : ℕ) : Set ArensPoint :=
  {x | match x with | root => True | branch j => j ≠ n | leaf j _ => j ≠ n}

theorem isOpen_omitRow (n : ℕ) : IsOpen (omitRow n) := by
  constructor
  · intro j hj
    exact ⟨0, fun m hm => by simpa [omitRow] using hj⟩
  · intro hr
    exact ⟨n + 1, fun j hj => by simp only [omitRow, Set.mem_setOf_eq]; omega⟩

@[simp] theorem root_mem_omitRow (n : ℕ) : root ∈ omitRow n := by simp [omitRow]

theorem leaf_not_mem_omitRow_of_row_eq {x : ArensPoint} {n : ℕ}
    (hx : x ∈ leaves) (hr : row x = n) : x ∉ omitRow n := by
  cases x <;> simp [leaves, row, omitRow] at hx hr ⊢
  exact hr

/-- Root neighborhood retaining all branches but only a prescribed tail of each leaf row. -/
def diagonalNhd (c : ℕ → ℕ) : Set ArensPoint :=
  {x | match x with | root => True | branch _ => True | leaf n m => c n ≤ m}

theorem isOpen_diagonalNhd (c : ℕ → ℕ) : IsOpen (diagonalNhd c) := by
  constructor
  · intro n hn
    exact ⟨c n, fun m hm => hm⟩
  · intro hr
    exact ⟨0, fun n hn => by simp [diagonalNhd]⟩

@[simp] theorem root_mem_diagonalNhd (c : ℕ → ℕ) : root ∈ diagonalNhd c := by
  simp [diagonalNhd]

theorem leaf_not_mem_diagonalNhd_of_lt {x : ArensPoint} {c : ℕ → ℕ}
    (hx : x ∈ leaves) (hlt : col x < c (row x)) : x ∉ diagonalNhd c := by
  cases x <;> simp [leaves, row, col, diagonalNhd] at hx hlt ⊢
  omega

/-- No sequence consisting only of original leaves can execute the second repair directly. -/
theorem no_leaf_sequence_tendsto_root (x : ℕ → ArensPoint)
    (hx : ∀ k, x k ∈ leaves) : ¬ Tendsto x atTop (𝓝 root) := by
  intro ht
  by_cases hfreq : ∃ n, ∀ K, ∃ k, K ≤ k ∧ row (x k) = n
  · rcases hfreq with ⟨n, hn⟩
    have hnhd : omitRow n ∈ 𝓝 root := (isOpen_omitRow n).mem_nhds (root_mem_omitRow n)
    rcases (Filter.tendsto_atTop'.mp ht) (omitRow n) hnhd with ⟨K, hK⟩
    rcases hn K with ⟨k, hk, hr⟩
    exact (leaf_not_mem_omitRow_of_row_eq (hx k) hr) (hK k hk)
  · push Not at hfreq
    choose K hK using hfreq
    let c : ℕ → ℕ := fun n => (Finset.range (K n)).sup (fun k => col (x k)) + 1
    have hnone : ∀ k, x k ∉ diagonalNhd c := by
      intro k
      have hklt : k < K (row (x k)) := by
        by_contra h
        exact hK (row (x k)) k (Nat.le_of_not_gt h) rfl
      have hle : col (x k) ≤ (Finset.range (K (row (x k)))).sup (fun j => col (x j)) :=
        Finset.le_sup (f := fun j => col (x j)) (Finset.mem_range.mpr hklt)
      apply leaf_not_mem_diagonalNhd_of_lt (hx k)
      dsimp [c]
      omega
    have hnhd : diagonalNhd c ∈ 𝓝 root :=
      (isOpen_diagonalNhd c).mem_nhds (root_mem_diagonalNhd c)
    rcases (Filter.tendsto_atTop'.mp ht) (diagonalNhd c) hnhd with ⟨K₀, hK₀⟩
    exact hnone K₀ (hK₀ K₀ le_rfl)

/-- First native sequential repair adds exactly the branch layer. -/
theorem seqClosure_leaves_eq : seqClosure leaves = leaves ∪ branches := by
  ext x
  constructor
  · rintro ⟨s, hs, ht⟩
    cases x with
    | root => exact (no_leaf_sequence_tendsto_root s hs ht).elim
    | branch n => simp [leaves, branches]
    | leaf n m => simp [leaves, branches]
  · intro hx
    cases x with
    | root => simp [leaves, branches] at hx
    | branch n =>
        exact ⟨fun m => leaf n m, fun m => leaf_mem_leaves n m, leafRow_tendsto n⟩
    | leaf n m => exact subset_seqClosure (leaf_mem_leaves n m)

/-- A second application of the same native repair adds the root and exhausts the space. -/
theorem seqClosure_seqClosure_leaves_eq : seqClosure (seqClosure leaves) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  intro x hx
  cases x with
  | root =>
      refine ⟨branch, ?_, branch_tendsto_root⟩
      intro n
      rw [seqClosure_leaves_eq]
      simp [branches]
  | branch n =>
      apply subset_seqClosure
      rw [seqClosure_leaves_eq]
      simp [branches]
  | leaf n m =>
      apply subset_seqClosure
      rw [seqClosure_leaves_eq]
      simp [leaves]

/-- Ordinary closure already sees the whole semantic envelope at stage zero. -/
theorem closure_leaves_eq : closure leaves = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  intro x hx
  have hxS : x ∈ seqClosure (seqClosure leaves) := by
    rw [seqClosure_seqClosure_leaves_eq]
    trivial
  have hxC : x ∈ closure (seqClosure leaves) := seqClosure_subset_closure hxS
  have hxCC : x ∈ closure (closure leaves) :=
    (closure_mono seqClosure_subset_closure) hxC
  simpa only [closure_closure] using hxCC

/-- Ordinary closure remains stationary after the first operational repair. -/
theorem closure_seqClosure_leaves_eq : closure (seqClosure leaves) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← closure_leaves_eq]
  exact closure_mono subset_seqClosure

theorem first_repair_layer : seqClosure leaves \ leaves = branches := by
  rw [seqClosure_leaves_eq]
  ext x
  cases x <;> simp [leaves, branches]

theorem second_repair_layer :
    seqClosure (seqClosure leaves) \ seqClosure leaves = ({root} : Set ArensPoint) := by
  rw [seqClosure_seqClosure_leaves_eq, seqClosure_leaves_eq]
  ext x
  cases x <;> simp [leaves, branches]

/-- The second repair witness is made entirely of outputs born in the first repair layer. -/
theorem hereditary_repair_witness :
    (∀ n, branch n ∈ seqClosure leaves \ leaves) ∧
      Tendsto branch atTop (𝓝 root) := by
  constructor
  · intro n
    rw [first_repair_layer]
    exact branch_mem_branches n
  · exact branch_tendsto_root

/--
Capstone: one native sequential repair generates two strict hereditary layers while ordinary
closure semantics is already stationary.
-/
theorem native_sequential_repair_mechanism :
    seqClosure leaves = leaves ∪ branches ∧
    seqClosure (seqClosure leaves) = Set.univ ∧
    closure leaves = Set.univ ∧
    closure (seqClosure leaves) = Set.univ ∧
    seqClosure leaves \ leaves = branches ∧
    seqClosure (seqClosure leaves) \ seqClosure leaves = ({root} : Set ArensPoint) ∧
    (∀ n, branch n ∈ seqClosure leaves \ leaves) ∧
    Tendsto branch atTop (𝓝 root) ∧
    (∀ x : ℕ → ArensPoint, (∀ k, x k ∈ leaves) → ¬ Tendsto x atTop (𝓝 root)) := by
  exact ⟨seqClosure_leaves_eq, seqClosure_seqClosure_leaves_eq, closure_leaves_eq,
    closure_seqClosure_leaves_eq, first_repair_layer, second_repair_layer,
    hereditary_repair_witness.1, hereditary_repair_witness.2,
    no_leaf_sequence_tendsto_root⟩

end ConstitutiveSequentialRepairHeredity
