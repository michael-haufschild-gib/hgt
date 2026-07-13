import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Clopen
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Small inductive dimension

Mathlib has no topological dimension theory.  The finite Bohr-rank conclusion of the finite-phase
theorem (eq. 9) needs it: the joint hull embeds in `ℂ^N`, hence has finite topological dimension,
hence (Pontryagin) finite character rank.  This file begins the theory by defining the **small
inductive dimension** `ind` and proving its foundational laws.

`SmallIndDimLE X n` reads `ind X ≤ n` for `n : ℕ` (the empty space has `ind = -1`, so it satisfies
`SmallIndDimLE _ n` for every `n`).  The definition is Menger–Urysohn's recursion: `ind X ≤ n+1`
iff every point has arbitrarily small neighbourhoods whose topological frontier has `ind ≤ n`.

Established here: the empty space is `≤ n` for all `n`; the bound is monotone in `n`.  The remaining
targets (`ind ℝ^N ≤ N`, subspace monotonicity, and the Pontryagin `dim = character-rank` bridge) are
the load-bearing pieces still under construction.
-/

namespace GaloisForLFunctions

/-- `SmallIndDimLE X n` : the small inductive dimension of `X` is at most `n`.  Menger–Urysohn
recursion: at level `0`, every neighbourhood contains a neighbourhood with empty frontier (a clopen
neighbourhood basis); at level `n+1`, one with frontier of small inductive dimension `≤ n`. -/
def SmallIndDimLE (X : Type*) [TopologicalSpace X] : ℕ → Prop
  | 0 => ∀ (x : X) (U : Set X), U ∈ nhds x → ∃ V ∈ nhds x, V ⊆ U ∧ frontier V = ∅
  | (n + 1) => ∀ (x : X) (U : Set X), U ∈ nhds x →
      ∃ V ∈ nhds x, V ⊆ U ∧ SmallIndDimLE (frontier V) n

/-- The empty space has small inductive dimension `-1 ≤ n` for every `n`: the defining condition is
vacuous over an empty point set. -/
theorem smallIndDimLE_of_isEmpty (X : Type*) [TopologicalSpace X] [IsEmpty X] (n : ℕ) :
    SmallIndDimLE X n := by
  cases n <;> exact fun x => isEmptyElim x

/-- The dimension bound is monotone: `ind X ≤ n` implies `ind X ≤ n+1`. -/
theorem SmallIndDimLE.succ {X : Type*} [TopologicalSpace X] {n : ℕ} :
    SmallIndDimLE X n → SmallIndDimLE X (n + 1) := by
  induction n generalizing X with
  | zero =>
      intro h x U hU
      obtain ⟨V, hVnhds, hVU, hVfront⟩ := h x U hU
      refine ⟨V, hVnhds, hVU, ?_⟩
      have : IsEmpty (frontier V) := by rw [hVfront]; exact Set.isEmpty_coe_sort.mpr rfl
      exact smallIndDimLE_of_isEmpty _ 0
  | succ n ih =>
      intro h x U hU
      obtain ⟨V, hVnhds, hVU, hVfront⟩ := h x U hU
      exact ⟨V, hVnhds, hVU, ih hVfront⟩

/-- Consequently the bound is monotone along `≤`. -/
theorem SmallIndDimLE.mono {X : Type*} [TopologicalSpace X] {m n : ℕ}
    (h : SmallIndDimLE X m) (hmn : m ≤ n) : SmallIndDimLE X n := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact ih.succ

/-- A discrete space is zero-dimensional: singletons are a clopen neighbourhood basis, so every
neighbourhood contains one with empty frontier.  This is the base case of the inductive climb to
`ind ℝ^N ≤ N` (frontiers of boxes drop one dimension, bottoming out at discrete point sets). -/
theorem smallIndDimLE_zero_of_discrete (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    SmallIndDimLE X 0 := by
  intro x U hU
  refine ⟨{x}, (isOpen_discrete _).mem_nhds (Set.mem_singleton x),
    Set.singleton_subset_iff.mpr (mem_of_mem_nhds hU), ?_⟩
  exact IsClopen.frontier_eq ⟨isClosed_discrete _, isOpen_discrete _⟩

/-- **The real line is one-dimensional: `ind ℝ ≤ 1`.**  Every neighbourhood of a point contains an
open interval, whose topological frontier is the two-point set `{a, b}` — a discrete (hence
zero-dimensional) subspace.  This is the first rung of `ind ℝ^N ≤ N`. -/
theorem smallIndDimLE_real_le_one : SmallIndDimLE ℝ 1 := by
  intro x U hU
  obtain ⟨a, b, hxab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hU
  refine ⟨Set.Ioo a b, Ioo_mem_nhds hxab.1 hxab.2, hsub, ?_⟩
  rw [frontier_Ioo (hxab.1.trans hxab.2)]
  exact smallIndDimLE_zero_of_discrete _

end GaloisForLFunctions
