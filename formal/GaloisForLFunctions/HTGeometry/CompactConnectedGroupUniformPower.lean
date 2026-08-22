import Mathlib

/-!
# Uniform finite powers in compact connected groups

An open, inversion-stable neighbourhood of the identity in a compact connected topological group
has a bounded word length: one fixed finite power is the whole group.  This is the compactness
step used to turn a local exponential chart into a finite global product chart.
-/

open Set Topology
open scoped Pointwise

namespace GaloisForLFunctions.HTGeometry

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ConnectedSpace G] [CompactSpace G]

/-- A symmetric open identity neighbourhood in a compact connected topological group has a
single finite power equal to the entire group. -/
theorem exists_pow_eq_univ_of_compact_connected
    {O : Set G} (hopen : IsOpen O) (hone : 1 ∈ O) (hinv : O⁻¹ = O) :
    ∃ N : ℕ, O ^ N = Set.univ := by
  classical
  let H : Subgroup G := {
    carrier := ⋃ n : ℕ, O ^ (n + 1)
    mul_mem' := fun ha hb => by
      rcases mem_iUnion.mp ha with ⟨k, hk⟩
      rcases mem_iUnion.mp hb with ⟨l, hl⟩
      apply mem_iUnion.mpr
      use k + 1 + l
      rw [add_assoc, pow_add]
      exact Set.mul_mem_mul hk hl
    one_mem' := by
      apply mem_iUnion.mpr
      use 0
      simpa using hone
    inv_mem' := fun ha => by
      rcases mem_iUnion.mp ha with ⟨k, hk⟩
      apply mem_iUnion.mpr
      use k
      rw [← hinv]
      simpa only [inv_pow, Set.mem_inv, inv_inv] using hk }
  have hpowOpen : ∀ n : ℕ, IsOpen (O ^ (n + 1)) := fun n => by
    rw [pow_succ]
    exact hopen.mul_left
  have hHopen : IsOpen (H : Set G) := by
    change IsOpen (⋃ n : ℕ, O ^ (n + 1))
    exact isOpen_iUnion hpowOpen
  have hHne : (H : Set G).Nonempty := ⟨1, H.one_mem⟩
  have hHeq : (H : Set G) = Set.univ :=
    (isClopen_iff.mp ⟨H.isClosed_of_isOpen hHopen, hHopen⟩).resolve_left hHne.ne_empty
  have hcover : (Set.univ : Set G) ⊆ ⋃ n : ℕ, O ^ (n + 1) := by
    rw [← hHeq]
    exact Set.Subset.rfl
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun n : ℕ => O ^ (n + 1)) hpowOpen hcover
  refine ⟨s.sup id + 1, Set.eq_univ_of_forall fun x => ?_⟩
  obtain ⟨n, hn, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact (pow_subset_pow_right hone (Nat.succ_le_succ (Finset.le_sup hn))) hx

end GaloisForLFunctions.HTGeometry
