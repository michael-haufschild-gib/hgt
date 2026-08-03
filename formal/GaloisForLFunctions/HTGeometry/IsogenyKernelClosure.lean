import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Maps.Basic

/-!
# Iterated isogeny kernels and their closed envelope

For an additive endomorphism `alpha`, this module constructs the increasing union of the kernels
of all iterates.  It proves that this union is invariant under pullback by `alpha`, and that its
topological closure remains invariant whenever `alpha` is open and continuous.  The latter is the
abstract topological argument behind invariance of the Zariski closure of an isogeny-torsion union.
-/

open scoped Classical

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- The `n`-fold iterate of an additive endomorphism, kept in the ordinary hom type. -/
def additiveIterate (alpha : G →+ G) : ℕ → G →+ G
  | 0 => AddMonoidHom.id G
  | n + 1 => (additiveIterate alpha n).comp alpha

@[simp]
theorem additiveIterate_zero_apply (alpha : G →+ G) (x : G) :
    additiveIterate alpha 0 x = x := rfl

@[simp]
theorem additiveIterate_succ_apply (alpha : G →+ G) (n : ℕ) (x : G) :
    additiveIterate alpha (n + 1) x = additiveIterate alpha n (alpha x) := rfl

theorem additiveIterate_succ_apply' (alpha : G →+ G) (n : ℕ) (x : G) :
    additiveIterate alpha (n + 1) x = alpha (additiveIterate alpha n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [additiveIterate_succ_apply, ih, additiveIterate_succ_apply]

theorem additiveIterate_add_apply (alpha : G →+ G) (m n : ℕ) (x : G) :
    additiveIterate alpha (m + n) x =
      additiveIterate alpha m (additiveIterate alpha n x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, additiveIterate_succ_apply, additiveIterate_succ_apply, ih]

/-- Increasing union of kernels of all iterates of an additive endomorphism. -/
def iteratedKernelUnion (alpha : G →+ G) : AddSubgroup G :=
  ⨆ n : ℕ, (additiveIterate alpha n).ker

private theorem iteratedKernel_directed (alpha : G →+ G) :
    Directed (· ≤ ·) (fun n : ℕ => (additiveIterate alpha n).ker) := by
  intro m n
  refine ⟨max m n, ?_, ?_⟩
  · intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_max_left m n)
    rw [hk, Nat.add_comm, additiveIterate_add_apply, hx, map_zero]
  · intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_max_right m n)
    rw [hk, Nat.add_comm, additiveIterate_add_apply, hx, map_zero]

theorem mem_iteratedKernelUnion_iff (alpha : G →+ G) (x : G) :
    x ∈ iteratedKernelUnion alpha ↔ ∃ n : ℕ, additiveIterate alpha n x = 0 := by
  rw [iteratedKernelUnion, AddSubgroup.mem_iSup_of_directed (iteratedKernel_directed alpha)]
  constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, hn⟩

/-- Pulling the union of all iterated kernels back through the endomorphism changes nothing. -/
theorem iteratedKernelUnion_comap (alpha : G →+ G) :
    (iteratedKernelUnion alpha).comap alpha = iteratedKernelUnion alpha := by
  ext x
  rw [AddSubgroup.mem_comap, mem_iteratedKernelUnion_iff, mem_iteratedKernelUnion_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, hn⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← additiveIterate_succ_apply, additiveIterate_succ_apply', hn, map_zero]

variable [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- If an endomorphism is open and continuous, its iterated-kernel closure is fully invariant. -/
theorem iteratedKernelUnion_topologicalClosure_comap
    (alpha : G →+ G) (hopen : IsOpenMap alpha) (hcont : Continuous alpha) :
    (iteratedKernelUnion alpha).topologicalClosure.comap alpha =
      (iteratedKernelUnion alpha).topologicalClosure := by
  ext x
  change alpha x ∈ closure (iteratedKernelUnion alpha : Set G) ↔
    x ∈ closure (iteratedKernelUnion alpha : Set G)
  have hpre := hopen.preimage_closure_eq_closure_preimage hcont
    (iteratedKernelUnion alpha : Set G)
  rw [← Set.mem_preimage, hpre]
  have hset : alpha ⁻¹' (iteratedKernelUnion alpha : Set G) =
      (iteratedKernelUnion alpha : Set G) := by
    ext y
    exact SetLike.ext_iff.mp (iteratedKernelUnion_comap alpha) y
  rw [hset]

end

end GaloisForLFunctions.HTGeometry
