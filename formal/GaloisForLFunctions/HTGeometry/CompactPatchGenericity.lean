import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Genericity against an uncountable parameter, by compact patches

A freeness predicate typically quantifies over an uncountable family — for translation orbits, over
all configurations of distinct shifts.  Baire does not apply to an uncountable intersection, so the
naive route fails.

The repair is to group the parameter into compact patches.  Over a compact patch the good set is not
merely dense but *open*: this is the tube lemma, since nonvanishing at every point of a compact set
persists under small perturbation of the other variable.  Countably many compact patches exhausting
the parameter then give countably many open dense sets, and Baire intersects them.

Nothing here is specific to Cauchy jets; the input is joint continuity and compactness of each patch.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- **Nonvanishing over a compact patch is an open condition.**  If the test function is jointly
continuous at each point of the patch, the parameters at which it avoids zero on all of that patch
form an open set.  Only pointwise joint continuity along the patch is needed, not global
continuity. -/
theorem isOpen_setOf_forall_mem_compact_ne_zero
    {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace E] [T1Space E] [Zero E]
    {K : Set Y} (hK : IsCompact K)
    (g : X → Y → E)
    (hg : ∀ x : X, ∀ y ∈ K, ContinuousAt (fun p : X × Y => g p.1 p.2) (x, y)) :
    IsOpen {x : X | ∀ y ∈ K, g x y ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  apply hK.eventually_forall_of_forall_eventually
  intro y hy
  have hne : g x₀ y ≠ 0 := hx₀ y hy
  exact hg x₀ y hy (isOpen_compl_singleton.mem_nhds hne)

/-- **Countable compact exhaustion gives a dense good set.**  If nonvanishing is dense over each of
countably many compact patches, then in a Baire space it is dense over their union. -/
theorem dense_setOf_forall_mem_iUnion_compact_ne_zero
    {X Y E : Type*} [TopologicalSpace X] [BaireSpace X] [TopologicalSpace Y]
    [TopologicalSpace E] [T1Space E] [Zero E]
    (K : ℕ → Set Y) (hK : ∀ m, IsCompact (K m))
    (g : X → Y → E)
    (hg : ∀ m, ∀ x : X, ∀ y ∈ K m,
      ContinuousAt (fun p : X × Y => g p.1 p.2) (x, y))
    (hdense : ∀ m, Dense {x : X | ∀ y ∈ K m, g x y ≠ 0}) :
    Dense {x : X | ∀ y ∈ ⋃ m, K m, g x y ≠ 0} := by
  have hopen : ∀ m, IsOpen {x : X | ∀ y ∈ K m, g x y ≠ 0} :=
    fun m => isOpen_setOf_forall_mem_compact_ne_zero (hK m) g (hg m)
  have hinter := dense_iInter_of_isOpen hopen hdense
  have hset : (⋂ m, {x : X | ∀ y ∈ K m, g x y ≠ 0}) =
      {x : X | ∀ y ∈ ⋃ m, K m, g x y ≠ 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro h y ⟨m, hm⟩
      exact h m y hm
    · intro h m y hy
      exact h y ⟨m, hy⟩
  rwa [hset] at hinter

/-- Specialization to a full exhaustion: if the compact patches cover the parameter space, the good
set is dense without any restriction on the parameter. -/
theorem dense_setOf_forall_ne_zero_of_compactExhaustion
    {X Y E : Type*} [TopologicalSpace X] [BaireSpace X] [TopologicalSpace Y]
    [TopologicalSpace E] [T1Space E] [Zero E]
    (K : ℕ → Set Y) (hK : ∀ m, IsCompact (K m)) (hcover : (⋃ m, K m) = Set.univ)
    (g : X → Y → E)
    (hg : ∀ m, ∀ x : X, ∀ y ∈ K m,
      ContinuousAt (fun p : X × Y => g p.1 p.2) (x, y))
    (hdense : ∀ m, Dense {x : X | ∀ y ∈ K m, g x y ≠ 0}) :
    Dense {x : X | ∀ y, g x y ≠ 0} := by
  have hmain := dense_setOf_forall_mem_iUnion_compact_ne_zero K hK g hg hdense
  have hset : {x : X | ∀ y ∈ ⋃ m, K m, g x y ≠ 0} =
      {x : X | ∀ y, g x y ≠ 0} := by
    ext x
    rw [hcover]
    simp
  rwa [hset] at hmain

end

end GaloisForLFunctions.HTGeometry
