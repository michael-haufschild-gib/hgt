import GaloisForLFunctions.HTGeometry.AugmentedSubspaceIso
import GaloisForLFunctions.HTGeometry.ChainSplitting
import Mathlib.LinearAlgebra.Projection

/-!
# The reduced zeroth homology of a two-component space

If a space is the disjoint union of two nonempty path-connected open pieces, its chains split in
every degree, and a `0`-chain of total coefficient zero is a boundary exactly when its component in
the first piece already has total coefficient zero.  The reduced zeroth homology is therefore the
coefficient ring, detected by the total coefficient of that component.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {Y : Type v} [TopologicalSpace Y] (U V : Set Y)
  (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
  (hcover : (Set.univ : Set Y) ⊆ U ∪ V)

/-- The component of a chain in the first piece. -/
noncomputable def compProj (k : ℕ) : (C(topSimplex k, Y) →₀ R) →ₗ[R] (subChains R U k) :=
  Submodule.projectionOnto _ _ (isCompl_subChains R hU hV hdisj hcover k)

theorem compProj_of_mem_left {k : ℕ} {a : C(topSimplex k, Y) →₀ R} (ha : a ∈ subChains R U k) :
    (compProj R U V hU hV hdisj hcover k a : C(topSimplex k, Y) →₀ R) = a := by
  rw [compProj, Submodule.projectionOnto_apply_of_mem_left _ ha]

theorem compProj_of_mem_right {k : ℕ} {b : C(topSimplex k, Y) →₀ R} (hb : b ∈ subChains R V k) :
    (compProj R U V hU hV hdisj hcover k b : C(topSimplex k, Y) →₀ R) = 0 := by
  rw [compProj, Submodule.projectionOnto_apply_of_mem_right _ hb]
  rfl

theorem compProj_add {k : ℕ} {a b : C(topSimplex k, Y) →₀ R} (ha : a ∈ subChains R U k)
    (hb : b ∈ subChains R V k) :
    (compProj R U V hU hV hdisj hcover k (a + b) : C(topSimplex k, Y) →₀ R) = a := by
  rw [map_add, Submodule.coe_add, compProj_of_mem_left R U V hU hV hdisj hcover ha,
    compProj_of_mem_right R U V hU hV hdisj hcover hb, add_zero]

include hU hV hdisj hcover in
theorem exists_split (k : ℕ) (c : C(topSimplex k, Y) →₀ R) :
    ∃ a ∈ subChains R U k, ∃ b ∈ subChains R V k, a + b = c := by
  have hc : c ∈ subChains R U k ⊔ subChains R V k := by
    rw [subChains_sup_eq_top R hU hV hdisj hcover]
    trivial
  exact Submodule.mem_sup.mp hc

theorem sub_compProj_mem {k : ℕ} (c : C(topSimplex k, Y) →₀ R) :
    c - (compProj R U V hU hV hdisj hcover k c : C(topSimplex k, Y) →₀ R) ∈ subChains R V k := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_split R U V hU hV hdisj hcover k c
  rw [compProj_add R U V hU hV hdisj hcover ha hb]
  simpa using hb

end GaloisForLFunctions.HTGeometry
