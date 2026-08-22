/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 3.6
(`t37n`), mechanism.

The proof of Proposition 3.6 rests on one topological principle: a continuous character of a
linearly topologized group — one with a neighbourhood basis of the identity consisting of open
subgroups — into a group with **no small subgroups** has open kernel, because the image of a small
enough open subgroup is a subgroup inside the distinguished neighbourhood and therefore trivial.
That principle is isolated here.
-/
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

namespace RHTower

/-- **No small subgroups.**  A topological group has no small subgroups if some neighbourhood of
the identity contains no nontrivial subgroup.  The unit group of the complex numbers is the
motivating example. -/
def DeningerNoSmallSubgroups (C : Type*) [Group C] [TopologicalSpace C] : Prop :=
  ∃ U ∈ nhds (1 : C), ∀ H : Subgroup C, (H : Set C) ⊆ U → H = ⊥

/-- **Deninger, Proposition 3.6, mechanism.**  A continuous character of a linearly topologized
group into a group with no small subgroups has open kernel: some open subgroup is mapped into the
small neighbourhood, hence to `1`. -/
theorem deningerIsOpen_ker_of_noSmallSubgroups {T C : Type*} [Group T] [TopologicalSpace T]
    [ContinuousMul T] [Group C] [TopologicalSpace C]
    (hbasis : ∀ V ∈ nhds (1 : T), ∃ H : Subgroup T, IsOpen (H : Set T) ∧ (H : Set T) ⊆ V)
    (hns : DeningerNoSmallSubgroups C) (α : T →* C) (hα : Continuous α) :
    IsOpen ((α.ker : Subgroup T) : Set T) := by
  obtain ⟨U, hU, hUsub⟩ := hns
  have hpre : α ⁻¹' U ∈ nhds (1 : T) := by
    refine hα.continuousAt.preimage_mem_nhds ?_
    rwa [map_one]
  obtain ⟨H, hHopen, hHsub⟩ := hbasis _ hpre
  have hmap : H.map α = ⊥ := by
    refine hUsub _ ?_
    rintro _ ⟨t, ht, rfl⟩
    exact hHsub ht
  have hle : H ≤ α.ker := by
    intro t ht
    have : α t ∈ H.map α := ⟨t, ht, rfl⟩
    rw [hmap] at this
    simpa [MonoidHom.mem_ker] using this
  -- a subgroup containing an open subgroup is open
  refine isOpen_iff_forall_mem_open.2 fun t ht => ?_
  refine ⟨(fun s => t * s) '' (H : Set T), ?_, (Homeomorph.mulLeft t).isOpenMap (H : Set T) hHopen, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact (α.ker).mul_mem ht (hle hs)
  · exact ⟨1, H.one_mem, mul_one t⟩

end RHTower
