import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Irreducible

/-!
# An irreducibility criterion for topological groups

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), the reduction step in
the proof of Proposition 10.3.

Because left translation is a homeomorphism, every nonempty open set of a topological group is a
translate of a neighbourhood of the identity.  Hence the group is irreducible as a topological
space as soon as every neighbourhood of the identity meets each of its translates.  This is the
step by which Deninger reduces the irreducibility of `Q^{>0}₀ \ (Ẑ^× × ℝ^{>0})` to an explicit
approximation statement about the adele topology.
-/

namespace HTGeometry

open Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Deninger, Proposition 10.3, the reduction step.**  A topological group is irreducible as a
topological space as soon as every neighbourhood of the identity meets each of its translates:
two nonempty open sets are translates of neighbourhoods of the identity. -/
theorem isPreirreducible_univ_of_nhds_one
    (h : ∀ U ∈ nhds (1 : G), ∀ g : G, (U ∩ g • U).Nonempty) :
    IsPreirreducible (Set.univ : Set G) := by
  rintro u v hu hv ⟨x₁, -, hx₁⟩ ⟨x₂, -, hx₂⟩
  have hu' : IsOpen (x₁⁻¹ • u) := hu.smul _
  have hv' : IsOpen (x₂⁻¹ • v) := hv.smul _
  have h1u : (1 : G) ∈ x₁⁻¹ • u := by
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simpa using hx₁
  have h1v : (1 : G) ∈ x₂⁻¹ • v := by
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simpa using hx₂
  have hU : (x₁⁻¹ • u) ∩ (x₂⁻¹ • v) ∈ nhds (1 : G) :=
    Filter.inter_mem (hu'.mem_nhds h1u) (hv'.mem_nhds h1v)
  obtain ⟨y, hy, hy'⟩ := h _ hU (x₁⁻¹ * x₂)
  obtain ⟨z, hz, hzy⟩ := hy'
  refine ⟨x₁ * y, Set.mem_univ _, ?_, ?_⟩
  · have := hy.1
    rw [Set.mem_smul_set_iff_inv_smul_mem] at this
    simpa using this
  · have hz2 := hz.2
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hz2
    have hzval : x₂ * z = x₁ * y := by
      rw [← hzy]
      show x₂ * z = x₁ * ((x₁⁻¹ * x₂) * z)
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    have : x₂ * z ∈ v := by simpa using hz2
    rwa [hzval] at this

/-- **Deninger, Proposition 10.3, the reduction step.**  The corresponding statement for the
space itself. -/
theorem preirreducibleSpace_of_nhds_one
    (h : ∀ U ∈ nhds (1 : G), ∀ g : G, (U ∩ g • U).Nonempty) :
    PreirreducibleSpace G :=
  ⟨isPreirreducible_univ_of_nhds_one h⟩

/-- **Deninger, Proposition 10.3, the reduction step.**  A nonempty topological group all of whose
identity neighbourhoods meet their translates is irreducible. -/
theorem irreducibleSpace_of_nhds_one
    (h : ∀ U ∈ nhds (1 : G), ∀ g : G, (U ∩ g • U).Nonempty) :
    IrreducibleSpace G := by
  haveI : Nonempty G := ⟨1⟩
  haveI := preirreducibleSpace_of_nhds_one h
  constructor
  exact ⟨1⟩

end HTGeometry
