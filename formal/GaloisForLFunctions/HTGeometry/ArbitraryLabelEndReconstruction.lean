import GaloisForLFunctions.HTGeometry.CoherenceEndReconstruction

/-!
# Arbitrary-label one-ended reconstruction

A label with only finitely many changing edges on a preconnected graph automatically has finite
range: along a walk from a fixed root the value changes only across the finitely many varying
edges, so every value is either the root value or the value at an endpoint of a varying edge.

Consequently the finite-valued hypothesis in `eventuallyConstant_of_finite_edgeVariation` is
redundant on a preconnected graph: the label may take values in an arbitrary type with no
finiteness, order, or algebraic structure.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

universe u

variable {V : Type u}

/-- Along any walk the label stays inside the root value together with the values at endpoints of
varying edges. -/
theorem label_mem_of_walk {α : Type*} {G : SimpleGraph V} (f : V → α)
    {S : Set α} (hroot : ∀ x, f x ∈ f '' edgeEndpointSupport (edgeVariation G f) → f x ∈ S)
    {a b : V} (p : G.Walk a b) (ha : f a ∈ S) : f b ∈ S := by
  induction p with
  | nil => exact ha
  | cons h q ih =>
      rename_i u v w
      by_cases hEq : f u = f v
      · exact ih (hEq ▸ ha)
      · refine ih (hroot v ?_)
        exact ⟨v, Or.inr ⟨(u, v), ⟨h, hEq⟩, rfl⟩, rfl⟩

/-- **Finite edge variation forces a finite label range.**  Preconnectedness is the only structural
input; the label type is arbitrary. -/
theorem finite_range_of_finite_edgeVariation {α : Type*} {G : SimpleGraph V}
    (hconn : G.Preconnected) (f : V → α)
    (hvar : (edgeVariation G f).Finite) (v₀ : V) :
    (Set.range f).Finite := by
  classical
  set S : Set α := insert (f v₀) (f '' edgeEndpointSupport (edgeVariation G f)) with hSdef
  have hSfin : S.Finite :=
    ((edgeEndpointSupport_finite hvar).image f).insert _
  have hsub : Set.range f ⊆ S := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨p⟩ := hconn v₀ v
    refine label_mem_of_walk f (S := S) ?_ p (by simp [hSdef])
    intro x hx
    exact Set.mem_insert_of_mem _ hx
  exact hSfin.subset hsub

/-- **Arbitrary-label one-ended reconstruction.**  On an infinite preconnected graph with the
finite-boundary one-ended property, every label with finitely many changing edges is constant
outside a finite vertex set.  No finiteness or algebraic structure on the label type is assumed. -/
theorem eventuallyConstant_of_finite_edgeVariation_of_preconnected
    {α : Type*} [Infinite V] {G : SimpleGraph V}
    (hconn : G.Preconnected) (hG : FiniteBoundaryOneEnded G) (f : V → α)
    (hvar : (edgeVariation G f).Finite) :
    EventuallyConstant f := by
  classical
  have hne : Nonempty V := inferInstance
  have hrange : (Set.range f).Finite :=
    finite_range_of_finite_edgeVariation hconn f hvar (Classical.arbitrary V)
  haveI : Fintype ↥(Set.range f) := hrange.fintype
  set g : V → ↥(Set.range f) := fun v => ⟨f v, Set.mem_range_self v⟩ with hgdef
  have hgvar : edgeVariation G g = edgeVariation G f := by
    ext e
    simp [edgeVariation, hgdef, Subtype.ext_iff]
  obtain ⟨a, ha⟩ :=
    eventuallyConstant_of_finite_edgeVariation hG g (by rw [hgvar]; exact hvar)
  refine ⟨(a : α), ?_⟩
  have hset : {v | f v ≠ (a : α)} = {v | g v ≠ a} := by
    ext v
    simp [hgdef, Subtype.ext_iff]
  rw [hset]
  exact ha

end GaloisForLFunctions.HTGeometry
