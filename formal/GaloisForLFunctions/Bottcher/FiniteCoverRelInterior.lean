/-
# Baire pigeonhole: a finite closed cover of a closed set has a member with relative interior (P4)

A closed nonempty set `S ⊆ ℂ` is a complete metric space, hence a Baire space.  If finitely many
closed sets cover `S`, one of them contains a nonempty relatively open subset of `S` — a set of the
form `U ∩ S` with `U` open in `ℂ`.  This is the pigeonhole step of the root-limit connected-case
route: the finitely many "modulus-one branch" loci cover a perfect Julia piece, so one of them has
relative interior, giving a relatively open Julia arc inside a single smooth curve.  Axiom-clean.
-/
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Analysis.Complex.Basic

open Set Topology

namespace Bottcher

/-- **Finite-cover relative interior (Baire).**  For a closed nonempty `S ⊆ ℂ` covered by finitely
many closed sets `F i`, some `F i` contains a nonempty relatively open subset `U ∩ S` of `S`. -/
theorem exists_relOpen_subset_of_finite_closed_cover {S : Set ℂ}
    (hScl : IsClosed S) (hSne : S.Nonempty)
    {ι : Type*} [Finite ι] (F : ι → Set ℂ) (hFcl : ∀ i, IsClosed (F i))
    (hcov : S ⊆ ⋃ i, F i) :
    ∃ i, ∃ U : Set ℂ, IsOpen U ∧ (U ∩ S).Nonempty ∧ U ∩ S ⊆ F i := by
  classical
  haveI hcomplete : CompleteSpace S := hScl.completeSpace_coe
  haveI : Nonempty S := hSne.to_subtype
  -- pull the cover back to the subtype
  set G : ι → Set S := fun i => Subtype.val ⁻¹' F i with hGdef
  have hGcl : ∀ i, IsClosed (G i) := fun i => (hFcl i).preimage continuous_subtype_val
  have hGcov : ⋃ i, G i = univ := by
    rw [eq_univ_iff_forall]
    intro x
    have hx : (x : ℂ) ∈ ⋃ i, F i := hcov x.2
    rw [mem_iUnion] at hx ⊢
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, hi⟩
  obtain ⟨i, hint⟩ := nonempty_interior_of_iUnion_of_closed hGcl hGcov
  obtain ⟨x, hx⟩ := hint
  -- an interior point of `G i` in the subtype gives an ambient open witness
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_interior.mp hx
  obtain ⟨U, hUo, hUeq⟩ := isOpen_induced_iff.mp hVo
  refine ⟨i, U, hUo, ⟨(x : ℂ), ?_, x.2⟩, ?_⟩
  · have : x ∈ Subtype.val ⁻¹' U := by rw [hUeq]; exact hxV
    exact this
  · rintro z ⟨hzU, hzS⟩
    have hz' : (⟨z, hzS⟩ : S) ∈ V := by rw [← hUeq]; exact hzU
    exact hVsub hz'

end Bottcher
