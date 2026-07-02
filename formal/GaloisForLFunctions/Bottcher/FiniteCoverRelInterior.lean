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

/-- **Modulus-one pigeonhole.**  If every point of a closed nonempty `S ⊆ ℂ` lands on the
modulus-one locus `{‖g_i‖ = 1}` of one of finitely many continuous functions `g_i`, then some
single `{‖g_i‖ = 1}` contains a nonempty relatively open piece of `S`.  This is the bridge from the
root-limit lemma (every frontier point carries a modulus-one branch value) to a relatively open
Julia arc lying in one smooth curve.  Direct Baire pigeonhole on the closed loci. -/
theorem exists_relOpen_subset_modulus_one {S : Set ℂ} (hScl : IsClosed S) (hSne : S.Nonempty)
    {ι : Type*} [Finite ι] (g : ι → ℂ → ℂ) (hg : ∀ i, Continuous (g i))
    (hcov : ∀ w ∈ S, ∃ i, ‖g i w‖ = 1) :
    ∃ i, ∃ U : Set ℂ, IsOpen U ∧ (U ∩ S).Nonempty ∧ ∀ w ∈ U ∩ S, ‖g i w‖ = 1 := by
  classical
  set F : ι → Set ℂ := fun i => {w : ℂ | ‖g i w‖ = 1} with hFdef
  have hFcl : ∀ i, IsClosed (F i) := fun i =>
    isClosed_eq ((hg i).norm) continuous_const
  have hcov' : S ⊆ ⋃ i, F i := by
    intro w hw
    obtain ⟨i, hi⟩ := hcov w hw
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i, U, hUo, hUSne, hUSsub⟩ :=
    exists_relOpen_subset_of_finite_closed_cover hScl hSne F hFcl hcov'
  exact ⟨i, U, hUo, hUSne, fun w hw => hUSsub hw⟩

end Bottcher
