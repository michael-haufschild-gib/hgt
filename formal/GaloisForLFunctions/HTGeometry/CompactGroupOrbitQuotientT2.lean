import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.IsClosedRestrict

/-!
# The orbit space of a compact group action is Hausdorff

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), the input to
Corollary 7.9 (`t89n`) for the quotients `X̂₀ (C)` and `X̌₀ (C)`.

Mathlib deduces Hausdorffness of an orbit space from properness of the action.  A compact group
acting continuously on a Hausdorff space acts properly, but this instance is not in mathlib; the
statement is proved here directly.  The orbit relation is the image of the closed set
`{(g, x, y) | g • x = y}` under the projection `G × (X × X) → X × X`, which is a closed map because
`G` is compact; and the quotient map of a group action is an open quotient map, so a closed orbit
relation makes the quotient Hausdorff.
-/

namespace HTGeometry

open MulAction Set

variable {G Z : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
  [TopologicalSpace Z] [T2Space Z] [MulAction G Z] [ContinuousSMul G Z]

/-- The orbit relation of a compact group acting continuously on a Hausdorff space is closed. -/
theorem isClosed_orbitRel_of_compactSpace :
    IsClosed {p : Z × Z | ∃ g : G, g • p.1 = p.2} := by
  have hS : IsClosed {q : G × (Z × Z) | q.1 • q.2.1 = q.2.2} := by
    refine isClosed_eq ?_ ?_
    · exact continuous_smul.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    · exact continuous_snd.comp continuous_snd
  have himg : (Prod.snd : G × (Z × Z) → Z × Z) '' {q : G × (Z × Z) | q.1 • q.2.1 = q.2.2}
      = {p : Z × Z | ∃ g : G, g • p.1 = p.2} := by
    ext p
    constructor
    · rintro ⟨⟨g, q⟩, hq, rfl⟩
      exact ⟨g, hq⟩
    · rintro ⟨g, hg⟩
      exact ⟨⟨g, p⟩, hg, rfl⟩
  rw [← himg]
  exact isClosedMap_snd_of_compactSpace _ hS

/-- **A compact group acting continuously on a Hausdorff space has Hausdorff orbit space.** -/
theorem t2Space_orbitQuotient_of_compactSpace :
    T2Space (orbitRel.Quotient G Z) := by
  rw [t2_iff_isClosed_diagonal]
  have hopen : IsOpenQuotientMap
      (Prod.map (Quotient.mk (orbitRel G Z)) (Quotient.mk (orbitRel G Z))) :=
    MulAction.isOpenQuotientMap_quotientMk.prodMap MulAction.isOpenQuotientMap_quotientMk
  rw [← hopen.isQuotientMap.isClosed_preimage]
  have hpre : (Prod.map (Quotient.mk (orbitRel G Z)) (Quotient.mk (orbitRel G Z))) ⁻¹'
      (Set.diagonal (orbitRel.Quotient G Z)) = {p : Z × Z | ∃ g : G, g • p.1 = p.2} := by
    ext ⟨x, y⟩
    simp only [Set.mem_preimage, Prod.map_apply, Set.mem_diagonal_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      obtain ⟨g, hg⟩ := Quotient.exact h
      refine ⟨g⁻¹, ?_⟩
      show g⁻¹ • x = y
      rw [← hg]
      exact inv_smul_smul g y
    · rintro ⟨g, hg⟩
      refine Quotient.sound ⟨g⁻¹, ?_⟩
      show g⁻¹ • y = x
      rw [← hg]
      exact inv_smul_smul g x
  rw [hpre]
  exact isClosed_orbitRel_of_compactSpace

end HTGeometry
