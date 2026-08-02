import GaloisForLFunctions.RHTower.DeningerFinestNuclear
import GaloisForLFunctions.RHTower.DeningerLocallyConstantTestSpace

/-!
# Subspaces of a countable-dimensional space are nuclear for the restricted finest topology

A subspace of a vector space is a direct summand, so a seminorm on it extends to the whole space by
composing with the projection.  The restrictions of all seminorms of the ambient space are
therefore all the seminorms of the subspace, and a subspace of a countable-dimensional space is
countable-dimensional, so the restricted family is nuclear — in the uncompleted sense, which is
what makes the subspace usable as a tensor factor.

* `deningerSeminorm_extend` : a seminorm on a subspace extends.
* `deningerIsNuclearSpace_finest_subspace` : **a subspace of a countable-dimensional space is
  nuclear.**
* `deningerTestSubspace_isNuclearSpace` : the same for subspaces of the locally constant test
  space.
-/

namespace RHTower

section SubspaceExtension

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **A seminorm on a subspace extends to the whole space**, by composing with the projection onto
a complement. -/
theorem deningerSeminorm_extend (F : Submodule 𝕜 E) (q : Seminorm 𝕜 F) :
    ∃ p : Seminorm 𝕜 E, ∀ v : F, q v = p (v : E) := by
  obtain ⟨G, hG⟩ := F.exists_isCompl
  refine ⟨q.comp (F.projectionOnto G hG), fun v => ?_⟩
  show q v = q (F.projectionOnto G hG (v : E))
  rw [Submodule.projectionOnto_apply_left hG v]

/-- **The restricted seminorms of a subspace are all of its seminorms.** -/
theorem deningerRestrictSeminorm_dominating (F : Submodule 𝕜 E) (q : Seminorm 𝕜 F) :
    ∃ (p : Seminorm 𝕜 E) (C : ℝ), ∀ v : F, q v ≤ C * deningerRestrictSeminorm F p v := by
  obtain ⟨p, hp⟩ := deningerSeminorm_extend F q
  refine ⟨p, 1, fun v => ?_⟩
  rw [one_mul]
  exact le_of_eq (hp v)

variable [CompleteSpace 𝕜]

/-- **A subspace of a countable-dimensional space is nuclear** for the restricted finest locally
convex topology, in the uncompleted sense. -/
theorem deningerIsNuclearSpace_finest_subspace (hE : Module.rank 𝕜 E ≤ Cardinal.aleph0)
    (F : Submodule 𝕜 E) :
    DeningerIsNuclearSpace (fun p : Seminorm 𝕜 E => deningerRestrictSeminorm F p) := by
  classical
  obtain ⟨s, ⟨bF⟩⟩ := Module.Basis.exists_basis 𝕜 F
  haveI : Countable s := by
    rw [← Cardinal.mk_le_aleph0_iff, bF.mk_eq_rank'']
    exact le_trans F.rank_le hE
  refine deningerIsNuclearSpace_of_dominating (fun q : Seminorm 𝕜 F => q)
    (fun p : Seminorm 𝕜 E => deningerRestrictSeminorm F p) ?_ ?_
    (deningerIsNuclearSpace_finest_of_countable bF)
  · intro p
    exact ⟨deningerRestrictSeminorm F p, 1, fun v => by rw [one_mul]⟩
  · intro q
    exact deningerRestrictSeminorm_dominating F q

end SubspaceExtension

section TestSubspace

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]

/-- **Every subspace of the locally constant test space is nuclear** in the uncompleted sense. -/
theorem deningerTestSubspace_isNuclearSpace (F : Submodule ℝ (DeningerTestSpace Y)) :
    DeningerIsNuclearSpace
      (fun p : Seminorm ℝ (DeningerTestSpace Y) => deningerRestrictSeminorm F p) := by
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℝ (deningerTestIndicators Y)
  haveI : Countable b := (deningerTestIndicators_countable.mono hbS).to_subtype
  have hbasis : Module.Basis b ℝ (DeningerTestSpace Y) := by
    refine Module.Basis.mk hli ?_
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hspan, deningerTestIndicators_span]
  refine deningerIsNuclearSpace_finest_subspace ?_ F
  rw [← hbasis.mk_eq_rank'']
  exact Cardinal.mk_le_aleph0_iff.mpr ‹Countable b›

end TestSubspace

end RHTower
