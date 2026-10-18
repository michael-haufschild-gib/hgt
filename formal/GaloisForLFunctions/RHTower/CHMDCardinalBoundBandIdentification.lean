import GaloisForLFunctions.RHTower.CHMDProjectedCardinalSpanning
import GaloisForLFunctions.RHTower.CHMDBoundStateInertia

/-!
# Identification of the projected-cardinal bound band

The closed span of actual projected divisor-cardinal packets is exactly the primitive part of the existing resolvent bound-state space. No finiteness of off-line zeros is assumed.
-/

set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section


namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump

local instance : CompleteSpace primitiveSector := isClosed_primitiveSector.completeSpace_coe

theorem openBoundStateBand_le_primitive_boundStateSpace :
    openBoundStateBand ≤ boundStateSpace ⊓ primitiveSector := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro w ⟨μ, hμ, hμ1, hw⟩
    exact ⟨mem_boundStateSpace_of_eigen hμ hw,
      mem_primitiveSector.mpr (inner_oneL_eq_zero_of_eigenvector hμ1.ne hw)⟩
  · exact isClosed_boundStateSpace.inter isClosed_primitiveSector

private theorem primitive_projection_oneL : primitiveSector.starProjection oneL = 0 := by
  apply (Submodule.starProjection_apply_eq_zero_iff (K := primitiveSector)).mpr
  change oneL ∈ (ℝ ∙ oneL)ᗮᗮ
  exact Submodule.le_orthogonal_orthogonal (ℝ ∙ oneL) (Submodule.subset_span
    (show oneL ∈ ({oneL} : Set MassSpace) from rfl))

theorem primitiveProjection_mem_openBoundStateBand {w : MassSpace}
    (hw : w ∈ boundStateSpace) : primitiveSector.starProjection w ∈ openBoundStateBand := by
  have hspan : Submodule.span ℝ {v : MassSpace | ∃ μ : ℝ,
      1 / 2 < μ ∧ resolvent v = μ • v} ≤
      openBoundStateBand.comap primitiveSector.starProjection.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro v ⟨μ, hμ, hv⟩
    change primitiveSector.starProjection v ∈ openBoundStateBand
    by_cases hμ1 : μ = 1
    · subst μ
      rw [one_smul] at hv
      rw [eq_smul_oneL_of_resolvent_eq hv, map_smul, primitive_projection_oneL, smul_zero]
      exact openBoundStateBand.zero_mem
    · have hp : v ∈ primitiveSector :=
        mem_primitiveSector.mpr (inner_oneL_eq_zero_of_eigenvector hμ1 hv)
      rw [Submodule.starProjection_eq_self_iff.mpr hp]
      by_cases hv0 : v = 0
      · simpa only [hv0] using openBoundStateBand.zero_mem
      · exact Submodule.le_topologicalClosure _ (Submodule.subset_span
          ⟨μ, hμ, eigenvalue_lt_one_of_primitive hv0 (mem_primitiveSector.mp hp) hv, hv⟩)
  exact Submodule.topologicalClosure_minimal _ hspan
    (isClosed_openBoundStateBand.preimage primitiveSector.starProjection.continuous) hw

/-- Exact identification with the repository's original closed primitive bound-state sector. -/
theorem openBoundStateBand_eq_primitive_boundStateSpace :
    openBoundStateBand = boundStateSpace ⊓ primitiveSector := by
  apply le_antisymm openBoundStateBand_le_primitive_boundStateSpace
  intro w hw
  have h := primitiveProjection_mem_openBoundStateBand hw.1
  rwa [Submodule.starProjection_eq_self_iff.mpr hw.2] at h

/-- Literal arithmetic cardinal packets synthesize the entire existing open-band receiver. -/
theorem closed_span_bandCardinalPackets_eq_primitive_boundStateSpace :
    (Submodule.span ℝ bandCardinalPackets).topologicalClosure =
      boundStateSpace ⊓ primitiveSector := by
  rw [closed_span_bandCardinalPackets, openBoundStateBand_eq_primitive_boundStateSpace]

theorem resolventInvariant_openBoundStateBand : ResolventInvariant openBoundStateBand := by
  rw [openBoundStateBand_eq_primitive_boundStateSpace]
  intro w hw
  exact ⟨resolventInvariant_boundStateSpace w hw.1,
    resolventInvariant_primitiveSector w hw.2⟩

end RHTower.CHMDPolar

end
