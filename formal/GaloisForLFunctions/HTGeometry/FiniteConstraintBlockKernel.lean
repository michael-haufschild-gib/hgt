import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# A block with one more atom than constraints has a nonzero invisible direction

This is the finite linear-algebra engine in the Hilbert-cube aperture construction.  Given `k+1`
linearly independent block atoms and only `k` real constraints, a nonzero combination of those
atoms annihilates every constraint.  The theorem produces both the nonzero coefficient vector and
the resulting nonzero kernel direction, preventing a dimension-counting statement from silently
collapsing under a noninjective synthesis map.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Finite synthesis by a linearly independent family is injective. -/
theorem fintype_linearCombination_injective_of_linearIndependent
    {k : ℕ} {u : Fin k → E} (hu : LinearIndependent ℝ u) :
    Function.Injective (Fintype.linearCombination ℝ u) := by
  intro c d hcd
  apply Finsupp.equivFunOnFinite.symm.injective
  apply sub_eq_zero.mp
  apply (linearIndependent_iff.mp hu)
  rw [map_sub]
  apply sub_eq_zero.mpr
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype _ _ (fun i => zero_smul ℝ (u i)),
    Finsupp.sum_fintype _ _ (fun i => zero_smul ℝ (u i))]
  simpa [Fintype.linearCombination_apply] using hcd

/-- **Finite block-kernel law.** With `k+1` independent atoms and `k` constraints, there is a
nonzero coefficient vector whose synthesized direction is nonzero and annihilates all
constraints. -/
theorem exists_nonzero_block_constraint_direction
    {k : ℕ} (T : E →ₗ[ℝ] (Fin k → ℝ)) (u : Fin (k + 1) → E)
    (hu : LinearIndependent ℝ u) :
    ∃ c : Fin (k + 1) → ℝ, c ≠ 0 ∧
      T ((Fintype.linearCombination ℝ u) c) = 0 ∧
      (Fintype.linearCombination ℝ u) c ≠ 0 := by
  let S : (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
    T.comp (Fintype.linearCombination ℝ u)
  have hdim : Module.finrank ℝ (Fin k → ℝ) < Module.finrank ℝ (Fin (k + 1) → ℝ) := by
    simp
  have hker : LinearMap.ker S ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨c, hc, hcne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨c, hcne, ?_, ?_⟩
  · exact hc
  · exact fun hzero => hcne ((fintype_linearCombination_injective_of_linearIndependent hu)
      (hzero.trans (map_zero _).symm))

end

end GaloisForLFunctions.HTGeometry
