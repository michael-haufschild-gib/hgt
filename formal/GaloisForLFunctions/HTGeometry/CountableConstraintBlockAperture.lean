import GaloisForLFunctions.HTGeometry.FiniteConstraintBlockKernel
import GaloisForLFunctions.HTGeometry.PositiveHilbertCubeEmbedding
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Countable block aperture for finitely constrained Banach spaces

Suppose a Banach space contains countably many separated blocks, each with `k+1` independent
atoms, together with bounded projections that isolate the blocks.  For any `k` continuous linear
constraints, every block contains a nonzero invisible direction.  Normalization and Hahn--Banach
produce a biorthogonal sequence, hence the geometric-series construction embeds a Hilbert cube in
the exact affine constraint fiber.

For the measure-theoretic application, the atoms are indicators of disjoint positive-measure
pieces and the block projections are multiplication by the enclosing block indicators.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Countably many separated `(k+1)`-atom blocks yield normalized biorthogonal directions in the
kernel of every `k`-constraint operator. -/
theorem exists_biorthogonal_constraint_kernel_directions_of_blocks
    {k : ℕ} (T : E →L[ℝ] (Fin k → ℝ))
    (u : ℕ → Fin (k + 1) → E)
    (hu : ∀ j, LinearIndependent ℝ (u j))
    (P : ℕ → E →L[ℝ] E)
    (hP : ∀ j m l, P j (u m l) = if j = m then u m l else 0) :
    ∃ v : ℕ → E, ∃ ell : ℕ → E →L[ℝ] ℝ,
      (∀ n, ‖v n‖ = 1) ∧ (∀ n, T (v n) = 0) ∧
      ∀ n m, ell n (v m) = if n = m then 1 else 0 := by
  choose c hcne hcT hrawne using fun j =>
    exists_nonzero_block_constraint_direction T.toLinearMap (u j) (hu j)
  let raw : ℕ → E := fun j => (Fintype.linearCombination ℝ (u j)) (c j)
  have hraw_ne (j : ℕ) : raw j ≠ 0 := hrawne j
  let v : ℕ → E := fun j => (‖raw j‖⁻¹ : ℝ) • raw j
  have hvnorm (j : ℕ) : ‖v j‖ = 1 := by
    simp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (hraw_ne j)
  have hvT (j : ℕ) : T (v j) = 0 := by
    simp only [v]
    have hrawT : T (raw j) = 0 := by
      simpa only [raw] using! hcT j
    rw [map_smul, hrawT, smul_zero]
  have hPraw (j m : ℕ) : P j (raw m) = if j = m then raw m else 0 := by
    simp only [raw, Fintype.linearCombination_apply, map_sum, map_smul, hP]
    split_ifs with hjm
    · rfl
    · simp
  have hPv (j m : ℕ) : P j (v m) = if j = m then v m else 0 := by
    simp only [v]
    rw [map_smul, hPraw]
    split_ifs <;> simp_all
  choose f hfnorm hfraw using fun j => exists_dual_vector ℝ (raw j)
    (norm_ne_zero_iff.mpr (hraw_ne j))
  let ell : ℕ → E →L[ℝ] ℝ := fun j => (f j).comp (P j)
  refine ⟨v, ell, hvnorm, hvT, ?_⟩
  intro j m
  simp only [ell, ContinuousLinearMap.comp_apply]
  rw [hPv]
  split_ifs with hjm
  · subst m
    simp only [v]
    rw [map_smul, hfraw, smul_eq_mul]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hraw_ne j))
  · simp

/-- **Countable block Hilbert-cube aperture.** The exact affine constraint fiber through `base`
contains a closed topologically embedded copy of `[-1,1]^ℕ`. -/
theorem exists_closedEmbeddedHilbertCube_in_finiteConstraintFiber
    {k : ℕ} (T : E →L[ℝ] (Fin k → ℝ)) (base : E) {delta : ℝ} (hdelta : 0 < delta)
    (u : ℕ → Fin (k + 1) → E)
    (hu : ∀ j, LinearIndependent ℝ (u j))
    (P : ℕ → E →L[ℝ] E)
    (hP : ∀ j m l, P j (u m l) = if j = m then u m l else 0) :
    ∃ v : ℕ → E, ∃ ell : ℕ → E →L[ℝ] ℝ,
      (∀ n, ‖v n‖ = 1) ∧ (∀ n, T (v n) = 0) ∧
      (∀ n m, ell n (v m) = if n = m then 1 else 0) ∧
      Topology.IsClosedEmbedding (affinePositiveHilbertCubeMap base delta v) ∧
      ∀ t : SignedHilbertCube,
        T (affinePositiveHilbertCubeMap base delta v t) = T base := by
  obtain ⟨v, ell, hvnorm, hvker, hbio⟩ :=
    exists_biorthogonal_constraint_kernel_directions_of_blocks T u hu P hP
  refine ⟨v, ell, hvnorm, hvker, hbio, ?_, ?_⟩
  · exact affinePositiveHilbertCubeMap_isClosedEmbedding base hdelta
      (fun n => (hvnorm n).le) ell hbio
  · exact affinePositiveHilbertCubeMap_constraint_eq T base hdelta.le
      (fun n => (hvnorm n).le) hvker

end

end GaloisForLFunctions.HTGeometry
