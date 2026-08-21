/-
# The collision bound of the fully coupled shortcut law

Inside the tube over a patch of the diagonal carrier the Hamiltonian is a bounded perturbation of a
*diagonal* Hamiltonian, so the flat-overlap bound applies verbatim: if the carrier energies of the
patch are separated by `γ` and the tube radius is `r`, then the uniform superposition has spectral
collision at most `(D^{-1/2} + 2Lr/γ)²` for every Hamiltonian of the tube, where `L` is the
Lipschitz constant of the coefficient-to-Hamiltonian map.  No seed selection and no genericity are
needed: the bound is deterministic on the whole tube.

Main results:
* `pathPatchEquiv_symm_notDiag`, `pathPatchIsometry_embed_offDiag` — the embedded patch lies in the
  carrier.
* `patchHamLM_embed_eq_diagonal` — **the patch Hamiltonian is diagonal**.
* `spectralCollision_uniformSeed_le_of_mem_patchThickening` — **`(22)` on the tube**.
-/
import GaloisForLFunctions.HTGeometry.CapacityIncubationInstantiation
import GaloisForLFunctions.HTGeometry.PathCarrierSeparatingDirection

open Matrix Finset Metric Set
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n : ℕ}

theorem pathPatchEquiv_symm_notDiag {l : PathLabel n} (hl : ¬ IsDiagLabel l) :
    ∃ j, (pathPatchEquiv n).symm l = Sum.inr j := by
  classical
  obtain ⟨j0, hj0⟩ : ∃ j0, (Equiv.sumCompl (IsDiagLabel (n := n))).symm l = Sum.inr j0 :=
    ⟨⟨l, hl⟩, by
      have : (Equiv.sumCompl (IsDiagLabel (n := n))) (Sum.inr ⟨l, hl⟩) = l := rfl
      exact (Equiv.symm_apply_eq _).mpr this.symm⟩
  refine ⟨Fintype.equivFinOfCardEq (card_offDiagLabel n) j0, ?_⟩
  show (Equiv.sumCongr (Fintype.equivFinOfCardEq (card_diagLabel n)).symm
      (Fintype.equivFinOfCardEq (card_offDiagLabel n)).symm).symm
      ((Equiv.sumCompl (IsDiagLabel (n := n))).symm l) = _
  rw [hj0]
  rfl

/-- The embedded patch lies inside the diagonal carrier. -/
theorem pathPatchIsometry_embed_offDiag (v : EuclideanSpace ℝ (Fin (2 * n + 3)))
    {l : PathLabel n} (hl : ¬ IsDiagLabel l) :
    pathPatchIsometry n (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * n + 12))))) l = 0 := by
  obtain ⟨j, hj⟩ := pathPatchEquiv_symm_notDiag hl
  rw [ofLp_pathPatchIsometry_embed, hj]
  rfl

variable {k : ℕ}

/-- **The patch Hamiltonian is diagonal.** -/
theorem patchHamLM_embed_eq_diagonal (v : EuclideanSpace ℝ (Fin (2 * (k + 1) + 3))) :
    patchHamLM k (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12)))))
      = Matrix.diagonal fun x => ((pathDiagEnergy
          (pathPatchIsometry (k + 1)
            (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12)))))) x : ℝ) : ℂ) := by
  rw [patchHamLM_apply]
  exact pathHamiltonian_eq_diagonal _ fun l hl => pathPatchIsometry_embed_offDiag v hl

/-- **`(22)` on the tube.**  Every Hamiltonian of the tube over a separated carrier patch keeps the
uniform superposition capacity-good. -/
theorem spectralCollision_uniformSeed_le_of_mem_patchThickening
    {PU : Set (EuclideanSpace ℝ (Fin (2 * (k + 1) + 3)))}
    (hcompact : IsCompact (embedPatch (d := 10 * (k + 1) + 12) PU))
    (hnonempty : (embedPatch (d := 10 * (k + 1) + 12) PU).Nonempty)
    {gap r : ℝ} (hgap : 0 < gap) (hr : 0 ≤ r)
    (hsep : ∀ v ∈ PU, ∀ x y : FiniteQubitConfiguration (Fin (k + 3)), x ≠ y →
      gap ≤ |pathDiagEnergy (pathPatchIsometry (k + 1)
              (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12)))))) x
            - pathDiagEnergy (pathPatchIsometry (k + 1)
              (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12)))))) y|)
    {ω : sphere (0 : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) 1}
    (hω : ω ∈ patchThickening (d := 10 * (k + 1) + 12) PU r)
    {ebasis : FiniteQubitConfiguration (Fin (k + 3)) → FiniteQubitConfiguration (Fin (k + 3)) → ℂ}
    {lam : FiniteQubitConfiguration (Fin (k + 3)) → ℝ}
    (heb : IsOrthoEigenBasis (patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3)
      (10 * (k + 1) + 12))) ebasis lam) :
    spectralCollision ebasis (uniformSeed (k + 3))
      ≤ ((Real.sqrt (2 ^ (k + 3)))⁻¹
          + 2 * (Real.sqrt (Fintype.card (PathLabel (k + 1))) * r) / gap) ^ 2 := by
  classical
  obtain ⟨y, hy, hdist⟩ :=
    hcompact.exists_infDist_eq_dist hnonempty
      (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))
  obtain ⟨v, hvPU, hvy⟩ := hy
  have hle : dist (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) y ≤ r := by
    rw [← hdist]
    exact hω
  have hnear : ‖patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))
      - Matrix.diagonal (fun x => ((pathDiagEnergy (pathPatchIsometry (k + 1)
          (WithLp.toLp 2 (v, (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12)))))) x : ℝ) : ℂ))‖
      ≤ Real.sqrt (Fintype.card (PathLabel (k + 1))) * r := by
    rw [← patchHamLM_embed_eq_diagonal v, hvy]
    refine le_trans (norm_patchHamLM_sub_le _ _) ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [← dist_eq_norm]
    exact hle
  have hdelta : (0 : ℝ) ≤ Real.sqrt (Fintype.card (PathLabel (k + 1))) * r :=
    mul_nonneg (Real.sqrt_nonneg _) hr
  have hchi : ∀ x, ‖uniformSeed (k + 3) x‖ ≤ (Real.sqrt (2 ^ (k + 3)))⁻¹ := fun x =>
    le_of_eq (norm_uniformSeed (k + 3) x)
  have hc : (0 : ℝ) ≤ (Real.sqrt (2 ^ (k + 3)))⁻¹ := by positivity
  exact spectralCollision_le_of_near_diagonal hgap
    (fun x z hxz => hsep v hvPU x z hxz) hdelta hnear heb hc hchi
    (norm_eucVec_uniformSeed (k + 3))

end GaloisForLFunctions.HTGeometry

end
