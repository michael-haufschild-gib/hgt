import GaloisForLFunctions.HTGeometry.CompactOperatorGeneralSpectrum
import GaloisForLFunctions.HTGeometry.GeneralizedEigenspaceIntertwining
import GaloisForLFunctions.HTGeometry.HilbertSchmidtBlockEigenvector
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantMultiplicity

/-!
# Algebraic multiplicity of a padded Hilbert--Schmidt finite section

A finite block acts on its coordinate space, while its zero-padded truncation acts on ambient
`ℓ²`.  Zero padding adds only zero generalized eigenvectors.  At every nonzero eigenvalue, the two
generalized eigenspaces are therefore linearly equivalent and have identical finite dimension.
-/

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt Matrix

variable {ι : Type*} [DecidableEq ι]

/-- Zero extension of a block vector, as a linear map into ambient `ℓ²`. -/
noncomputable def liftBlockLinearMap (s : Finset ι) :
    (↥s → ℂ) →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 where
  toFun := liftBlockLp
  map_add' := by
    intro v w
    apply lp.ext
    funext i
    by_cases hi : i ∈ s <;> simp [liftBlockLp_apply, liftBlock, hi]
  map_smul' := by
    intro c v
    apply lp.ext
    funext i
    by_cases hi : i ∈ s <;> simp [liftBlockLp_apply, liftBlock, hi]

@[simp] theorem liftBlockLinearMap_apply (s : Finset ι) (v : ↥s → ℂ) :
    liftBlockLinearMap s v = liftBlockLp v := rfl

theorem liftBlockLinearMap_injective (s : Finset ι) :
    Function.Injective (liftBlockLinearMap s) := by
  intro v w h
  funext i
  have hi := congrFun
    (congrArg (fun x : lp (fun _ : ι => ℂ) 2 => (x : ι → ℂ)) h) (i : ι)
  simpa [liftBlockLinearMap_apply, liftBlockLp_apply, liftBlock_apply_of_mem] using hi

/-- The padded truncation factors through its finite block on every ambient vector. -/
theorem toOperator_truncKernel_eq_liftBlock_mulVec_restrict {K : ι × ι → ℂ} (hK : IsHS K)
    (s : Finset ι) (x : lp (fun _ : ι => ℂ) 2) :
    toOperator (isHS_truncKernel hK s) x =
      liftBlockLp ((blockMatrix K s) *ᵥ fun j : ↥s => x (j : ι)) := by
  apply lp.ext
  funext i
  show (∑' j, truncKernel K s (i, j) * x j) =
    liftBlock ((blockMatrix K s) *ᵥ fun j : ↥s => x (j : ι)) i
  by_cases hi : i ∈ s
  · have hzero : ∀ j ∉ s, truncKernel K s (i, j) * x j = 0 := by
      intro j hj
      simp [truncKernel, hj]
    rw [tsum_eq_sum (s := s) hzero,
      ← Finset.sum_coe_sort s fun j : ι => truncKernel K s (i, j) * x j]
    have hentry : ∀ j : ↥s, truncKernel K s (i, (j : ι)) * x (j : ι)
        = (blockMatrix K s) ⟨i, hi⟩ j * x (j : ι) := by
      intro j
      simp [truncKernel, blockMatrix, hi, j.2]
    rw [Finset.sum_congr rfl fun j _ => hentry j,
      liftBlock_apply_of_mem _ hi, Matrix.mulVec, dotProduct]
  · have hzero : ∀ j : ι, truncKernel K s (i, j) * x j = 0 := by
      intro j
      simp [truncKernel, hi]
    rw [liftBlock_apply_of_notMem _ hi]
    simp [hzero]

/-- Zero extension intertwines the finite block matrix with its padded operator. -/
theorem liftBlockLinearMap_intertwines {K : ι × ι → ℂ} (hK : IsHS K) (s : Finset ι)
    (v : ↥s → ℂ) :
    liftBlockLinearMap s (Matrix.toLin' (blockMatrix K s) v) =
      toOperator (isHS_truncKernel hK s) (liftBlockLinearMap s v) := by
  rw [toOperator_truncKernel_eq_liftBlock_mulVec_restrict hK s]
  apply congrArg liftBlockLp
  funext i
  simp [Matrix.toLin'_apply, liftBlockLinearMap_apply, liftBlockLp_apply,
    liftBlock_apply_of_mem]

/-- The range of the padded truncation lies in the zero-extension coordinate range. -/
theorem range_toOperator_truncKernel_le_range_liftBlockLinearMap {K : ι × ι → ℂ}
    (hK : IsHS K) (s : Finset ι) :
    LinearMap.range (toOperator (isHS_truncKernel hK s) :
      lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) ≤
      LinearMap.range (liftBlockLinearMap s) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨(blockMatrix K s) *ᵥ fun j : ↥s => x (j : ι), ?_⟩
  exact (toOperator_truncKernel_eq_liftBlock_mulVec_restrict hK s x).symm

/-- **A padded finite section has exactly the block's algebraic multiplicity away from zero.** -/
theorem finrank_maxGenEigenspace_toOperator_truncKernel_eq_block {K : ι × ι → ℂ}
    (hK : IsHS K) (s : Finset ι) {mu : ℂ} (hmu : mu ≠ 0) :
    Module.finrank ℂ
        (Module.End.maxGenEigenspace (Matrix.toLin' (blockMatrix K s)) mu) =
      Module.finrank ℂ (Module.End.maxGenEigenspace
        (toOperator (isHS_truncKernel hK s) :
          lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) mu) := by
  apply finrank_maxGenEigenspace_eq_of_intertwining
    (Matrix.toLin' (blockMatrix K s))
    (toOperator (isHS_truncKernel hK s) :
      lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2)
    (liftBlockLinearMap s) (liftBlockLinearMap_injective s)
    (liftBlockLinearMap_intertwines hK s) mu
  exact le_trans (maxGenEigenspace_le_range_of_ne_zero _ hmu)
    (range_toOperator_truncKernel_le_range_liftBlockLinearMap hK s)

/-! ## Reindexing to the canonical `Fin` block -/

/-- Reindex block vectors along mathlib's canonical equivalence with `Fin`. -/
noncomputable def blockFinToBlockEquiv (s : Finset ι) :
    (Fin (Fintype.card ↥s) → ℂ) ≃ₗ[ℂ] (↥s → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin ↥s)

omit [DecidableEq ι] in
@[simp] theorem blockFinToBlockEquiv_apply (s : Finset ι)
    (v : Fin (Fintype.card ↥s) → ℂ) (i : ↥s) :
    blockFinToBlockEquiv s v i = v (Fintype.equivFin ↥s i) := rfl

/-- Reindexing intertwines the canonical `Fin` block with the subtype-indexed block. -/
theorem blockFinToBlockEquiv_intertwines (K : ι × ι → ℂ) (s : Finset ι)
    (v : Fin (Fintype.card ↥s) → ℂ) :
    blockFinToBlockEquiv s (Matrix.toLin' (blockFin K s) v) =
      Matrix.toLin' (blockMatrix K s) (blockFinToBlockEquiv s v) := by
  have hv : Matrix.toLin' (blockFin K s) v =
      (blockFinToBlockEquiv s).symm
        (Matrix.toLin' (blockMatrix K s) (blockFinToBlockEquiv s v)) := by
    simp [blockFin, blockFinToBlockEquiv, LinearMap.comp_apply]
  rw [hv]
  exact (blockFinToBlockEquiv s).apply_symm_apply _

/-- Direct zero extension from the canonical `Fin` block into ambient `ℓ²`. -/
noncomputable def liftBlockFinLinearMap (s : Finset ι) :
    (Fin (Fintype.card ↥s) → ℂ) →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 :=
  (liftBlockLinearMap s).comp (blockFinToBlockEquiv s).toLinearMap

theorem liftBlockFinLinearMap_injective (s : Finset ι) :
    Function.Injective (liftBlockFinLinearMap s) :=
  (liftBlockLinearMap_injective s).comp (blockFinToBlockEquiv s).injective

/-- The canonical `Fin` block intertwines with the padded finite-section operator. -/
theorem liftBlockFinLinearMap_intertwines {K : ι × ι → ℂ} (hK : IsHS K) (s : Finset ι)
    (v : Fin (Fintype.card ↥s) → ℂ) :
    liftBlockFinLinearMap s (Matrix.toLin' (blockFin K s) v) =
      toOperator (isHS_truncKernel hK s) (liftBlockFinLinearMap s v) := by
  change liftBlockLinearMap s
      (blockFinToBlockEquiv s (Matrix.toLin' (blockFin K s) v)) =
    toOperator (isHS_truncKernel hK s) (liftBlockLinearMap s (blockFinToBlockEquiv s v))
  rw [blockFinToBlockEquiv_intertwines K s v,
    liftBlockLinearMap_intertwines hK s]

theorem range_liftBlockLinearMap_le_range_liftBlockFinLinearMap (s : Finset ι) :
    LinearMap.range (liftBlockLinearMap s) ≤ LinearMap.range (liftBlockFinLinearMap s) := by
  rintro _ ⟨v, rfl⟩
  refine ⟨(blockFinToBlockEquiv s).symm v, ?_⟩
  simp [liftBlockFinLinearMap]

/-- **Canonical `Fin` version of exact finite-section algebraic multiplicity.** -/
theorem finrank_maxGenEigenspace_toOperator_truncKernel_eq_blockFin {K : ι × ι → ℂ}
    (hK : IsHS K) (s : Finset ι) {mu : ℂ} (hmu : mu ≠ 0) :
    Module.finrank ℂ (Module.End.maxGenEigenspace (Matrix.toLin' (blockFin K s)) mu) =
      Module.finrank ℂ (Module.End.maxGenEigenspace
        (toOperator (isHS_truncKernel hK s) :
          lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) mu) := by
  apply finrank_maxGenEigenspace_eq_of_intertwining
    (Matrix.toLin' (blockFin K s))
    (toOperator (isHS_truncKernel hK s) :
      lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2)
    (liftBlockFinLinearMap s) (liftBlockFinLinearMap_injective s)
    (liftBlockFinLinearMap_intertwines hK s) mu
  exact le_trans (maxGenEigenspace_le_range_of_ne_zero _ hmu)
    (le_trans (range_toOperator_truncKernel_le_range_liftBlockLinearMap hK s)
      (range_liftBlockLinearMap_le_range_liftBlockFinLinearMap s))

end GaloisForLFunctions.HTGeometry
