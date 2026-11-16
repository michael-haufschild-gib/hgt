import GaloisForLFunctions.HilbertMetric.Spectral.ClippedCongruence

/-!
# Local clipped certificates combine globally

Optimal certificates on disjoint principal blocks assemble to an admissible
global certificate. Off-block interactions need no size or sign restriction.
Thus a sum of local clipped defects survives globally and under mixed weights.
-/
open Matrix RiemannGaussian.HermitianRankTrace
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.HilbertMetric.Clipped
noncomputable section
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
  {ι : κ → Type*} [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)]

omit [∀ k, DecidableEq (ι k)] in
/-- Positivity is preserved by assembling finitely many disjoint blocks. -/
theorem block_positive (M : ∀ k, Matrix (ι k) (ι k) ℂ)
    (hM : ∀ k, (M k).PosSemidef) : (Matrix.blockDiagonal' M).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_blockDiagonal'_iff.mpr (fun k => (hM k).isHermitian))
  intro x
  have h := Finset.sum_nonneg (s := Finset.univ) (fun k _ =>
    (hM k).dotProduct_mulVec_nonneg (fun i => x ⟨k, i⟩))
  simpa [dotProduct, Matrix.mulVec, Fintype.sum_sigma, Matrix.blockDiagonal'_apply,
    Finset.mul_sum, dite_mul, Finset.sum_dite_irrel] using h

omit [∀ k, DecidableEq (ι k)] in
/-- A block-diagonal test matrix sees precisely the corresponding principal blocks. -/
theorem trace_block_pair (B : ∀ k, Matrix (ι k) (ι k) ℂ)
    (A : Matrix (Σ k, ι k) (Σ k, ι k) ℂ) :
    trace (Matrix.blockDiagonal' B * A) =
      ∑ k, trace (B k * A.submatrix (Sigma.mk k) (Sigma.mk k)) := by
  simp [trace, diag, Matrix.mul_apply, Fintype.sum_sigma,
    Matrix.blockDiagonal'_apply, Matrix.submatrix_apply, dite_mul]

/-- Clipped energy dominates the sum of its disjoint principal-block energies. -/
theorem energy_blocks_lower {A : Matrix (Σ k, ι k) (Σ k, ι k) ℂ}
    (hA : A.IsHermitian) (c : ℝ) :
    (∑ k, energy c (Matrix.blockDiag' A k)) ≤ energy c A := by
  let C := fun k => certificate (hA.submatrix (Sigma.mk k)) c
  have hC : (Matrix.blockDiagonal' C).IsHermitian :=
    Matrix.isHermitian_blockDiagonal'_iff.mpr fun k => certificate_hermitian _ _
  have hcap := block_positive
    (fun k => (c : ℂ) • (1 : Matrix (ι k) (ι k) ℂ) - C k)
    (fun k => certificate_cap (hA.submatrix (Sigma.mk k)) c)
  change (Matrix.blockDiagonal' ((c : ℂ) • (1 : ∀ k, Matrix (ι k) (ι k) ℂ) - C)).PosSemidef at hcap
  rw [Matrix.blockDiagonal'_sub, Matrix.blockDiagonal'_smul, Matrix.blockDiagonal'_one] at hcap
  calc
    _ = ∑ k, (2 * (trace (C k * Matrix.blockDiag' A k)).re - (trace (C k * C k)).re) := by
      apply Finset.sum_congr rfl
      intro k _
      exact (certificate_attains (hA.submatrix (Sigma.mk k)) c).symm
    _ = 2 * (trace (Matrix.blockDiagonal' C * A)).re -
        (trace (Matrix.blockDiagonal' C * Matrix.blockDiagonal' C)).re := by
      rw [trace_block_pair, ← Matrix.blockDiagonal'_mul, Matrix.trace_blockDiagonal']
      simp only [Complex.re_sum, Finset.sum_sub_distrib, Finset.mul_sum]
      rfl
    _ ≤ _ := dual_bound hA hC c hcap

end

section Centering
variable {η : Type*} [Fintype η] [DecidableEq η]

/-- Unit-centered defect is ordinary clipped energy after subtracting the identity. -/
theorem defectEnergy_eq_shift {A : Matrix η η ℂ} (hA : A.IsHermitian) (τ : ℝ) :
    defectEnergy τ A = energy τ (A - 1) := by
  have hs : A - 1 = specMap hA (fun x => x - 1) := by
    rw [show (fun x : ℝ => x - 1) = id - (fun _ => 1) from rfl,
      specMap_sub, specMap_id, specMap_constant]
    simp
  rw [hs, energy, RiemannGaussian.HermitianRankTrace.specMap,
    Unitary.conjStarAlgAut_apply, spectralSum_unitary]
  change defectEnergy τ A = spectralSum (quadratic τ)
    (diagonal fun i => ((hA.eigenvalues i - 1 : ℝ) : ℂ))
  rw [spectralSum_diagonal, defectEnergy, spectralSum_eq hA]
  rfl

end Centering

section DefectBlocks
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
  {ι : κ → Type*} [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)]

/-- Centered local defects add without any restriction on inter-block correlations. -/
theorem defect_blocks_lower {A : Matrix (Σ k, ι k) (Σ k, ι k) ℂ}
    (hA : A.IsHermitian) (τ : ℝ) :
    (∑ k, defectEnergy τ (Matrix.blockDiag' A k)) ≤ defectEnergy τ A := by
  rw [defectEnergy_eq_shift hA]
  have h := energy_blocks_lower (hA.sub Matrix.isHermitian_one) τ
  simp only [Matrix.blockDiag'_sub, Matrix.blockDiag'_one, Pi.sub_apply, Pi.one_apply] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro k _
  exact defectEnergy_eq_shift (hA.submatrix (Sigma.mk k)) τ

/-- Every disjoint block retains its own square-energy surplus up to its own cutoff. -/
theorem block_minima_lower {A : Matrix (Σ k, ι k) (Σ k, ι k) ℂ}
    (hA : A.IsHermitian) (τ : ℝ≥0) :
    (∑ k, min ((trace (Matrix.blockDiag' A k * Matrix.blockDiag' A k)).re -
      2 * (trace (Matrix.blockDiag' A k)).re + Fintype.card (ι k)) ((τ : ℝ) ^ 2)) ≤
        defectEnergy τ A :=
  (Finset.sum_le_sum fun k _ => defectEnergy_min_bound
    (hA.submatrix (Sigma.mk k)) τ).trans (defect_blocks_lower hA τ)

/-- Local defects remain additive after independently doubling any selected columns. -/
theorem mixed_block_defects {U : Matrix (Σ k, ι k) (Σ k, ι k) ℂ}
    (hU : U.IsHermitian) (hdiag : ∀ i, U i i = 1)
    (doubled : (Σ k, ι k) → Bool) (τ : ℝ≥0) :
    (∑ k, defectEnergy τ (Matrix.blockDiag' U k)) + ∑ i, binaryWeight doubled i ^ 2 ≤
      energy (mixedCutoff τ) (weightedGram (binaryWeight doubled) U) :=
  (add_le_add (defect_blocks_lower hU τ) le_rfl).trans (binary_mixed_bound hU hdiag doubled τ)

#print axioms energy_blocks_lower
#print axioms block_minima_lower
#print axioms mixed_block_defects

end DefectBlocks
end GaloisForLFunctions.HilbertMetric.Clipped
