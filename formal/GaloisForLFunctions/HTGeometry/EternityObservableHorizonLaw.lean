import GaloisForLFunctions.HTGeometry.EternityHorizonCapstone
import Mathlib.Analysis.Matrix.PosDef

/-!
# The observable form of the bounded-horizon law

A density matrix pairs with an operator inside its operator norm: the trace pairing is a convex
combination of diagonal entries in an eigenbasis of the state, and every entry of a matrix is
bounded by its operator norm.

Consequently the Heisenberg bound for a Hamiltonian perturbation descends to expectation values:
the observed signal of two Hamiltonians separated by `δ` differs by at most `2|t| δ ‖O‖` in every
state, so no bounded-time expectation value can resolve an exact recurrence change.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-- The matrix algebra is a C⋆-algebra for the operator norm. -/
local instance instCStarAlgebraMatrixObservable : CStarAlgebra (Matrix d d ℂ) where

omit [Nonempty d] in
/-- Every entry of a matrix is bounded by its operator norm. -/
theorem norm_entry_le_l2_opNorm (Y : Matrix d d ℂ) (i j : d) : ‖Y i j‖ ≤ ‖Y‖ := by
  have hsingle : ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ d)‖ = 1 := by
    simp
  have h := Matrix.l2_opNorm_mulVec Y (EuclideanSpace.single j (1 : ℂ))
  rw [hsingle, mul_one] at h
  have hcol : Y *ᵥ (EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ d).ofLp
      = fun i => Y i j := by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_ite_eq']
  have hcoord := PiLp.norm_apply_le
    ((EuclideanSpace.equiv d ℂ).symm (Y *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  rw [hcol] at h hcoord
  exact le_trans hcoord h

omit [Nonempty d] in
/-- Conjugation by a contraction does not increase the operator norm. -/
theorem l2_opNorm_star_conj_le {W : Matrix d d ℂ} (hW : ‖W‖ ≤ 1) (X : Matrix d d ℂ) :
    ‖star W * X * W‖ ≤ ‖X‖ := by
  have hWs : ‖star W‖ ≤ 1 := by
    rw [norm_star]
    exact hW
  calc ‖star W * X * W‖ ≤ ‖star W * X‖ * ‖W‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖star W‖ * ‖X‖) * ‖W‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * ‖X‖) * 1 := by
        refine mul_le_mul ?_ hW (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right hWs (norm_nonneg _)
    _ = ‖X‖ := by ring

/-- **The trace pairing of a state with an operator is inside the operator norm.** -/
theorem norm_trace_densityMatrix_mul_le {ρ : Matrix d d ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (X : Matrix d d ℂ) : ‖(ρ * X).trace‖ ≤ ‖X‖ := by
  classical
  set W : Matrix d d ℂ := (hρ.1.eigenvectorUnitary : Matrix d d ℂ) with hWdef
  have hWnorm : ‖W‖ = 1 := CStarRing.norm_coe_unitary hρ.1.eigenvectorUnitary
  set p : d → ℝ := hρ.1.eigenvalues with hpdef
  have hspec : ρ = W * Matrix.diagonal (fun i => (p i : ℂ)) * star W := hρ.1.spectral_theorem
  set Y : Matrix d d ℂ := star W * X * W with hYdef
  have hcyc : (ρ * X).trace = (Matrix.diagonal (fun i => (p i : ℂ)) * Y).trace := by
    rw [hspec]
    calc (W * Matrix.diagonal (fun i => (p i : ℂ)) * star W * X).trace
        = (W * (Matrix.diagonal (fun i => (p i : ℂ)) * (star W * X))).trace := by
          simp only [Matrix.mul_assoc]
      _ = ((Matrix.diagonal (fun i => (p i : ℂ)) * (star W * X)) * W).trace :=
          Matrix.trace_mul_comm _ _
      _ = (Matrix.diagonal (fun i => (p i : ℂ)) * Y).trace := by
          rw [hYdef]
          simp only [Matrix.mul_assoc]
  have hdiag : (Matrix.diagonal (fun i => (p i : ℂ)) * Y).trace = ∑ i, (p i : ℂ) * Y i i := by
    simp only [Matrix.trace, Matrix.diag_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq]
  have hpnn : ∀ i, 0 ≤ p i := Matrix.PosSemidef.eigenvalues_nonneg hρ
  have hpsum : ∑ i, p i = 1 := by
    have h := hρ.1.trace_eq_sum_eigenvalues
    rw [htr] at h
    have hcast : ((1 : ℝ) : ℂ) = ((∑ i, p i : ℝ) : ℂ) := by
      push_cast
      exact h
    exact_mod_cast hcast.symm
  have hentry : ∀ i, ‖Y i i‖ ≤ ‖X‖ := by
    intro i
    refine le_trans (norm_entry_le_l2_opNorm Y i i) ?_
    rw [hYdef]
    exact l2_opNorm_star_conj_le (le_of_eq hWnorm) X
  rw [hcyc, hdiag]
  calc ‖∑ i, (p i : ℂ) * Y i i‖ ≤ ∑ i, ‖(p i : ℂ) * Y i i‖ := norm_sum_le _ _
    _ = ∑ i, p i * ‖Y i i‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpnn i)]
    _ ≤ ∑ i, p i * ‖X‖ :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hentry i) (hpnn i)
    _ = ‖X‖ := by rw [← Finset.sum_mul, hpsum, one_mul]

/-- **Theorem C `(3)`: the observable form of the bounded-horizon law.**  In every state the
expectation of a bounded observable evolved by two Hamiltonians differs by at most twice the time,
the Hamiltonian distance and the observable norm. -/
theorem norm_trace_densityMatrix_heisenberg_sub_le {ρ : Matrix d d ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (H K O : Matrix d d ℂ) (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K)
    (t : ℝ) :
    ‖(ρ * (unitaryEvolution H t * O * star (unitaryEvolution H t)
        - unitaryEvolution K t * O * star (unitaryEvolution K t))).trace‖
      ≤ 2 * |t| * ‖H - K‖ * ‖O‖ := by
  refine le_trans (norm_trace_densityMatrix_mul_le hρ htr _) ?_
  exact selfAdjoint_heisenbergEvolution_norm_sub_le (A := Matrix d d ℂ) H K O hH hK t

end

end GaloisForLFunctions.HTGeometry
