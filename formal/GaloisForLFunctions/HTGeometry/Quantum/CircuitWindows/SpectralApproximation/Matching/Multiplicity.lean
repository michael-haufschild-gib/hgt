import GaloisForLFunctions.HTGeometry.RiemannGaussian.HermitianRankTrace.VonNeumann
import GaloisForLFunctions.HTGeometry.PauliEdgeBlockNorms

/-! # Matching normal spectra with multiplicity in the fitting bases -/

open Matrix Finset RiemannGaussian.HermitianRankTrace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.Matching
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Some permutation costs no more than the transport plan given by
the squared overlaps of the two orthonormal bases. -/
theorem permutation_le_average (Q : unitaryGroup I ℂ) (cost : I→I→ℝ) :
    ∃ σ : Equiv.Perm I, (∑ i, cost i (σ i)) ≤ ∑ i, (normSqMatrix Q.val *ᵥ cost i) i := by
  classical
  let price (σ : Equiv.Perm I) := ∑ i, cost i (σ i)
  obtain ⟨σ,_,hmin⟩ := exists_min_image univ price univ_nonempty
  obtain ⟨w,hw,hsum,hmat⟩ := exists_eq_sum_perm_of_mem_doublyStochastic
    (normSqMatrix_mem_doublyStochastic_of_unitary Q.property)
  refine ⟨σ,?_⟩
  rw [←hmat]
  simp only [sum_mulVec,smul_mulVec,permMatrix_mulVec,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,Function.comp_apply]
  rw [sum_comm]
  calc price σ = ∑ τ, w τ*price σ := by rw [←sum_mul,hsum,one_mul]
       _ ≤ ∑ τ, w τ*price τ := sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hmin τ (mem_univ _)) (hw τ)
       _ = _ := sum_congr rfl fun τ _ => by rw [price,mul_sum]

/-- Hoffman–Wielandt in the transition basis. A single permutation
matches both spectra with squared error bounded by the full squared
Hilbert–Schmidt error, including every multiplicity. -/
theorem squared_matching (Q : unitaryGroup I ℂ) (z w : I→ℂ) :
    ∃ σ : Equiv.Perm I, (∑ i, ‖z i-w (σ i)‖^2) ≤
      hsNormSq (diagonal z*Q.val-Q.val*diagonal w) := by
  obtain ⟨σ,hσ⟩ := permutation_le_average Q fun i j => ‖z i-w j‖^2
  refine ⟨σ,hσ.trans_eq ?_⟩
  rw [hsNormSq,sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  change ‖Q.val i j‖^2*‖z i-w j‖^2=‖(diagonal z*Q.val-Q.val*diagonal w) i j‖^2
  rw [Matrix.sub_apply,diagonal_mul,mul_diagonal,mul_comm (Q.val i j),←sub_mul,norm_mul,mul_pow,mul_comm]

/-- One assignment simultaneously matches every complex eigenvalue with
error at most sqrt(D) times the operator approximation error. -/
theorem uniform_matching (Q : unitaryGroup I ℂ) (z w : I→ℂ) :
    ∃ σ : Equiv.Perm I, ∀ i, ‖z i-w (σ i)‖ ≤
      Real.sqrt (Fintype.card I)*‖diagonal z*Q.val-Q.val*diagonal w‖ := by
  obtain ⟨σ,hh⟩ := squared_matching Q z w
  refine ⟨σ,fun i => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  exact (single_le_sum (f:=fun j => ‖z j-w (σ j)‖^2) (fun j _ => sq_nonneg _) (mem_univ i)).trans
    (hh.trans (hsNormSq_le_card_mul_sq _))

/-- Normal matrices in arbitrary orthonormal eigenbases admit one
multiplicity-preserving assignment controlled by their operator distance. -/
theorem match_conjugates (V W : unitaryGroup I ℂ) (z w : I → ℂ) :
    ∃ σ : Equiv.Perm I, ∀ i, ‖z i - w (σ i)‖ ≤ Real.sqrt (Fintype.card I) *
      ‖V.val * diagonal z * star V.val - W.val * diagonal w * star W.val‖ := by
  let Q : unitaryGroup I ℂ := star V * W
  let A := V.val * diagonal z * star V.val
  let B := W.val * diagonal w * star W.val
  have hA : star V.val * A * W.val = diagonal z * Q.val := by
    change star V.val * (V.val * diagonal z * star V.val) * W.val =
      diagonal z * (star V.val * W.val)
    calc _ = (star V.val * V.val) * (diagonal z * (star V.val * W.val)) := by
              simp only [mul_assoc]
         _ = _ := by rw [V.property.1,one_mul]
  have hB : star V.val * B * W.val = Q.val * diagonal w := by
    change star V.val * (W.val * diagonal w * star W.val) * W.val =
      (star V.val * W.val) * diagonal w
    calc _ = (star V.val * W.val) * diagonal w * (star W.val * W.val) := by
              simp only [mul_assoc]
         _ = _ := by rw [W.property.1,mul_one]
  have he : star V.val * (A-B) * W.val = diagonal z * Q.val - Q.val * diagonal w := by
    rw [mul_sub,sub_mul,hA,hB]
  obtain ⟨σ,hσ⟩ := uniform_matching Q z w
  refine ⟨σ,fun i => ?_⟩
  have h := hσ i
  rwa [←he,CStarRing.norm_mul_mem_unitary _ W.property,
    CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem V.property)] at h

#print axioms match_conjugates
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.Matching
