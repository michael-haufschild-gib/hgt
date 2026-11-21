import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelBohrSampling
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelResponsePerturbation
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelProbeStability

/-!
# Stability under sampled response errors

The inverse response converts measurement error into a commutator
error at each width. Interpolation propagates these errors back to
the unfiltered probe with its exact extrapolation weights.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H K : Matrix ι ι ℂ}

/-- The commutator with the measured response is the inverse-response
error multiplied by the Green shift. -/
theorem abelCommuteResponse_eq_shift_smul_error_sub_commutator
    (hH : H.IsHermitian) (hK : K.IsHermitian) (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    let Y := hamiltonianDampedGapResponse hH 0 ε X
    let E := hamiltonianDampedGapResponse hK 0 ε X - Y
    (K - H) * Y - Y * (K - H) = hamiltonianAbelShift ε • E - (K * E - E * K) := by
  let Y := hamiltonianDampedGapResponse hH 0 ε X
  let E := hamiltonianDampedGapResponse hK 0 ε X - Y
  let C := (K - H) * Y - Y * (K - H)
  let z := hamiltonianAbelShift ε
  have he := congrArg (hamiltonianAbelInverse K ε) (abelResponse_sub hH hK ε X)
  rw [hamiltonianAbelInverse_leftInverse hK ε] at he
  change hamiltonianAbelInverse K ε E = z⁻¹ • C at he
  change C = z • E - (K * E - E * K)
  calc
    _ = z • (z⁻¹ • C) := by rw [smul_smul,
      mul_inv_cancel₀ (hamiltonianAbelShift_ne_zero ε), one_smul]
    _ = z • hamiltonianAbelInverse K ε E := congrArg (fun M : Matrix ι ι ℂ => z • M) he.symm
    _ = _ := by rw [hamiltonianAbelInverse_eq_sub, smul_sub, smul_smul,
      mul_inv_cancel₀ (hamiltonianAbelShift_ne_zero ε), one_smul]

private theorem norm_abelCommuteResponse_apply_le (hH : H.IsHermitian) (hK : K.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) (δ : ℝ)
    (hδ : ∀ i j, ‖(hamiltonianDampedGapResponse hK 0 ε X -
      hamiltonianDampedGapResponse hH 0 ε X) i j‖ ≤ δ) (i j : ι) :
    let Y := hamiltonianDampedGapResponse hH 0 ε X
    ‖((K - H) * Y - Y * (K - H)) i j‖ ≤
      ((ε : ℝ) + (∑ l, ‖K i l‖) + ∑ l, ‖K l j‖) * δ := by
  let E := hamiltonianDampedGapResponse hK 0 ε X - hamiltonianDampedGapResponse hH 0 ε X
  have hl : ‖(K * E) i j‖ ≤ (∑ l, ‖K i l‖) * δ := by
    rw [Matrix.mul_apply, Finset.sum_mul]
    apply (norm_sum_le _ _).trans
    refine Finset.sum_le_sum fun l _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hδ l j) (norm_nonneg _)
  have hr : ‖(E * K) i j‖ ≤ (∑ l, ‖K l j‖) * δ := by
    rw [Matrix.mul_apply, Finset.sum_mul]
    apply (norm_sum_le _ _).trans
    refine Finset.sum_le_sum fun l _ => ?_
    rw [norm_mul, mul_comm ‖E i l‖]
    exact mul_le_mul_of_nonneg_left (hδ i l) (norm_nonneg _)
  have hZ : ‖hamiltonianAbelShift ε * E i j‖ ≤ (ε : ℝ) * δ := by
    rw [norm_mul, norm_hamiltonianAbelShift]
    exact mul_le_mul_of_nonneg_left (hδ i j) (show 0 < (ε : ℝ) from ε.2).le
  dsimp only
  rw [abelCommuteResponse_eq_shift_smul_error_sub_commutator hH hK ε X]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  change ‖hamiltonianAbelShift ε * E i j - ((K * E) i j - (E * K) i j)‖ ≤ _
  calc
    _ ≤ ‖hamiltonianAbelShift ε * E i j‖ + (‖(K * E) i j‖ + ‖(E * K) i j‖) :=
      (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    _ ≤ (ε : ℝ) * δ + ((∑ l, ‖K i l‖) * δ + (∑ l, ‖K l j‖) * δ) :=
      add_le_add hZ (add_le_add hl hr)
    _ = _ := by ring

/-- Propagated entrywise error at the unfiltered probe. -/
def abelSampleReadoutBound {n : ℕ} (hH : H.IsHermitian) (K X : Matrix ι ι ℂ)
    (widths : Fin n → Ioi (0 : ℝ)) (δ : Fin n → ℝ) (i j : ι) : ℝ :=
  ∑ k, ‖abelWidthLagrangeWeight widths k 0 *
    (abelBohrDenominator hH X).eval (abelWidthNode (widths k))‖ *
    (((widths k : ℝ) + (∑ l, ‖K i l‖) + ∑ l, ‖K l j‖) * δ k)

/-- Measured differences bound the original probe commutator at every
entry, with row and column costs of the competing Hamiltonian. -/
theorem norm_abelCommuteProbe_apply_le_of_width_samples {n : ℕ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) (X : Matrix ι ι ℂ)
    (widths : Fin n → Ioi (0 : ℝ)) (hwidths : Function.Injective widths)
    (hn : (abelProbeBohrGaps hH X).card < n) (δ : Fin n → ℝ)
    (hδ : ∀ k i j, ‖(hamiltonianDampedGapResponse hK 0 (widths k) X -
        hamiltonianDampedGapResponse hH 0 (widths k) X) i j‖ ≤ δ k)
    (i j : ι) :
    ‖(((K - H) * X - X * (K - H)) i j)‖ ≤ abelSampleReadoutBound hH K X widths δ i j := by
  rw [abelCommuteProbe_eq_sum_width_samples hH (K - H) X widths hwidths hn, Matrix.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_abelCommuteResponse_apply_le hH hK (widths k) X (δ k) (hδ k) i j) (norm_nonneg _)

#print axioms abelCommuteResponse_eq_shift_smul_error_sub_commutator
#print axioms norm_abelCommuteProbe_apply_le_of_width_samples

end

end GaloisForLFunctions.HTGeometry
