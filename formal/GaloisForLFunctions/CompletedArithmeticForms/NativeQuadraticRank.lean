import GaloisForLFunctions.CompletedArithmeticForms.GaussianContractionBound
import GaloisForLFunctions.CompletedArithmeticForms.NativeHermiteHorizon

/-!
# Quadratic rank control of the complete native form

The Gaussian contraction bound pays the first atom in the complete comparison
norm. The transformed infinite remainder adds only a linear dimension cost.
The exact Hermite congruence preserves their combined relative error in every
original signed moment direction.
-/

noncomputable section

open Matrix Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower

theorem hermiteGaussianHead_quadratic_eq (N : ℕ) (v : Fin N → ℝ) :
    v ⬝ᵥ hermiteGaussianHead N *ᵥ v = ∑ i, hermiteGaussianNormSq i.val * v i ^ 2 := by
  simp only [hermiteGaussianHead, dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem hermiteGaussianNormSq_one_le (n : ℕ) : 1 ≤ hermiteGaussianNormSq n := by
  have hp : (1 : ℝ) ≤ (8 : ℝ) ^ n := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 8) n
  have hf : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast (show 1 ≤ n.factorial from n.factorial_pos)
  simpa only [one_mul, hermiteGaussianNormSq] using
    mul_le_mul hp hf (by norm_num : (0 : ℝ) ≤ 1) (by positivity)

/-- The exact Hermite Gaussian norm dominates unweighted coefficient energy. -/
theorem sum_sq_le_hermiteGaussianHead (N : ℕ) (v : Fin N → ℝ) :
    ∑ i, v i ^ 2 ≤ v ⬝ᵥ hermiteGaussianHead N *ᵥ v := by
  rw [hermiteGaussianHead_quadratic_eq]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (hermiteGaussianNormSq_one_le i.val) (sq_nonneg (v i))

/-- Relative complete-form error is invariant under the exact monic Hermite coordinate change. -/
theorem relativeFormError_of_hermiteCongruence {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) {η : ℝ}
    (he : ∀ w, |w ⬝ᵥ (hermiteJetMatrix N * A * (hermiteJetMatrix N).transpose -
      hermiteGaussianHead N) *ᵥ w| ≤ η * (w ⬝ᵥ hermiteGaussianHead N *ᵥ w))
    (v : Fin N → ℝ) :
    |v ⬝ᵥ (A - gaussianFullHead N) *ᵥ v| ≤ η * (v ⬝ᵥ gaussianFullHead N *ᵥ v) := by
  obtain ⟨w, hw⟩ := hermiteJetMatrix_transpose_surjective N v
  have h := he w
  have hquad (M : Matrix (Fin N) (Fin N) ℝ) :
      w ⬝ᵥ (hermiteJetMatrix N * M * (hermiteJetMatrix N).transpose) *ᵥ w =
        v ⬝ᵥ M *ᵥ v := by
    simpa only [star_trivial, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose, hw] using
      HTGeometry.star_dotProduct_real_congr_mulVec M (hermiteJetMatrix N).transpose w
  have hdiff : hermiteJetMatrix N * A * (hermiteJetMatrix N).transpose -
      hermiteGaussianHead N = hermiteJetMatrix N * (A - gaussianFullHead N) *
        (hermiteJetMatrix N).transpose := by
    rw [hermiteGaussianHead_eq_full_congruence, Matrix.mul_sub, Matrix.sub_mul]
  rw [hdiff, hermiteGaussianHead_eq_full_congruence, hquad, hquad] at h
  exact h

/-- Quadratic rank error for the literal first-atom moment form in its original coordinates. -/
theorem firstAtomBalancedFullHead_quadratic_rank_error_le {x : ℝ} (N : ℕ)
    (hq : 16 * ((N : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (v : Fin N → ℝ) :
    |v ⬝ᵥ (finiteHankelMatrix (firstAtomBalancedFullMoment x) N - gaussianFullHead N) *ᵥ v| ≤
      (firstAtomQuadraticFormCost N / thetaCuspSingleAtomReflectionScale 1 x) *
        (v ⬝ᵥ gaussianFullHead N *ᵥ v) := by
  apply relativeFormError_of_hermiteCongruence
  intro w
  have h := firstAtomHermiteHead_quadratic_error_le N hq w
  rw [realWickJetMatrix_eq_congruence (firstAtomNormalizedRotatedPair_entire x),
    realEntireMomentMatrix_firstAtom] at h
  exact h

/-- The complete transformed theta remainder has only a linear relative dimension cost. -/
theorem nativeHermiteTail_relative_error_le {x : ℝ} (N : ℕ)
    (hq : 16 * ((N : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (v : Fin N → ℝ) :
    |v ⬝ᵥ (nativeHermiteHead N x -
      realWickJetMatrix (firstAtomNormalizedRotatedPair x) N) *ᵥ v| ≤
      ((N : ℝ) * nativePolynomialTailConstant * Real.exp 8 /
        thetaCuspSingleAtomReflectionScale 1 x) * (v ⬝ᵥ hermiteGaussianHead N *ᵥ v) := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hA := nativePolynomialTailConstant_pos
  have he := weighted_entry_error_le
    (nativeHermiteHead N x - realWickJetMatrix (firstAtomNormalizedRotatedPair x) N)
    (fun _ => (1 : ℝ)) (fun _ => by norm_num)
    (by positivity : 0 ≤ nativePolynomialTailConstant * Real.exp 8 /
      thetaCuspSingleAtomReflectionScale 1 x)
    (fun i j => by
      simpa only [Matrix.sub_apply, mul_one] using nativeHermiteHead_firstAtom_error_le N hq i j) v
  simp only [one_pow, one_mul] at he
  calc
    _ ≤ (N : ℝ) * (nativePolynomialTailConstant * Real.exp 8 /
        thetaCuspSingleAtomReflectionScale 1 x) * ∑ i, v i ^ 2 := he
    _ ≤ (N : ℝ) * (nativePolynomialTailConstant * Real.exp 8 /
        thetaCuspSingleAtomReflectionScale 1 x) * (v ⬝ᵥ hermiteGaussianHead N *ᵥ v) :=
      mul_le_mul_of_nonneg_left (sum_sq_le_hermiteGaussianHead N v) (by positivity)
    _ = _ := by ring

/-- Quadratic rank numerator including every native theta atom. -/
def nativeQuadraticFormCost (N : ℕ) : ℝ :=
  firstAtomQuadraticFormCost N + (N : ℝ) * nativePolynomialTailConstant * Real.exp 8

theorem nativeQuadraticFormCost_pos (N : ℕ) : 0 < nativeQuadraticFormCost N := by
  have hF := firstAtomQuadraticFormCost_pos N
  have hA := nativePolynomialTailConstant_pos
  unfold nativeQuadraticFormCost
  positivity

/-- The complete native Hermite form has quadratic relative error in rank. -/
theorem nativeHermiteHead_quadratic_error_le {x : ℝ} (N : ℕ)
    (hq : 16 * ((N : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (v : Fin N → ℝ) :
    |v ⬝ᵥ (nativeHermiteHead N x - hermiteGaussianHead N) *ᵥ v| ≤
      (nativeQuadraticFormCost N / thetaCuspSingleAtomReflectionScale 1 x) *
        (v ⬝ᵥ hermiteGaussianHead N *ᵥ v) := by
  have he : nativeHermiteHead N x - hermiteGaussianHead N =
      (nativeHermiteHead N x - realWickJetMatrix (firstAtomNormalizedRotatedPair x) N) +
      (realWickJetMatrix (firstAtomNormalizedRotatedPair x) N - hermiteGaussianHead N) := by abel
  rw [he, add_mulVec, dotProduct_add]
  apply (_root_.abs_add_le _ _).trans
  have h := add_le_add (nativeHermiteTail_relative_error_le N hq v)
    (firstAtomHermiteHead_quadratic_error_le N hq v)
  apply h.trans_eq
  unfold nativeQuadraticFormCost
  ring

/-- Quadratic mixed-rank Gaussian control of the literal complete native moment source. -/
theorem nativeBalancedFullHead_quadratic_rank_error_le {x : ℝ} (N : ℕ)
    (hq : 16 * ((N : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (v : Fin N → ℝ) :
    |v ⬝ᵥ (finiteHankelMatrix (nativeBalancedFullMoment x) N - gaussianFullHead N) *ᵥ v| ≤
      (nativeQuadraticFormCost N / thetaCuspSingleAtomReflectionScale 1 x) *
        (v ⬝ᵥ gaussianFullHead N *ᵥ v) := by
  apply relativeFormError_of_hermiteCongruence
  intro w
  exact nativeHermiteHead_quadratic_error_le N hq w

#print axioms relativeFormError_of_hermiteCongruence
#print axioms firstAtomBalancedFullHead_quadratic_rank_error_le
#print axioms nativeHermiteTail_relative_error_le
#print axioms nativeBalancedFullHead_quadratic_rank_error_le

end GaloisForLFunctions.CompletedArithmeticForms
