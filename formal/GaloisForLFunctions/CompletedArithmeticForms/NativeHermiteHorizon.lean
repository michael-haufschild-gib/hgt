import GaloisForLFunctions.CompletedArithmeticForms.HermiteSourceBound
import GaloisForLFunctions.CompletedArithmeticForms.HermiteNativeTail
import GaloisForLFunctions.HTGeometry.EvenEntireSquareFactor

/-!
# A polynomial rank horizon for the complete native moment form

The actual first-atom and infinite-tail errors are paid in the same diagonal
Hermite norm. The monic coordinate change is bijective, so its relative bound
returns to the complete native moment form without any inverse-matrix penalty.
-/

noncomputable section

open Finset Matrix

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

/-- Complete Gaussian signed moment head, including all odd-zero cross entries. -/
def gaussianFullHead (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  finiteHankelMatrix (evenMomentSequence gaussianMoment) N

theorem complexGaussian_all_jets (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => Complex.exp (4 * z ^ 2)) 0 =
      (evenMomentSequence gaussianMoment n : ℂ) := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    rw [show n = 2 * k by omega, complexGaussian_even_jet, evenMomentSequence_even]
  · obtain ⟨k, hk⟩ := ho
    have heven : Function.Even (fun z : ℂ => Complex.exp (4 * z ^ 2)) := by
      intro z
      simp only [neg_sq]
    rw [show n = 2 * k + 1 by omega, evenMomentSequence_odd, Complex.ofReal_zero]
    exact HTGeometry.iteratedDeriv_zero_of_even_of_odd heven ⟨k, rfl⟩

theorem gaussianFullHead_eq_entire (N : ℕ) :
    gaussianFullHead N = realEntireMomentMatrix (fun z : ℂ => Complex.exp (4 * z ^ 2)) N := by
  ext i j
  simp only [gaussianFullHead, finiteHankelMatrix, realEntireMomentMatrix,
    complexGaussian_all_jets, Complex.ofReal_re]

theorem gaussianFullHead_posDef (N : ℕ) : (gaussianFullHead N).PosDef := by
  apply (finiteHankelMatrix_evenMomentSequence_posDef_iff gaussianMoment N).mpr
  constructor
  · simpa only [gaussianShiftedHead, Nat.add_zero] using
      gaussianShiftedHead_posDef ((N + 1) / 2) 0
  · exact gaussianShiftedHead_posDef (N / 2) 1

theorem hermiteGaussianHead_eq_full_congruence (N : ℕ) :
    hermiteGaussianHead N = hermiteJetMatrix N * gaussianFullHead N *
      (hermiteJetMatrix N).transpose := by
  calc
    _ = realWickJetMatrix (fun z : ℂ => Complex.exp (4 * z ^ 2)) N := by
      simpa only [hermiteGaussianHead, hermiteGaussianNormSq] using
        (realWickJetMatrix_gaussian N).symm
    _ = _ := by
      rw [realWickJetMatrix_eq_congruence (by fun_prop), ← gaussianFullHead_eq_entire]

private theorem hermiteGaussianNormSq_ge_one (n : ℕ) : 1 ≤ hermiteGaussianNormSq n := by
  have hp : (1 : ℝ) ≤ (8 : ℝ) ^ n := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 8) n
  have hf : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast (show 1 ≤ n.factorial from n.factorial_pos)
  simpa only [one_mul, hermiteGaussianNormSq] using
    mul_le_mul hp hf (by norm_num : (0 : ℝ) ≤ 1) (by positivity)

private theorem hermiteGaussianNorm_ge_one (n : ℕ) :
    1 ≤ Real.sqrt (hermiteGaussianNormSq n) := by
  have hs := Real.sq_sqrt (hermiteGaussianNormSq_pos n).le
  nlinarith only [hs, hermiteGaussianNormSq_ge_one n, Real.sqrt_nonneg (hermiteGaussianNormSq n)]

/-- Cubic complete-source entry numerator after both arithmetic channels are combined. -/
def nativeHermiteErrorNumerator (N : ℕ) : ℝ :=
  hermiteSourceErrorNumerator N + nativePolynomialTailConstant * Real.exp 8

/-- Quartic rank payment for the complete native quadratic form. -/
def nativeHermiteFormCost (N : ℕ) : ℝ := (N : ℝ) * nativeHermiteErrorNumerator N

theorem nativeHermiteErrorNumerator_pos (N : ℕ) : 0 < nativeHermiteErrorNumerator N := by
  have h1 := hermiteSourceErrorNumerator_pos N
  have h2 := nativePolynomialTailConstant_pos
  unfold nativeHermiteErrorNumerator
  positivity

theorem nativeHermiteFormCost_nonneg (N : ℕ) : 0 ≤ nativeHermiteFormCost N :=
  mul_nonneg (Nat.cast_nonneg N) (nativeHermiteErrorNumerator_pos N).le

/-- Complete native entry error in the literal Hermite Gaussian norm. -/
theorem nativeHermiteHead_entry_error_le {x : ℝ} (N : ℕ)
    (hq : 16 * ((N : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (i j : Fin N) :
    |nativeHermiteHead N x i j - hermiteGaussianHead N i j| ≤
      (nativeHermiteErrorNumerator N / thetaCuspSingleAtomReflectionScale 1 x) *
        Real.sqrt (hermiteGaussianNormSq i.val) * Real.sqrt (hermiteGaussianNormSq j.val) := by
  have hq4 : 4 * ((N : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    nlinarith only [hq, sq_nonneg ((N : ℝ) + 2)]
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hfirst := (Complex.abs_re_le_norm _).trans
    (firstAtomWickError_normalized_jet_le (Nat.le_of_lt i.isLt) (Nat.le_of_lt j.isLt) hq4)
  change |firstAtomHermiteError N x i j| ≤ _ at hfirst
  rw [firstAtomHermiteError_eq] at hfirst
  have hprod : 1 ≤ Real.sqrt (hermiteGaussianNormSq i.val) *
      Real.sqrt (hermiteGaussianNormSq j.val) := by
    simpa only [one_mul] using mul_le_mul (hermiteGaussianNorm_ge_one i.val)
      (hermiteGaussianNorm_ge_one j.val) (by norm_num : (0 : ℝ) ≤ 1)
      (Real.sqrt_nonneg _)
  have htail := nativeHermiteHead_firstAtom_error_le N hq i j
  have htail' : |nativeHermiteHead N x i j -
      realWickJetMatrix (firstAtomNormalizedRotatedPair x) N i j| ≤
      (nativePolynomialTailConstant * Real.exp 8 / thetaCuspSingleAtomReflectionScale 1 x) *
        Real.sqrt (hermiteGaussianNormSq i.val) * Real.sqrt (hermiteGaussianNormSq j.val) := by
    apply htail.trans
    have hA := nativePolynomialTailConstant_pos
    simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hprod
      (show 0 ≤ nativePolynomialTailConstant * Real.exp 8 /
        thetaCuspSingleAtomReflectionScale 1 x by positivity)
  calc
    _ ≤ |nativeHermiteHead N x i j -
          realWickJetMatrix (firstAtomNormalizedRotatedPair x) N i j| +
        |realWickJetMatrix (firstAtomNormalizedRotatedPair x) N i j -
          hermiteGaussianHead N i j| := abs_sub_le _ _ _
    _ ≤ _ := by
      have h := add_le_add htail' hfirst
      apply h.trans_eq
      unfold nativeHermiteErrorNumerator
      ring

/-- The complete native Hermite form has a polynomial cost, independent of any inverse matrix. -/
theorem nativeHermiteHead_relative_error_le {x : ℝ} (N : ℕ)
    (hq : 16 * ((N : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (v : Fin N → ℝ) :
    |v ⬝ᵥ (nativeHermiteHead N x - hermiteGaussianHead N) *ᵥ v| ≤
      (nativeHermiteFormCost N / thetaCuspSingleAtomReflectionScale 1 x) *
        (v ⬝ᵥ hermiteGaussianHead N *ᵥ v) := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have he := weighted_entry_error_le (nativeHermiteHead N x - hermiteGaussianHead N)
    (fun i => Real.sqrt (hermiteGaussianNormSq i.val))
    (fun i => Real.sqrt_pos.mpr (hermiteGaussianNormSq_pos i.val))
    (div_nonneg (nativeHermiteErrorNumerator_pos N).le hqp.le)
    (nativeHermiteHead_entry_error_le N hq) v
  simp only [Real.sq_sqrt (hermiteGaussianNormSq_pos _).le] at he
  have hg : v ⬝ᵥ hermiteGaussianHead N *ᵥ v =
      ∑ i, hermiteGaussianNormSq i.val * v i ^ 2 := by
    simp only [hermiteGaussianHead, dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hg]
  convert he using 1
  unfold nativeHermiteFormCost
  ring

/-- The same polynomial relative error holds in the original complete native moment form. -/
theorem nativeBalancedFullHead_polynomial_rank_error_le {x : ℝ} (N : ℕ)
    (hq : 16 * ((N : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (v : Fin N → ℝ) :
    |v ⬝ᵥ (finiteHankelMatrix (nativeBalancedFullMoment x) N - gaussianFullHead N) *ᵥ v| ≤
      (nativeHermiteFormCost N / thetaCuspSingleAtomReflectionScale 1 x) *
        (v ⬝ᵥ gaussianFullHead N *ᵥ v) := by
  obtain ⟨w, hw⟩ := hermiteJetMatrix_transpose_surjective N v
  have h := nativeHermiteHead_relative_error_le N hq w
  have hquad (M : Matrix (Fin N) (Fin N) ℝ) :
      w ⬝ᵥ (hermiteJetMatrix N * M * (hermiteJetMatrix N).transpose) *ᵥ w =
        v ⬝ᵥ M *ᵥ v := by
    simpa only [star_trivial, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose, hw] using
      HTGeometry.star_dotProduct_real_congr_mulVec M (hermiteJetMatrix N).transpose w
  have he : nativeHermiteHead N x - hermiteGaussianHead N =
      hermiteJetMatrix N *
        (finiteHankelMatrix (nativeBalancedFullMoment x) N - gaussianFullHead N) *
          (hermiteJetMatrix N).transpose := by
    rw [nativeHermiteHead, hermiteGaussianHead_eq_full_congruence,
      Matrix.mul_sub, Matrix.sub_mul]
  rw [he, hermiteGaussianHead_eq_full_congruence, hquad, hquad] at h
  exact h

/-- A polynomial source scale leaves a strict half-Gaussian reserve in every native direction. -/
theorem nativeBalancedFullHead_half_posDef_of_polynomial_rank_scale {x : ℝ} (N : ℕ)
    (hq : 16 * ((N : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hscale : 2 * nativeHermiteFormCost N < thetaCuspSingleAtomReflectionScale 1 x) :
    (finiteHankelMatrix (nativeBalancedFullMoment x) N -
      (1 / 2 : ℝ) • gaussianFullHead N).PosDef := by
  have hG := gaussianFullHead_posDef N
  have hA : (finiteHankelMatrix (nativeBalancedFullMoment x) N).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [finiteHankelMatrix, Nat.add_comm]
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hη : nativeHermiteFormCost N / thetaCuspSingleAtomReflectionScale 1 x < 1 / 2 := by
    apply (div_lt_iff₀ hqp).mpr
    linarith only [hscale]
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hA.sub ((hG.smul (by norm_num : (0 : ℝ) < 1 / 2)).isHermitian), ?_⟩
  intro v hv
  rw [star_trivial]
  have hg : 0 < v ⬝ᵥ gaussianFullHead N *ᵥ v := by
    simpa only [star_trivial] using (Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 (x := v) hv
  have he := (abs_le.mp (nativeBalancedFullHead_polynomial_rank_error_le N hq v)).1
  have hs : v ⬝ᵥ (finiteHankelMatrix (nativeBalancedFullMoment x) N -
      (1 / 2 : ℝ) • gaussianFullHead N) *ᵥ v =
      v ⬝ᵥ (finiteHankelMatrix (nativeBalancedFullMoment x) N - gaussianFullHead N) *ᵥ v +
        (1 / 2) * (v ⬝ᵥ gaussianFullHead N *ᵥ v) := by
    simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    ring
  rw [hs]
  nlinarith only [he, mul_pos (sub_pos.mpr hη) hg]

#print axioms gaussianFullHead_posDef
#print axioms nativeHermiteHead_relative_error_le
#print axioms nativeBalancedFullHead_polynomial_rank_error_le
#print axioms nativeBalancedFullHead_half_posDef_of_polynomial_rank_scale

end GaloisForLFunctions.CompletedArithmeticForms
