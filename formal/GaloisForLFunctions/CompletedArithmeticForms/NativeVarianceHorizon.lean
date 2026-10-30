import GaloisForLFunctions.CompletedArithmeticForms.NativePolynomialHorizon
import GaloisForLFunctions.CompletedArithmeticForms.WeightedInverseStability
import GaloisForLFunctions.CompletedArithmeticForms.NativeSuccessorHorizon

/-!
# Variance-weighted mixed and successor horizons of the complete native source

The polynomial source error is relative to each actual Gaussian moment. Its
full mixed-form payment is the variance-weighted inverse cost of the complete
Gamma head. The same payment controls the exact native Schur successor.
-/

noncomputable section

open Matrix Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

/-- Coordinate variances paired with their exact dual costs in the shifted Gamma head. -/
def gaussianVarianceInverseCost (N s : ℕ) : ℝ := varianceInverseCost (gaussianShiftedHead N s)

theorem gaussianVarianceInverseCost_nonneg (N s : ℕ) : 0 ≤ gaussianVarianceInverseCost N s :=
  varianceInverseCost_nonneg (gaussianShiftedHead_posDef N s)

theorem dimension_le_gaussianVarianceInverseCost (N s : ℕ) :
    (N : ℝ) ≤ gaussianVarianceInverseCost N s :=
  dimension_le_varianceInverseCost (gaussianShiftedHead_posDef N s)

theorem gaussianVarianceInverseCost_eq_cofactor_div (N s : ℕ) :
    gaussianVarianceInverseCost N s =
      (∑ i : Fin N, gaussianMoment (i.val + i.val + s) *
        (gaussianShiftedHead N s).adjugate i i) /
      (∏ i : Fin N, gaussianMoment s * 16 ^ (2 * i.val) *
        (i.val.factorial : ℝ) * gammaShapeMoment ((s : ℝ) + 1 / 2) i.val) := by
  rw [gaussianVarianceInverseCost, varianceInverseCost_eq_cofactor_div, det_gaussianShiftedHead]
  rfl

/-- Relative mixed-form numerator, retaining polynomial order cost and the infinite theta remainder. -/
def nativePolynomialMixedErrorNumerator (N s : ℕ) : ℝ :=
  (N : ℝ) * gaussianVarianceInverseCost N s *
    (3 * ((s + 2 * N : ℕ) : ℝ) ^ 2 + nativePolynomialTailConstant)

theorem nativePolynomialMixedErrorNumerator_nonneg (N s : ℕ) :
    0 ≤ nativePolynomialMixedErrorNumerator N s := by
  have hV := gaussianVarianceInverseCost_nonneg N s
  have hA := nativePolynomialTailConstant_pos
  unfold nativePolynomialMixedErrorNumerator
  positivity

/-- Complete native mixed entries have a joint relative error in the full Gamma norm. -/
theorem nativeBalancedHead_polynomial_relative_error_le (N s : ℕ) {x : ℝ}
    (hq : nativePolynomialOrderScale (s + 2 * N) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (v : Fin N → ℝ) :
    |v ⬝ᵥ (finiteHankelMatrix (nativeBalancedMoment s x) N - gaussianShiftedHead N s) *ᵥ v| ≤
      (nativePolynomialMixedErrorNumerator N s / thetaCuspSingleAtomReflectionScale 1 x) *
        (v ⬝ᵥ gaussianShiftedHead N s *ᵥ v) := by
  let ε := (3 * ((s + 2 * N : ℕ) : ℝ) ^ 2 + nativePolynomialTailConstant) /
    thetaCuspSingleAtomReflectionScale 1 x
  have hq0 : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hε : 0 ≤ ε := by
    have hA := nativePolynomialTailConstant_pos
    dsimp [ε]
    positivity
  have hentry (i j : Fin N) :
      |finiteHankelMatrix (nativeBalancedMoment s x) N i j - gaussianShiftedHead N s i j| ≤
        ε * |gaussianShiftedHead N s i j| := by
    have h := nativeScaledEvenJet_quadratic_relative_error_le_through
      (show i.val + j.val + s ≤ s + 2 * N by omega) hq
    change |thetaCuspNativeScaledEvenJet (i.val + j.val + s) x -
      gaussianMoment (i.val + j.val + s)| ≤ ε * |gaussianMoment (i.val + j.val + s)|
    rw [abs_of_pos (gaussianMoment_positive _)]
    convert h using 1
    dsimp [ε]
    ring
  have h := relative_entry_error_le_varianceInverseCost (gaussianShiftedHead_posDef N s) hε hentry v
  convert h using 1
  dsimp [nativePolynomialMixedErrorNumerator, gaussianVarianceInverseCost, ε]
  ring

/-- Paying half the mixed-form cost leaves a strict half-Gamma reserve. -/
theorem nativeBalancedHead_half_posDef_of_polynomial_scale (N s : ℕ) {x : ℝ}
    (hq : nativePolynomialOrderScale (s + 2 * N) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hcost : 2 * nativePolynomialMixedErrorNumerator N s < thetaCuspSingleAtomReflectionScale 1 x) :
    (finiteHankelMatrix (nativeBalancedMoment s x) N -
      (1 / 2 : ℝ) • gaussianShiftedHead N s).PosDef := by
  have hG := gaussianShiftedHead_posDef N s
  have hq0 : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hc : nativePolynomialMixedErrorNumerator N s /
      thetaCuspSingleAtomReflectionScale 1 x < 1 / 2 := by
    apply (div_lt_iff₀ hq0).mpr
    linarith only [hcost]
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian]
    ext i j
    simp [finiteHankelMatrix, gaussianShiftedHead, Nat.add_comm]
  · intro v hv
    rw [star_trivial]
    have hg : 0 < v ⬝ᵥ gaussianShiftedHead N s *ᵥ v := by
      simpa only [star_trivial] using (Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 (x := v) hv
    have he := (abs_le.mp (nativeBalancedHead_polynomial_relative_error_le N s hq v)).1
    have hs : v ⬝ᵥ (finiteHankelMatrix (nativeBalancedMoment s x) N -
        (1 / 2 : ℝ) • gaussianShiftedHead N s) *ᵥ v =
      v ⬝ᵥ (finiteHankelMatrix (nativeBalancedMoment s x) N - gaussianShiftedHead N s) *ᵥ v +
        (1 / 2) * (v ⬝ᵥ gaussianShiftedHead N s *ᵥ v) := by
      simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      ring
    rw [hs]
    nlinarith only [he, mul_pos (sub_pos.mpr hc) hg]

/-- The exact native Schur successor inherits the same relative polynomial payment. -/
theorem nativeBalancedSuccessor_polynomial_relative_error_le (N s : ℕ) {x : ℝ}
    (hq : nativePolynomialOrderScale (s + 2 * (N + 1)) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hcost : nativePolynomialMixedErrorNumerator (N + 1) s < thetaCuspSingleAtomReflectionScale 1 x) :
    |nativeBalancedSuccessor N s x - nativeGammaReserve N s| ≤
      (nativePolynomialMixedErrorNumerator (N + 1) s / thetaCuspSingleAtomReflectionScale 1 x) *
        nativeGammaReserve N s := by
  have hq0 : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hη := div_nonneg (nativePolynomialMixedErrorNumerator_nonneg (N + 1) s) hq0.le
  have hη1 : nativePolynomialMixedErrorNumerator (N + 1) s /
      thetaCuspSingleAtomReflectionScale 1 x < 1 := (div_lt_one hq0).mpr hcost
  have h := successorSchur_relative_error (gaussianShiftedHead_posDef (N + 1) s)
    hη hη1 (nativeBalancedHead_polynomial_relative_error_le (N + 1) s hq)
  rw [gaussianShifted_successorSchur N s] at h
  exact h

/-- Explicit source scale for a strict half-Gamma native successor. -/
def nativePolynomialSuccessorScale (N s : ℕ) : ℝ :=
  nativePolynomialOrderScale (s + 2 * (N + 1)) +
    2 * nativePolynomialMixedErrorNumerator (N + 1) s

theorem nativePolynomialSuccessorScale_ge_six (N s : ℕ) :
    6 ≤ nativePolynomialSuccessorScale N s := by
  unfold nativePolynomialSuccessorScale
  linarith only [nativePolynomialOrderScale_ge_six (s + 2 * (N + 1)),
    nativePolynomialMixedErrorNumerator_nonneg (N + 1) s]

theorem nativeBalancedSuccessor_half_bounds_of_polynomial_scale (N s : ℕ) {x : ℝ}
    (hq : nativePolynomialSuccessorScale N s ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    nativeGammaReserve N s / 2 < nativeBalancedSuccessor N s x ∧
      nativeBalancedSuccessor N s x < 3 * nativeGammaReserve N s / 2 := by
  have hdom := nativePolynomialOrderScale_ge_six (s + 2 * (N + 1))
  have hC := nativePolynomialMixedErrorNumerator_nonneg (N + 1) s
  have hbase : nativePolynomialOrderScale (s + 2 * (N + 1)) ≤
      thetaCuspSingleAtomReflectionScale 1 x := by
    unfold nativePolynomialSuccessorScale at hq
    linarith only [hq, hC]
  have hhalf : 2 * nativePolynomialMixedErrorNumerator (N + 1) s <
      thetaCuspSingleAtomReflectionScale 1 x := by
    unfold nativePolynomialSuccessorScale at hq
    linarith only [hq, hdom]
  have hpay : nativePolynomialMixedErrorNumerator (N + 1) s <
      thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hhalf, hC]
  have hq0 : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hη : nativePolynomialMixedErrorNumerator (N + 1) s /
      thetaCuspSingleAtomReflectionScale 1 x < 1 / 2 := by
    apply (div_lt_iff₀ hq0).mpr
    linarith only [hhalf]
  have he := nativeBalancedSuccessor_polynomial_relative_error_le N s hbase hpay
  have hs := he.trans_lt (mul_lt_mul_of_pos_right hη (nativeGammaReserve_pos N s))
  obtain ⟨hl, hu⟩ := abs_lt.mp hs
  constructor <;> linarith only [hl, hu]

/-- Physical center for the polynomial native-successor horizon. -/
def nativePolynomialSuccessorHorizon (N s : ℕ) : ℝ :=
  max 0 (Real.log (nativePolynomialSuccessorScale N s / Real.pi) / 2)

theorem nativeBalancedSuccessor_half_bounds_of_polynomial_horizon (N s : ℕ) {x : ℝ}
    (hx : nativePolynomialSuccessorHorizon N s ≤ x) :
    nativeGammaReserve N s / 2 < nativeBalancedSuccessor N s x ∧
      nativeBalancedSuccessor N s x < 3 * nativeGammaReserve N s / 2 := by
  have hQ : 0 < nativePolynomialSuccessorScale N s :=
    lt_of_lt_of_le (by norm_num) (nativePolynomialSuccessorScale_ge_six N s)
  have hxlog : Real.log (nativePolynomialSuccessorScale N s / Real.pi) ≤ 2 * x := by
    have h := (le_max_right 0 (Real.log (nativePolynomialSuccessorScale N s / Real.pi) / 2)).trans hx
    linarith only [h]
  have he := Real.exp_le_exp.mpr hxlog
  rw [Real.exp_log (div_pos hQ Real.pi_pos)] at he
  have hm := mul_le_mul_of_nonneg_left he Real.pi_pos.le
  apply nativeBalancedSuccessor_half_bounds_of_polynomial_scale N s
  simpa only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one,
    mul_div_cancel₀ _ Real.pi_ne_zero] using hm

#print axioms gaussianVarianceInverseCost_eq_cofactor_div
#print axioms nativeBalancedHead_polynomial_relative_error_le
#print axioms nativeBalancedHead_half_posDef_of_polynomial_scale
#print axioms nativeBalancedSuccessor_polynomial_relative_error_le
#print axioms nativeBalancedSuccessor_half_bounds_of_polynomial_horizon

end GaloisForLFunctions.CompletedArithmeticForms
