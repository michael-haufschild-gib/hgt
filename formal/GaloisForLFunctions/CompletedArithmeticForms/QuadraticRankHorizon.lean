import GaloisForLFunctions.CompletedArithmeticForms.NativeQuadraticRank
import GaloisForLFunctions.CompletedArithmeticForms.PolynomialRankHorizon

/-!
# Quadratic joint rank and shift horizons

The complete native and first-atom forms retain strict half-Gaussian reserves on
one explicit quadratic physical scale. Principal monomial restriction and the
exact Schur comparison preserve that payment for every shift and successor.
-/

noncomputable section

open Matrix

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

/-- A complete relative form bound below one half leaves a strict half reserve. -/
theorem halfReserve_posDef_of_relative_error {N : ℕ} {A G : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (hG : G.PosDef) {η : ℝ} (hη : η < 1 / 2)
    (he : ∀ v, |v ⬝ᵥ (A - G) *ᵥ v| ≤ η * (v ⬝ᵥ G *ᵥ v)) :
    (A - (1 / 2 : ℝ) • G).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hA.sub ((hG.smul (by norm_num : (0 : ℝ) < 1 / 2)).isHermitian), ?_⟩
  intro v hv
  rw [star_trivial]
  have hg : 0 < v ⬝ᵥ G *ᵥ v := by
    simpa only [star_trivial] using (Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 (x := v) hv
  have hl := (abs_le.mp (he v)).1
  have hs : v ⬝ᵥ (A - (1 / 2 : ℝ) • G) *ᵥ v =
      v ⬝ᵥ (A - G) *ᵥ v + (1 / 2) * (v ⬝ᵥ G *ᵥ v) := by
    simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    ring
  rw [hs]
  nlinarith only [hl, mul_pos (sub_pos.mpr hη) hg]

/-- Every shifted even-moment relative bound is a restriction of the complete signed bound. -/
theorem relativeFormError_shifted_of_full (m : ℕ → ℝ) (N s M : ℕ)
    (hM : 2 * N + s ≤ M) {η : ℝ} (hη : 0 ≤ η)
    (he : ∀ v, |v ⬝ᵥ (finiteHankelMatrix (evenMomentSequence m) M - gaussianFullHead M) *ᵥ v| ≤
      η * (v ⬝ᵥ gaussianFullHead M *ᵥ v)) (v : Fin N → ℝ) :
    |v ⬝ᵥ (finiteHankelMatrix (fun k => m (k + s)) N - gaussianShiftedHead N s) *ᵥ v| ≤
      η * (v ⬝ᵥ gaussianShiftedHead N s *ᵥ v) := by
  have hA : (finiteHankelMatrix (evenMomentSequence m) M).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [finiteHankelMatrix, Nat.add_comm]
  have h := relativeFormError_submatrix hA (gaussianFullHead_posDef M).posSemidef hη he
    (shiftedEvenIndex N s M hM) v
  have hg : (gaussianFullHead M).submatrix
      (shiftedEvenIndex N s M hM) (shiftedEvenIndex N s M hM) = gaussianShiftedHead N s :=
    finiteHankelMatrix_shiftedEven_submatrix gaussianMoment N s M hM
  rw [finiteHankelMatrix_shiftedEven_submatrix m N s M hM, hg] at h
  exact h

/-- The complete native shifted form has a quadratic joint rank and shift cost. -/
theorem nativeBalancedHead_quadratic_rank_error_in_dimension {x : ℝ} (N s M : ℕ)
    (hM : 2 * N + s ≤ M)
    (hq : 16 * ((M : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (v : Fin N → ℝ) :
    |v ⬝ᵥ (finiteHankelMatrix (nativeBalancedMoment s x) N - gaussianShiftedHead N s) *ᵥ v| ≤
      (nativeQuadraticFormCost M / thetaCuspSingleAtomReflectionScale 1 x) *
        (v ⬝ᵥ gaussianShiftedHead N s *ᵥ v) := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  exact relativeFormError_shifted_of_full (fun k => thetaCuspNativeScaledEvenJet k x) N s M hM
    (div_nonneg (nativeQuadraticFormCost_pos M).le hqp.le)
    (nativeBalancedFullHead_quadratic_rank_error_le M hq) v

/-- The literal first-atom shifted form has the same quadratic degree domain. -/
theorem firstAtomBalancedHead_quadratic_rank_error_in_dimension {x : ℝ} (N s M : ℕ)
    (hM : 2 * N + s ≤ M)
    (hq : 16 * ((M : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (v : Fin N → ℝ) :
    |v ⬝ᵥ (finiteHankelMatrix (firstAtomBalancedMoment s x) N - gaussianShiftedHead N s) *ᵥ v| ≤
      (firstAtomQuadraticFormCost M / thetaCuspSingleAtomReflectionScale 1 x) *
        (v ⬝ᵥ gaussianShiftedHead N s *ᵥ v) := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  exact relativeFormError_shifted_of_full (fun k => thetaCuspFirstAtomScaledEvenJet k x) N s M hM
    (div_nonneg (firstAtomQuadraticFormCost_pos M).le hqp.le)
    (firstAtomBalancedFullHead_quadratic_rank_error_le M hq) v

/-- The exact native successor preserves the quadratic full-form relative payment. -/
theorem nativeBalancedSuccessor_quadratic_rank_error_le (N s : ℕ) {x : ℝ}
    (hq : 16 * (((2 * (N + 1) + s : ℕ) : ℝ) + 2) ^ 2 ≤
      thetaCuspSingleAtomReflectionScale 1 x)
    (hc : nativeQuadraticFormCost (2 * (N + 1) + s) <
      thetaCuspSingleAtomReflectionScale 1 x) :
    |nativeBalancedSuccessor N s x - nativeGammaReserve N s| ≤
      (nativeQuadraticFormCost (2 * (N + 1) + s) / thetaCuspSingleAtomReflectionScale 1 x) *
        nativeGammaReserve N s := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have h := successorSchur_relative_error (gaussianShiftedHead_posDef (N + 1) s)
    (div_nonneg (nativeQuadraticFormCost_pos _).le hqp.le)
    ((div_lt_one hqp).mpr hc)
    (nativeBalancedHead_quadratic_rank_error_in_dimension (N + 1) s (2 * (N + 1) + s)
      le_rfl hq)
  rw [gaussianShifted_successorSchur N s] at h
  exact h

/-- One quadratic scale pays the complete source domain and a strict half reserve. -/
def nativeQuadraticRankScale (M : ℕ) : ℝ :=
  16 * ((M : ℝ) + 2) ^ 2 + 2 * nativeQuadraticFormCost M

theorem nativeQuadraticRankScale_base_le (M : ℕ) :
    16 * ((M : ℝ) + 2) ^ 2 ≤ nativeQuadraticRankScale M := by
  unfold nativeQuadraticRankScale
  linarith only [nativeQuadraticFormCost_pos M]

theorem nativeQuadraticRankScale_pos (M : ℕ) : 0 < nativeQuadraticRankScale M :=
  lt_of_lt_of_le (by positivity) (nativeQuadraticRankScale_base_le M)

theorem nativeQuadraticRankScale_cost_lt (M : ℕ) :
    2 * nativeQuadraticFormCost M < nativeQuadraticRankScale M := by
  unfold nativeQuadraticRankScale
  have hp : 0 < 16 * ((M : ℝ) + 2) ^ 2 := by positivity
  linarith only [hp]

theorem firstAtomQuadraticFormCost_le_native (M : ℕ) :
    firstAtomQuadraticFormCost M ≤ nativeQuadraticFormCost M := by
  have hA := nativePolynomialTailConstant_pos
  have ht : 0 ≤ (M : ℝ) * nativePolynomialTailConstant * Real.exp 8 := by positivity
  unfold nativeQuadraticFormCost
  linarith only [ht]

/-- Strict half-Gaussian reserve of every contained complete native shifted head. -/
theorem nativeBalancedHead_half_posDef_of_quadratic_rank_scale (N s M : ℕ)
    (hM : 2 * N + s ≤ M) {x : ℝ}
    (hq : nativeQuadraticRankScale M ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (finiteHankelMatrix (nativeBalancedMoment s x) N -
      (1 / 2 : ℝ) • gaussianShiftedHead N s).PosDef := by
  have hA : (finiteHankelMatrix (nativeBalancedMoment s x) N).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [finiteHankelMatrix, Nat.add_comm]
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  apply halfReserve_posDef_of_relative_error hA (gaussianShiftedHead_posDef N s)
    (η := nativeQuadraticFormCost M / thetaCuspSingleAtomReflectionScale 1 x)
  · apply (div_lt_iff₀ hqp).mpr
    have hc := (nativeQuadraticRankScale_cost_lt M).trans_le hq
    linarith only [hc]
  · exact nativeBalancedHead_quadratic_rank_error_in_dimension N s M hM
      ((nativeQuadraticRankScale_base_le M).trans hq)

/-- The same source scale leaves a half-Gaussian reserve for the literal first atom. -/
theorem firstAtomBalancedHead_half_posDef_of_quadratic_rank_scale (N s M : ℕ)
    (hM : 2 * N + s ≤ M) {x : ℝ}
    (hq : nativeQuadraticRankScale M ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (finiteHankelMatrix (firstAtomBalancedMoment s x) N -
      (1 / 2 : ℝ) • gaussianShiftedHead N s).PosDef := by
  have hA : (finiteHankelMatrix (firstAtomBalancedMoment s x) N).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [finiteHankelMatrix, Nat.add_comm]
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  apply halfReserve_posDef_of_relative_error hA (gaussianShiftedHead_posDef N s)
    (η := firstAtomQuadraticFormCost M / thetaCuspSingleAtomReflectionScale 1 x)
  · apply (div_lt_iff₀ hqp).mpr
    have hc := (nativeQuadraticRankScale_cost_lt M).trans_le hq
    linarith only [hc, firstAtomQuadraticFormCost_le_native M]
  · exact firstAtomBalancedHead_quadratic_rank_error_in_dimension N s M hM
      ((nativeQuadraticRankScale_base_le M).trans hq)

/-- Complete native successors lie within strict half/three-halves bounds on a quadratic scale. -/
theorem nativeBalancedSuccessor_half_bounds_of_quadratic_rank_scale (N s : ℕ) {x : ℝ}
    (hq : nativeQuadraticRankScale (2 * (N + 1) + s) ≤
      thetaCuspSingleAtomReflectionScale 1 x) :
    nativeGammaReserve N s / 2 < nativeBalancedSuccessor N s x ∧
      nativeBalancedSuccessor N s x < 3 * nativeGammaReserve N s / 2 := by
  let M := 2 * (N + 1) + s
  have hbase := (nativeQuadraticRankScale_base_le M).trans hq
  have hc := (nativeQuadraticRankScale_cost_lt M).trans_le hq
  have hcost : nativeQuadraticFormCost M < thetaCuspSingleAtomReflectionScale 1 x := by
    linarith only [hc, nativeQuadraticFormCost_pos M]
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hη : nativeQuadraticFormCost M / thetaCuspSingleAtomReflectionScale 1 x < 1 / 2 := by
    apply (div_lt_iff₀ hqp).mpr
    linarith only [hc]
  have he := nativeBalancedSuccessor_quadratic_rank_error_le N s hbase hcost
  have hstrict := he.trans_lt (mul_lt_mul_of_pos_right hη (nativeGammaReserve_pos N s))
  obtain ⟨hl, hu⟩ := abs_lt.mp hstrict
  constructor <;> linarith only [hl, hu]

#print axioms nativeBalancedHead_quadratic_rank_error_in_dimension
#print axioms nativeBalancedSuccessor_quadratic_rank_error_le
#print axioms nativeBalancedHead_half_posDef_of_quadratic_rank_scale
#print axioms firstAtomBalancedHead_half_posDef_of_quadratic_rank_scale
#print axioms nativeBalancedSuccessor_half_bounds_of_quadratic_rank_scale

end GaloisForLFunctions.CompletedArithmeticForms
