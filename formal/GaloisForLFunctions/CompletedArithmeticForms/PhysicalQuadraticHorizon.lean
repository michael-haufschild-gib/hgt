import GaloisForLFunctions.CompletedArithmeticForms.QuadraticRankHorizon

/-!
# Physical rank growth on the square-root source scale

The exact source mass and length rescaling carries the quadratic complete-form
reserve to both literal native and first-atom heads. The first failing physical
first-atom dimension consequently has a square-root lower bound in source scale.
-/

noncomputable section

open Matrix

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

private theorem physicalShiftedHead_posDef_of_normalized (m : ℕ → ℝ) (N s : ℕ)
    {f q : ℝ} (hf : f ≠ 0) (hq : 0 < q)
    (hA : (finiteHankelMatrix (fun k => m (k + s) / (f ^ 2 * q ^ (k + s))) N).PosDef) :
    (finiteHankelMatrix (fun k => m (k + s)) N).PosDef := by
  let D : Matrix (Fin N) (Fin N) ℝ := diagonal (fun i => f * q ^ i.val)
  have hD : Function.Injective D.mulVec := by
    intro v w h
    funext i
    have hi := congrFun h i
    simp only [D, Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (mul_ne_zero hf (pow_ne_zero _ hq.ne')) hi
  have he : finiteHankelMatrix (fun k => m (k + s)) N =
      q ^ s • (Dᴴ * finiteHankelMatrix
        (fun k => m (k + s) / (f ^ 2 * q ^ (k + s))) N * D) := by
    ext i j
    simp only [D, diagonal_conjTranspose, star_trivial, diagonal_mul, mul_diagonal,
      Matrix.smul_apply, smul_eq_mul, finiteHankelMatrix]
    rw [pow_add, pow_add]
    field_simp [hf, hq.ne']
  rw [he]
  exact (hA.conjTranspose_mul_mul_same hD).smul (pow_pos hq s)

private theorem firstAtom_source_ne_zero_on_quadratic_scale {M : ℕ} {x : ℝ}
    (hq : nativeQuadraticRankScale M ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspSourceTerm x 1 ≠ 0 := by
  have hb := (nativeQuadraticRankScale_base_le M).trans hq
  have hq3 : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    nlinarith only [hb, Nat.cast_nonneg (α := ℝ) M, sq_nonneg (M : ℝ)]
  intro hzero
  have hp := firstAtom_mass_pos hq3
  rw [hzero, zero_pow (by omega : (2 : ℕ) ≠ 0)] at hp
  exact lt_irrefl 0 hp

/-- Quadratic rank payment makes the physical complete native shifted head strict. -/
theorem nativeShiftedHead_posDef_of_quadratic_rank_scale (N s M : ℕ)
    (hM : 2 * N + s ≤ M) {x : ℝ}
    (hq : nativeQuadraticRankScale M ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (nativeShiftedMatrix N s x).PosDef := by
  have hhalf := nativeBalancedHead_half_posDef_of_quadratic_rank_scale N s M hM hq
  have hG := (gaussianShiftedHead_posDef N s).smul (by norm_num : (0 : ℝ) < 1 / 2)
  have hA : (finiteHankelMatrix (nativeBalancedMoment s x) N).PosDef := by
    simpa only [sub_add_cancel] using hhalf.add hG
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  exact physicalShiftedHead_posDef_of_normalized
    (fun k => (-1 : ℝ) ^ k * thetaCuspNativeReflectionJet (2 * k) x) N s
    (firstAtom_source_ne_zero_on_quadratic_scale hq) hqp hA

/-- The same quadratic scale makes the physical first-atom shifted head strict. -/
theorem firstAtomShiftedHead_posDef_of_quadratic_rank_scale (N s M : ℕ)
    (hM : 2 * N + s ≤ M) {x : ℝ}
    (hq : nativeQuadraticRankScale M ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (finiteHankelMatrix
      (fun k => (-1 : ℝ) ^ (k + s) * thetaCuspFirstAtomReflectionJet (2 * (k + s)) x) N).PosDef := by
  have hhalf := firstAtomBalancedHead_half_posDef_of_quadratic_rank_scale N s M hM hq
  have hG := (gaussianShiftedHead_posDef N s).smul (by norm_num : (0 : ℝ) < 1 / 2)
  have hA : (finiteHankelMatrix (firstAtomBalancedMoment s x) N).PosDef := by
    simpa only [sub_add_cancel] using hhalf.add hG
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  exact physicalShiftedHead_posDef_of_normalized
    (fun k => (-1 : ℝ) ^ k * thetaCuspFirstAtomReflectionJet (2 * k) x) N s
    (firstAtom_source_ne_zero_on_quadratic_scale hq) hqp hA

/-- Literal complete native signed heads have a quadratic physical rank scale. -/
theorem nativeSignedHead_posDef_of_quadratic_rank_scale (N : ℕ) {x : ℝ}
    (hq : nativeQuadraticRankScale (N + 1) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (finiteHankelMatrix (thetaCuspNativeSignedJet x) N).PosDef := by
  rw [thetaCuspNativeSignedJet_eq_evenMomentSequence,
    finiteHankelMatrix_evenMomentSequence_posDef_iff]
  exact ⟨nativeShiftedHead_posDef_of_quadratic_rank_scale ((N + 1) / 2) 0 (N + 1)
      (by omega) hq,
    nativeShiftedHead_posDef_of_quadratic_rank_scale (N / 2) 1 (N + 1) (by omega) hq⟩

/-- Literal first-atom signed heads share the complete quadratic source horizon. -/
theorem firstAtomSignedHead_posDef_of_quadratic_rank_scale (N : ℕ) {x : ℝ}
    (hq : nativeQuadraticRankScale (N + 1) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (finiteHankelMatrix (firstAtomSignedSequence x) N).PosDef := by
  rw [firstAtomSignedSequence_eq_evenMomentSequence,
    finiteHankelMatrix_evenMomentSequence_posDef_iff]
  exact ⟨firstAtomShiftedHead_posDef_of_quadratic_rank_scale ((N + 1) / 2) 0 (N + 1)
      (by omega) hq,
    firstAtomShiftedHead_posDef_of_quadratic_rank_scale (N / 2) 1 (N + 1) (by omega) hq⟩

/-- No physical first-atom mixed failure occurs below the paid quadratic rank horizon. -/
theorem firstAtomFailureRank_gt_of_quadratic_rank_scale (N : ℕ) {x : ℝ}
    (hq : nativeQuadraticRankScale (N + 1) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    N < firstAtomFailureRank x := by
  have hA := (firstAtomSignedHead_posDef_of_quadratic_rank_scale N hq).posSemidef
  by_contra h
  have hle : firstAtomFailureRank x ≤ N := le_of_not_gt h
  let e : Fin (firstAtomFailureRank x) → Fin N := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hle⟩
  have hsub := hA.submatrix e
  have he : (finiteHankelMatrix (firstAtomSignedSequence x) N).submatrix e e =
      finiteHankelMatrix (firstAtomSignedSequence x) (firstAtomFailureRank x) := by
    ext i j
    rfl
  rw [he] at hsub
  exact firstAtomFailureRank_spec x hsub

/-- Universal coefficient of the quadratic physical rank scale. -/
def nativeQuadraticScaleConstant : ℝ :=
  16 + 32 * gaussianRelativeErrorConstant + 2 * nativePolynomialTailConstant * Real.exp 8

theorem nativeQuadraticScaleConstant_pos : 0 < nativeQuadraticScaleConstant := by
  have hD := gaussianRelativeErrorConstant_pos
  have hA := nativePolynomialTailConstant_pos
  unfold nativeQuadraticScaleConstant
  positivity

theorem nativeQuadraticRankScale_le_quadratic (M : ℕ) :
    nativeQuadraticRankScale M ≤ nativeQuadraticScaleConstant * ((M : ℝ) + 2) ^ 2 := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h1 : ((M : ℝ) + 1) ^ 2 ≤ ((M : ℝ) + 2) ^ 2 := by nlinarith only [hM]
  have h2 : (M : ℝ) ≤ ((M : ℝ) + 2) ^ 2 := by nlinarith only [hM, sq_nonneg (M : ℝ)]
  have hD := gaussianRelativeErrorConstant_pos
  have hA := nativePolynomialTailConstant_pos
  have hm1 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 32 * gaussianRelativeErrorConstant by positivity)
  have hm2 := mul_le_mul_of_nonneg_left h2
    (show 0 ≤ 2 * nativePolynomialTailConstant * Real.exp 8 by positivity)
  unfold nativeQuadraticRankScale nativeQuadraticFormCost firstAtomQuadraticFormCost
    nativeQuadraticScaleConstant
  nlinarith only [hm1, hm2]

/-- Logarithmic center bound at the square-root physical rank scale. -/
def nativeQuadraticRankHorizon (M : ℕ) : ℝ :=
  max 0 (Real.log (nativeQuadraticScaleConstant / Real.pi) / 2 + Real.log ((M : ℝ) + 2))

theorem nativeQuadraticRankScale_le_of_horizon (M : ℕ) {x : ℝ}
    (hx : nativeQuadraticRankHorizon M ≤ x) :
    nativeQuadraticRankScale M ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  have hp : 0 < (M : ℝ) + 2 := by positivity
  have hc := div_pos nativeQuadraticScaleConstant_pos Real.pi_pos
  have hxlog : Real.log (nativeQuadraticScaleConstant / Real.pi) +
      2 * Real.log ((M : ℝ) + 2) ≤ 2 * x := by
    have h := (le_max_right 0
      (Real.log (nativeQuadraticScaleConstant / Real.pi) / 2 +
        Real.log ((M : ℝ) + 2))).trans hx
    linarith only [h]
  have he := Real.exp_le_exp.mpr hxlog
  rw [Real.exp_add, Real.exp_log hc,
    show Real.exp (2 * Real.log ((M : ℝ) + 2)) = ((M : ℝ) + 2) ^ 2 by
      rw [show 2 * Real.log ((M : ℝ) + 2) =
        Real.log ((M : ℝ) + 2) + Real.log ((M : ℝ) + 2) by ring,
        Real.exp_add, Real.exp_log hp]
      ring] at he
  have hm := mul_le_mul_of_nonneg_left he Real.pi_pos.le
  apply (nativeQuadraticRankScale_le_quadratic M).trans
  convert hm using 1
  · field_simp
  · simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one]

/-- Complete physical native signed rank is paid on a center horizon logarithmic in rank. -/
theorem nativeSignedHead_posDef_of_quadratic_rank_horizon (N : ℕ) {x : ℝ}
    (hx : nativeQuadraticRankHorizon (N + 1) ≤ x) :
    (finiteHankelMatrix (thetaCuspNativeSignedJet x) N).PosDef :=
  nativeSignedHead_posDef_of_quadratic_rank_scale N (nativeQuadraticRankScale_le_of_horizon _ hx)

/-- The exact native shifted successor has the same logarithmic joint rank and shift horizon. -/
theorem nativeBalancedSuccessor_half_bounds_of_quadratic_rank_horizon (N s : ℕ) {x : ℝ}
    (hx : nativeQuadraticRankHorizon (2 * (N + 1) + s) ≤ x) :
    nativeGammaReserve N s / 2 < nativeBalancedSuccessor N s x ∧
      nativeBalancedSuccessor N s x < 3 * nativeGammaReserve N s / 2 :=
  nativeBalancedSuccessor_half_bounds_of_quadratic_rank_scale N s
    (nativeQuadraticRankScale_le_of_horizon _ hx)

/-- The first physical mixed failure requires rank beyond the quadratic source horizon. -/
theorem firstAtomFailureRank_gt_of_quadratic_rank_horizon (N : ℕ) {x : ℝ}
    (hx : nativeQuadraticRankHorizon (N + 1) ≤ x) : N < firstAtomFailureRank x :=
  firstAtomFailureRank_gt_of_quadratic_rank_scale N (nativeQuadraticRankScale_le_of_horizon _ hx)

/-- The literal first-atom failure dimension has an unconditional square-root lower boundary. -/
theorem firstAtomFailureRank_sqrt_scale_lower (x : ℝ) :
    Real.sqrt (thetaCuspSingleAtomReflectionScale 1 x / nativeQuadraticScaleConstant) <
      (firstAtomFailureRank x : ℝ) + 3 := by
  have hq : thetaCuspSingleAtomReflectionScale 1 x <
      nativeQuadraticScaleConstant * ((firstAtomFailureRank x : ℝ) + 3) ^ 2 := by
    by_contra h
    have hle := le_of_not_gt h
    have hb := nativeQuadraticRankScale_le_quadratic (firstAtomFailureRank x + 1)
    have he : nativeQuadraticScaleConstant * (((firstAtomFailureRank x + 1 : ℕ) : ℝ) + 2) ^ 2 =
        nativeQuadraticScaleConstant * ((firstAtomFailureRank x : ℝ) + 3) ^ 2 := by
      push_cast
      ring
    rw [he] at hb
    exact Nat.lt_irrefl _ (firstAtomFailureRank_gt_of_quadratic_rank_scale
      (firstAtomFailureRank x) (hb.trans hle))
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hdiv : thetaCuspSingleAtomReflectionScale 1 x / nativeQuadraticScaleConstant <
      ((firstAtomFailureRank x : ℝ) + 3) ^ 2 := by
    apply (div_lt_iff₀ nativeQuadraticScaleConstant_pos).mpr
    nlinarith only [hq]
  have hs := Real.sq_sqrt (div_pos hqp nativeQuadraticScaleConstant_pos).le
  nlinarith only [hs, hdiv,
    Real.sqrt_nonneg (thetaCuspSingleAtomReflectionScale 1 x / nativeQuadraticScaleConstant),
    Nat.cast_nonneg (α := ℝ) (firstAtomFailureRank x)]

#print axioms nativeSignedHead_posDef_of_quadratic_rank_scale
#print axioms firstAtomSignedHead_posDef_of_quadratic_rank_scale
#print axioms nativeSignedHead_posDef_of_quadratic_rank_horizon
#print axioms nativeBalancedSuccessor_half_bounds_of_quadratic_rank_horizon
#print axioms firstAtomFailureRank_sqrt_scale_lower

end GaloisForLFunctions.CompletedArithmeticForms
