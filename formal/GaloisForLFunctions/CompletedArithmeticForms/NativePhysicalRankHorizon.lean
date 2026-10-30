import GaloisForLFunctions.CompletedArithmeticForms.PolynomialRankHorizon

/-!
# Literal native heads on a logarithmic rank horizon

The polynomial complete-form estimate survives the exact source mass and length
rescaling. Its explicit quartic physical scale gives a logarithmic center bound
for every full signed native head and every shifted native successor.
-/

noncomputable section

open Matrix

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

/-- The physical shifted source is strict whenever its complete containing dimension is paid. -/
theorem nativeShiftedHead_posDef_of_polynomial_rank_scale (N s M : ℕ)
    (hM : 2 * N + s ≤ M) {x : ℝ}
    (hq : nativePolynomialRankScale M ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (nativeShiftedMatrix N s x).PosDef := by
  have hhalf := nativeBalancedHead_half_posDef_of_polynomial_rank_scale N s M hM hq
  have hG := (gaussianShiftedHead_posDef N s).smul (by norm_num : (0 : ℝ) < 1 / 2)
  have hA : (finiteHankelMatrix (nativeBalancedMoment s x) N).PosDef := by
    simpa only [sub_add_cancel] using hhalf.add hG
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let D : Matrix (Fin N) (Fin N) ℝ := diagonal (fun i => f * q ^ i.val)
  have hbase := (nativePolynomialRankScale_base_le M).trans hq
  have hq3 : 3 ≤ q := by
    change 16 * ((M : ℝ) + 2) ^ 2 ≤ q at hbase
    nlinarith only [hbase, Nat.cast_nonneg (α := ℝ) M, sq_nonneg (M : ℝ)]
  have hqp : 0 < q := by linarith only [hq3]
  have hf : f ≠ 0 := by
    intro h
    have hp := firstAtom_mass_pos hq3
    change 0 < f ^ 2 at hp
    rw [h, zero_pow (by omega : (2 : ℕ) ≠ 0)] at hp
    exact lt_irrefl 0 hp
  have hD : Function.Injective D.mulVec := by
    intro v w h
    funext i
    have hi := congrFun h i
    simp only [D, Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (mul_ne_zero hf (pow_ne_zero _ hqp.ne')) hi
  have he : nativeShiftedMatrix N s x =
      q ^ s • (Dᴴ * finiteHankelMatrix (nativeBalancedMoment s x) N * D) := by
    ext i j
    simp only [D, diagonal_conjTranspose, star_trivial, diagonal_mul, mul_diagonal,
      Matrix.smul_apply, smul_eq_mul, nativeShiftedMatrix, finiteHankelMatrix,
      nativeBalancedMoment, thetaCuspNativeScaledEvenJet]
    change _ = q ^ s * (f * q ^ i.val *
      (_ / (f ^ 2 * q ^ (i.val + j.val + s))) * (f * q ^ j.val))
    rw [pow_add, pow_add]
    field_simp [hf, hqp.ne']
    ring
  rw [he]
  exact (hA.conjTranspose_mul_mul_same hD).smul (pow_pos hqp s)

/-- Every complete physical signed head has a polynomial rank scale, including odd dimensions. -/
theorem nativeSignedHead_posDef_of_polynomial_rank_scale (N : ℕ) {x : ℝ}
    (hq : nativePolynomialRankScale (N + 1) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (finiteHankelMatrix (thetaCuspNativeSignedJet x) N).PosDef := by
  rw [thetaCuspNativeSignedJet_eq_evenMomentSequence,
    finiteHankelMatrix_evenMomentSequence_posDef_iff]
  exact ⟨nativeShiftedHead_posDef_of_polynomial_rank_scale ((N + 1) / 2) 0 (N + 1)
      (by omega) hq,
    nativeShiftedHead_posDef_of_polynomial_rank_scale (N / 2) 1 (N + 1) (by omega) hq⟩

/-- Explicit center horizon for the literal complete signed source. -/
theorem nativeSignedHead_posDef_of_polynomial_rank_horizon (N : ℕ) {x : ℝ}
    (hx : nativePolynomialRankHorizon (N + 1) ≤ x) :
    (finiteHankelMatrix (thetaCuspNativeSignedJet x) N).PosDef :=
  nativeSignedHead_posDef_of_polynomial_rank_scale N
    (nativePolynomialRankScale_le_of_horizon _ hx)

/-- A rank-independent coefficient for the quartic physical scale. -/
def nativeRankScaleConstant : ℝ :=
  16 + 2 * gaussianRelativeErrorConstant * Real.exp 2 +
    2 * nativePolynomialTailConstant * Real.exp 8

theorem nativeRankScaleConstant_pos : 0 < nativeRankScaleConstant := by
  have hD := gaussianRelativeErrorConstant_pos
  have hA := nativePolynomialTailConstant_pos
  unfold nativeRankScaleConstant
  positivity

/-- The physical scale is bounded by one explicit universal constant times the fourth power. -/
theorem nativePolynomialRankScale_le_quartic (M : ℕ) :
    nativePolynomialRankScale M ≤ nativeRankScaleConstant * ((M : ℝ) + 2) ^ 4 := by
  let p : ℝ := (M : ℝ) + 2
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hp : 1 ≤ p := by dsimp [p]; linarith only [hM]
  have hp24 : p ^ 2 ≤ p ^ 4 := pow_le_pow_right₀ hp (by omega : 2 ≤ 4)
  have hMp : (M : ℝ) ≤ p := by dsimp [p]; linarith
  have hp14 : p ≤ p ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hp (by omega : 1 ≤ 4)
  have hM4 := hMp.trans hp14
  have hprod : (M : ℝ) * ((M : ℝ) + 1) * p ^ 2 ≤ p ^ 4 := by
    have hm : (M : ℝ) * ((M : ℝ) + 1) ≤ p ^ 2 := by dsimp [p]; nlinarith only [hM]
    calc
      _ ≤ p ^ 2 * p ^ 2 := mul_le_mul_of_nonneg_right hm (sq_nonneg p)
      _ = _ := by ring
  have hD := gaussianRelativeErrorConstant_pos
  have hA := nativePolynomialTailConstant_pos
  have h1 := mul_le_mul_of_nonneg_left hp24 (by norm_num : (0 : ℝ) ≤ 16)
  have h2 := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 2 * gaussianRelativeErrorConstant * Real.exp 2 by positivity)
  have h3 := mul_le_mul_of_nonneg_left hM4
    (show 0 ≤ 2 * nativePolynomialTailConstant * Real.exp 8 by positivity)
  have h := add_le_add (add_le_add h1 h2) h3
  dsimp [p] at h
  unfold nativePolynomialRankScale nativeHermiteFormCost nativeHermiteErrorNumerator
    hermiteSourceErrorNumerator nativeRankScaleConstant
  nlinarith only [h]

/-- A logarithmic center bound with a rank-independent additive constant. -/
def nativeLogarithmicRankHorizon (M : ℕ) : ℝ :=
  max 0 (Real.log (nativeRankScaleConstant / Real.pi) / 2 +
    2 * Real.log ((M : ℝ) + 2))

theorem nativePolynomialRankScale_le_of_logarithmic_horizon (M : ℕ) {x : ℝ}
    (hx : nativeLogarithmicRankHorizon M ≤ x) :
    nativePolynomialRankScale M ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  have hp : 0 < (M : ℝ) + 2 := by positivity
  have hc := div_pos nativeRankScaleConstant_pos Real.pi_pos
  have hxlog : Real.log (nativeRankScaleConstant / Real.pi) +
      4 * Real.log ((M : ℝ) + 2) ≤ 2 * x := by
    have h := (le_max_right 0
      (Real.log (nativeRankScaleConstant / Real.pi) / 2 +
        2 * Real.log ((M : ℝ) + 2))).trans hx
    linarith only [h]
  have he := Real.exp_le_exp.mpr hxlog
  rw [Real.exp_add, Real.exp_log hc,
    show Real.exp (4 * Real.log ((M : ℝ) + 2)) = ((M : ℝ) + 2) ^ 4 by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hp]] at he
  have hm := mul_le_mul_of_nonneg_left he Real.pi_pos.le
  apply (nativePolynomialRankScale_le_quartic M).trans
  convert hm using 1
  · field_simp
  · simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one]

/-- Full native signed rank grows at least exponentially with half the source center. -/
theorem nativeSignedHead_posDef_of_logarithmic_rank_horizon (N : ℕ) {x : ℝ}
    (hx : nativeLogarithmicRankHorizon (N + 1) ≤ x) :
    (finiteHankelMatrix (thetaCuspNativeSignedJet x) N).PosDef :=
  nativeSignedHead_posDef_of_polynomial_rank_scale N
    (nativePolynomialRankScale_le_of_logarithmic_horizon _ hx)

/-- The same logarithmic joint rank and shift horizon pays the complete exact successor. -/
theorem nativeBalancedSuccessor_half_bounds_of_logarithmic_rank_horizon (N s : ℕ) {x : ℝ}
    (hx : nativeLogarithmicRankHorizon (2 * (N + 1) + s) ≤ x) :
    nativeGammaReserve N s / 2 < nativeBalancedSuccessor N s x ∧
      nativeBalancedSuccessor N s x < 3 * nativeGammaReserve N s / 2 :=
  nativeBalancedSuccessor_half_bounds_of_polynomial_rank_scale N s
    (nativePolynomialRankScale_le_of_logarithmic_horizon _ hx)

#print axioms nativeShiftedHead_posDef_of_polynomial_rank_scale
#print axioms nativeSignedHead_posDef_of_polynomial_rank_horizon
#print axioms nativePolynomialRankScale_le_quartic
#print axioms nativeSignedHead_posDef_of_logarithmic_rank_horizon
#print axioms nativeBalancedSuccessor_half_bounds_of_logarithmic_rank_horizon

end GaloisForLFunctions.CompletedArithmeticForms
