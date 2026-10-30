import GaloisForLFunctions.CompletedArithmeticForms.NativeHermiteHorizon
import GaloisForLFunctions.CompletedArithmeticForms.NativeSuccessorHorizon

/-!
# Polynomial joint rank and shift horizons

Shifted even-moment heads are principal restrictions of one complete signed head.
The relative Hermite estimate therefore pays every shifted quadratic form and
its exact Schur successor with a polynomial rank and shift cost.
-/

noncomputable section

open Matrix Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

/-- A relative form bound survives every principal restriction with the same cost. -/
theorem relativeFormError_submatrix {M N : ℕ} {A G : Matrix (Fin M) (Fin M) ℝ}
    (hA : A.IsHermitian) (hG : G.PosSemidef) {η : ℝ} (hη : 0 ≤ η)
    (he : ∀ v, |v ⬝ᵥ (A - G) *ᵥ v| ≤ η * (v ⬝ᵥ G *ᵥ v))
    (e : Fin N → Fin M) (v : Fin N → ℝ) :
    |v ⬝ᵥ (A.submatrix e e - G.submatrix e e) *ᵥ v| ≤
      η * (v ⬝ᵥ G.submatrix e e *ᵥ v) := by
  have hηG := (hG.smul hη).isHermitian
  have hE := hA.sub hG.isHermitian
  have hp : (η • G + (A - G)).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hηG.add hE, ?_⟩
    intro w
    simp only [star_trivial, add_mulVec, smul_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    have hl := (abs_le.mp (he w)).1
    linarith only [hl]
  have hm : (η • G - (A - G)).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hηG.sub hE, ?_⟩
    intro w
    simp only [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
    simpa only [sub_mulVec, dotProduct_sub] using sub_nonneg.mpr (abs_le.mp (he w)).2
  have hl := (hp.submatrix e).dotProduct_mulVec_nonneg v
  have hu := (hm.submatrix e).dotProduct_mulVec_nonneg v
  change 0 ≤ star v ⬝ᵥ (η • G.submatrix e e + (A.submatrix e e - G.submatrix e e)) *ᵥ v at hl
  change 0 ≤ star v ⬝ᵥ (η • G.submatrix e e - (A.submatrix e e - G.submatrix e e)) *ᵥ v at hu
  simp only [star_trivial, add_mulVec, sub_mulVec, smul_mulVec,
    dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hl hu ⊢
  exact abs_le.mpr ⟨by linarith only [hl], by linarith only [hu]⟩

/-- Monomial coordinates realizing a shifted even head inside a complete signed head. -/
def shiftedEvenIndex (N s M : ℕ) (hM : 2 * N + s ≤ M) (i : Fin N) : Fin M :=
  ⟨2 * i.val + s, by omega⟩

theorem shiftedEvenIndex_injective (N s M : ℕ) (hM : 2 * N + s ≤ M) :
    Function.Injective (shiftedEvenIndex N s M hM) := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  change 2 * i.val + s = 2 * j.val + s at hv
  omega

/-- Exact principal restriction, including all shift and parity factors. -/
theorem finiteHankelMatrix_shiftedEven_submatrix (m : ℕ → ℝ) (N s M : ℕ)
    (hM : 2 * N + s ≤ M) :
    (finiteHankelMatrix (evenMomentSequence m) M).submatrix
      (shiftedEvenIndex N s M hM) (shiftedEvenIndex N s M hM) =
        finiteHankelMatrix (fun k => m (k + s)) N := by
  ext i j
  change evenMomentSequence m ((2 * i.val + s) + (2 * j.val + s)) = _
  rw [show (2 * i.val + s) + (2 * j.val + s) =
    2 * (i.val + j.val + s) by omega, evenMomentSequence_even]
  rfl

/-- A single complete signed dimension pays every shifted head it contains. -/
theorem nativeBalancedHead_polynomial_rank_error_in_dimension {x : ℝ} (N s M : ℕ)
    (hM : 2 * N + s ≤ M)
    (hq : 16 * ((M : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (v : Fin N → ℝ) :
    |v ⬝ᵥ (finiteHankelMatrix (nativeBalancedMoment s x) N -
      gaussianShiftedHead N s) *ᵥ v| ≤
      (nativeHermiteFormCost M / thetaCuspSingleAtomReflectionScale 1 x) *
        (v ⬝ᵥ gaussianShiftedHead N s *ᵥ v) := by
  have hA : (finiteHankelMatrix (nativeBalancedFullMoment x) M).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [finiteHankelMatrix, Nat.add_comm]
  have hqpos : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have h := relativeFormError_submatrix hA (gaussianFullHead_posDef M).posSemidef
    (div_nonneg (nativeHermiteFormCost_nonneg M) hqpos.le)
    (nativeBalancedFullHead_polynomial_rank_error_le M hq)
    (shiftedEvenIndex N s M hM) v
  have hn : (finiteHankelMatrix (nativeBalancedFullMoment x) M).submatrix
      (shiftedEvenIndex N s M hM) (shiftedEvenIndex N s M hM) =
      finiteHankelMatrix (nativeBalancedMoment s x) N :=
    finiteHankelMatrix_shiftedEven_submatrix (fun k => thetaCuspNativeScaledEvenJet k x) N s M hM
  have hg : (gaussianFullHead M).submatrix
      (shiftedEvenIndex N s M hM) (shiftedEvenIndex N s M hM) = gaussianShiftedHead N s :=
    finiteHankelMatrix_shiftedEven_submatrix gaussianMoment N s M hM
  rw [hn, hg] at h
  exact h

/-- Explicit quartic dependence on the joint rank and shift degree. -/
theorem nativeBalancedHead_polynomial_rank_error_le {x : ℝ} (N s : ℕ)
    (hq : 16 * (((2 * N + s : ℕ) : ℝ) + 2) ^ 2 ≤
      thetaCuspSingleAtomReflectionScale 1 x) (v : Fin N → ℝ) :
    |v ⬝ᵥ (finiteHankelMatrix (nativeBalancedMoment s x) N -
      gaussianShiftedHead N s) *ᵥ v| ≤
      (nativeHermiteFormCost (2 * N + s) / thetaCuspSingleAtomReflectionScale 1 x) *
        (v ⬝ᵥ gaussianShiftedHead N s *ᵥ v) :=
  nativeBalancedHead_polynomial_rank_error_in_dimension N s (2 * N + s) le_rfl hq v

/-- The exact mixed successor retains the same relative cost as its complete containing head. -/
theorem nativeBalancedSuccessor_polynomial_rank_error_le (N s : ℕ) {x : ℝ}
    (hq : 16 * (((2 * (N + 1) + s : ℕ) : ℝ) + 2) ^ 2 ≤
      thetaCuspSingleAtomReflectionScale 1 x)
    (hcost : nativeHermiteFormCost (2 * (N + 1) + s) <
      thetaCuspSingleAtomReflectionScale 1 x) :
    |nativeBalancedSuccessor N s x - nativeGammaReserve N s| ≤
      (nativeHermiteFormCost (2 * (N + 1) + s) / thetaCuspSingleAtomReflectionScale 1 x) *
        nativeGammaReserve N s := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have h := successorSchur_relative_error (gaussianShiftedHead_posDef (N + 1) s)
    (div_nonneg (nativeHermiteFormCost_nonneg _) hqp.le)
    ((div_lt_one hqp).mpr hcost)
    (nativeBalancedHead_polynomial_rank_error_le (N + 1) s hq)
  rw [gaussianShifted_successorSchur N s] at h
  exact h

/-- Polynomial scale paying both the source domain and a strict half-form reserve. -/
def nativePolynomialRankScale (M : ℕ) : ℝ :=
  16 * ((M : ℝ) + 2) ^ 2 + 2 * nativeHermiteFormCost M

theorem nativePolynomialRankScale_base_le (M : ℕ) :
    16 * ((M : ℝ) + 2) ^ 2 ≤ nativePolynomialRankScale M := by
  unfold nativePolynomialRankScale
  linarith only [nativeHermiteFormCost_nonneg M]

theorem nativePolynomialRankScale_pos (M : ℕ) : 0 < nativePolynomialRankScale M :=
  lt_of_lt_of_le (by positivity) (nativePolynomialRankScale_base_le M)

theorem nativePolynomialRankScale_cost_lt (M : ℕ) :
    2 * nativeHermiteFormCost M < nativePolynomialRankScale M := by
  unfold nativePolynomialRankScale
  have hp : 0 < 16 * ((M : ℝ) + 2) ^ 2 := by positivity
  linarith only [hp]

/-- A containing dimension supplies a strict half-Gaussian reserve in every shifted direction. -/
theorem nativeBalancedHead_half_posDef_of_polynomial_rank_scale (N s M : ℕ)
    (hM : 2 * N + s ≤ M) {x : ℝ}
    (hq : nativePolynomialRankScale M ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (finiteHankelMatrix (nativeBalancedMoment s x) N -
      (1 / 2 : ℝ) • gaussianShiftedHead N s).PosDef := by
  have h := (nativeBalancedFullHead_half_posDef_of_polynomial_rank_scale M
    ((nativePolynomialRankScale_base_le M).trans hq)
    ((nativePolynomialRankScale_cost_lt M).trans_le hq)).submatrix
      (shiftedEvenIndex_injective N s M hM)
  change ((finiteHankelMatrix (nativeBalancedFullMoment x) M).submatrix
      (shiftedEvenIndex N s M hM) (shiftedEvenIndex N s M hM) -
    (1 / 2 : ℝ) • (gaussianFullHead M).submatrix
      (shiftedEvenIndex N s M hM) (shiftedEvenIndex N s M hM)).PosDef at h
  have hn : (finiteHankelMatrix (nativeBalancedFullMoment x) M).submatrix
      (shiftedEvenIndex N s M hM) (shiftedEvenIndex N s M hM) =
      finiteHankelMatrix (nativeBalancedMoment s x) N :=
    finiteHankelMatrix_shiftedEven_submatrix (fun k => thetaCuspNativeScaledEvenJet k x) N s M hM
  have hg : (gaussianFullHead M).submatrix
      (shiftedEvenIndex N s M hM) (shiftedEvenIndex N s M hM) = gaussianShiftedHead N s :=
    finiteHankelMatrix_shiftedEven_submatrix gaussianMoment N s M hM
  rw [hn, hg] at h
  exact h

/-- Polynomial joint rank and shift payment for the literal exact successor. -/
theorem nativeBalancedSuccessor_half_bounds_of_polynomial_rank_scale (N s : ℕ) {x : ℝ}
    (hq : nativePolynomialRankScale (2 * (N + 1) + s) ≤
      thetaCuspSingleAtomReflectionScale 1 x) :
    nativeGammaReserve N s / 2 < nativeBalancedSuccessor N s x ∧
      nativeBalancedSuccessor N s x < 3 * nativeGammaReserve N s / 2 := by
  let M := 2 * (N + 1) + s
  have hbase := (nativePolynomialRankScale_base_le M).trans hq
  have hc := (nativePolynomialRankScale_cost_lt M).trans_le hq
  have hcost : nativeHermiteFormCost M < thetaCuspSingleAtomReflectionScale 1 x := by
    linarith only [hc, nativeHermiteFormCost_nonneg M]
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hη : nativeHermiteFormCost M / thetaCuspSingleAtomReflectionScale 1 x < 1 / 2 := by
    apply (div_lt_iff₀ hqp).mpr
    linarith only [hc]
  have he := nativeBalancedSuccessor_polynomial_rank_error_le N s hbase hcost
  have hstrict := he.trans_lt (mul_lt_mul_of_pos_right hη (nativeGammaReserve_pos N s))
  obtain ⟨hl, hu⟩ := abs_lt.mp hstrict
  constructor <;> linarith only [hl, hu]

/-- Center horizon associated with the explicit quartic physical scale. -/
def nativePolynomialRankHorizon (M : ℕ) : ℝ :=
  max 0 (Real.log (nativePolynomialRankScale M / Real.pi) / 2)

theorem nativePolynomialRankScale_le_of_horizon (M : ℕ) {x : ℝ}
    (hx : nativePolynomialRankHorizon M ≤ x) :
    nativePolynomialRankScale M ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  have hxlog : Real.log (nativePolynomialRankScale M / Real.pi) ≤ 2 * x := by
    have h := (le_max_right 0 (Real.log (nativePolynomialRankScale M / Real.pi) / 2)).trans hx
    linarith only [h]
  have he := Real.exp_le_exp.mpr hxlog
  rw [Real.exp_log (div_pos (nativePolynomialRankScale_pos M) Real.pi_pos)] at he
  have hm := mul_le_mul_of_nonneg_left he Real.pi_pos.le
  simpa only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one,
    mul_div_cancel₀ _ Real.pi_ne_zero] using hm

/-- Every center beyond the logarithm of the polynomial scale has the exact successor reserve. -/
theorem nativeBalancedSuccessor_half_bounds_of_polynomial_rank_horizon (N s : ℕ) {x : ℝ}
    (hx : nativePolynomialRankHorizon (2 * (N + 1) + s) ≤ x) :
    nativeGammaReserve N s / 2 < nativeBalancedSuccessor N s x ∧
      nativeBalancedSuccessor N s x < 3 * nativeGammaReserve N s / 2 :=
  nativeBalancedSuccessor_half_bounds_of_polynomial_rank_scale N s
    (nativePolynomialRankScale_le_of_horizon _ hx)

#print axioms nativeBalancedHead_polynomial_rank_error_le
#print axioms nativeBalancedSuccessor_polynomial_rank_error_le
#print axioms nativeBalancedHead_half_posDef_of_polynomial_rank_scale
#print axioms nativeBalancedSuccessor_half_bounds_of_polynomial_rank_horizon

end GaloisForLFunctions.CompletedArithmeticForms
