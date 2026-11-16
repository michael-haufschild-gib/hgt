import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeTraceAtAPrimaryPrimeIsInvariantUnderTheModularGroup

/-!
# The Hecke points at a primary prime of a ramified cusp are ramified

For `M ∈ SL₂(O)`, the Hecke points `A_p^{±1}Mx` are `N'Ux` with `N' ∈ SL₂(O)` of first column
`(pM₀₀, M₁₀)/g` (resp. `(M₀₀, pM₁₀)/g`), `g ∣ p`, and `U` upper triangular with `|U₀₀|² = |g|²/|p|`
(`dilation_factor`, `contraction_factor`). Since `p ≡ 1 mod 3`, the column residue modulo `3` of `(M₀₀, M₁₀)` is
unchanged, so a ramified point stays ramified, and the height changes by `|g|²/|p| ∈ [1/|p|, |p|]`. Hence
`θ_s` decays exponentially at both Hecke points of a ramified point (`sourceTheta_hecke_ramified`).
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem colRes_p_left (x y : O) : colRes (P.p * x) y = colRes x y := by
  rw [colRes, colRes, cuspResidue_congr (show (3 : O) ∣ P.p * x - x from by
    obtain ⟨t, ht⟩ := P.three_dvd_sub_one
    exact ⟨t * x, by linear_combination x * ht⟩)]

theorem colRes_p_right (x y : O) : colRes x (P.p * y) = colRes x y := by
  rw [colRes, colRes, cuspResidue_congr (show (3 : O) ∣ P.p * y - y from by
    obtain ⟨t, ht⟩ := P.three_dvd_sub_one
    exact ⟨t * y, by linear_combination y * ht⟩)]

theorem root_inv_mul : P.root⁻¹ * ringComplex P.p = P.root := by
  rw [← P.root_sq]
  field_simp [P.root_ne_zero]

theorem norm_root_sq : ‖P.root‖ ^ 2 = ‖ringComplex P.p‖ := by
  rw [← norm_pow, P.root_sq]

/-- The Hecke point `A_pMx`: `A_pM = N'U` with `N'` of first column `(pM₀₀, M₁₀)/g`, `|U₀₀|² = |g|²/|p|`. -/
theorem dilation_factor (M : SL(2, O)) :
    ∃ (N' : SL(2, O)) (g : O), g ≠ 0 ∧ P.p * M 0 0 = g * N' 0 0 ∧ M 1 0 = g * N' 1 0 ∧
      ∃ U : SL(2, ℂ), U 1 0 = 0 ∧ ‖U 0 0‖ ^ 2 = ‖ringComplex g‖ ^ 2 / ‖ringComplex P.p‖ ∧
        P.dilation * integralComplexMatrix M = integralComplexMatrix N' * U := by
  have hM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact M.det_coe
  have hnz : ¬(P.p * M 0 0 = 0 ∧ M 1 0 = 0) := by
    rintro ⟨h1, h2⟩
    have h0 : M 0 0 = 0 := (mul_eq_zero.mp h1).resolve_left P.ne_zero
    rw [h0, h2] at hM
    simp at hM
  obtain ⟨g, p', q', a, b, hg, hp, hq, hab⟩ := exists_column_factor _ _ hnz
  refine ⟨columnCompletion p' q' a b hab, g, hg, by simp [columnCompletion, hp], by simp [columnCompletion, hq], ?_⟩
  set N' := columnCompletion p' q' a b hab
  have hr' := P.root_inv_mul
  have hp' := congrArg ringComplex hp
  have hq' := congrArg ringComplex hq
  have hab' := congrArg ringComplex hab
  simp only [map_mul, map_add, map_one] at hp' hq' hab'
  have hinv : ((integralComplexMatrix N')⁻¹ : SL(2, ℂ)) = integralComplexMatrix N'⁻¹ := (map_inv _ _).symm
  refine ⟨(integralComplexMatrix N')⁻¹ * (P.dilation * integralComplexMatrix M), ?_, ?_, by group⟩
  · rw [hinv]
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, integralComplexMatrix,
      Matrix.SpecialLinearGroup.SL2_inv_expl, N', columnCompletion, PrimaryPrime.dilation, complexDiagonal,
      Matrix.vecMul, dotProduct, Matrix.map_apply]
    linear_combination (-(ringComplex q') * P.root⁻¹) * hp' + (ringComplex p' * P.root⁻¹) * hq' +
      (ringComplex q' * ringComplex (M 0 0)) * hr'
  · rw [hinv]
    have h00 : (integralComplexMatrix N'⁻¹ * (P.dilation * integralComplexMatrix M)) 0 0 =
        ringComplex g * P.root⁻¹ := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, integralComplexMatrix,
        Matrix.SpecialLinearGroup.SL2_inv_expl, N', columnCompletion, PrimaryPrime.dilation, complexDiagonal,
        Matrix.vecMul, dotProduct, Matrix.map_apply]
      linear_combination (ringComplex a * P.root⁻¹) * hp' + (ringComplex b * P.root⁻¹) * hq' +
        (P.root⁻¹ * ringComplex g) * hab' - (ringComplex a * ringComplex (M 0 0)) * hr'
    rw [h00, norm_mul, mul_pow, norm_inv, inv_pow, P.norm_root_sq, div_eq_mul_inv]

/-- The Hecke point `A_p⁻¹Mx`: `A_p⁻¹M = N'U` with `N'` of first column `(M₀₀, pM₁₀)/g`. -/
theorem contraction_factor (M : SL(2, O)) :
    ∃ (N' : SL(2, O)) (g : O), g ≠ 0 ∧ M 0 0 = g * N' 0 0 ∧ P.p * M 1 0 = g * N' 1 0 ∧
      ∃ U : SL(2, ℂ), U 1 0 = 0 ∧ ‖U 0 0‖ ^ 2 = ‖ringComplex g‖ ^ 2 / ‖ringComplex P.p‖ ∧
        P.contraction * integralComplexMatrix M = integralComplexMatrix N' * U := by
  have hM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact M.det_coe
  have hnz : ¬(M 0 0 = 0 ∧ P.p * M 1 0 = 0) := by
    rintro ⟨h1, h2⟩
    have h0 : M 1 0 = 0 := (mul_eq_zero.mp h2).resolve_left P.ne_zero
    rw [h1, h0] at hM
    simp at hM
  obtain ⟨g, p', q', a, b, hg, hp, hq, hab⟩ := exists_column_factor _ _ hnz
  refine ⟨columnCompletion p' q' a b hab, g, hg, by simp [columnCompletion, hp], by simp [columnCompletion, hq], ?_⟩
  set N' := columnCompletion p' q' a b hab
  have hr' := P.root_inv_mul
  have hp' := congrArg ringComplex hp
  have hq' := congrArg ringComplex hq
  have hab' := congrArg ringComplex hab
  simp only [map_mul, map_add, map_one] at hp' hq' hab'
  have hinv : ((integralComplexMatrix N')⁻¹ : SL(2, ℂ)) = integralComplexMatrix N'⁻¹ := (map_inv _ _).symm
  refine ⟨(integralComplexMatrix N')⁻¹ * (P.contraction * integralComplexMatrix M), ?_, ?_, by group⟩
  · rw [hinv]
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, integralComplexMatrix,
      Matrix.SpecialLinearGroup.SL2_inv_expl, N', columnCompletion, PrimaryPrime.contraction, complexDiagonal,
      Matrix.vecMul, dotProduct, Matrix.map_apply]
    linear_combination (-(ringComplex q') * P.root⁻¹) * hp' + (ringComplex p' * P.root⁻¹) * hq' -
      (ringComplex p' * ringComplex (M 1 0)) * hr'
  · rw [hinv]
    have h00 : (integralComplexMatrix N'⁻¹ * (P.contraction * integralComplexMatrix M)) 0 0 =
        ringComplex g * P.root⁻¹ := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, integralComplexMatrix,
        Matrix.SpecialLinearGroup.SL2_inv_expl, N', columnCompletion, PrimaryPrime.contraction, complexDiagonal,
        Matrix.vecMul, dotProduct, Matrix.map_apply]
      linear_combination (ringComplex a * P.root⁻¹) * hp' + (ringComplex b * P.root⁻¹) * hq' +
        (P.root⁻¹ * ringComplex g) * hab' - (ringComplex b * ringComplex (M 1 0)) * hr'
    rw [h00, norm_mul, mul_pow, norm_inv, inv_pow, P.norm_root_sq, div_eq_mul_inv]

/-- A divisor of `p` has squared absolute value at most `|p|²`. -/
theorem norm_sq_le_of_mul {g k : O} (h : g * k = P.p) : ‖ringComplex g‖ ^ 2 ≤ ‖ringComplex P.p‖ ^ 2 := by
  have hk : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact P.ne_zero h.symm
  have hk1 := one_le_norm_sq_ringComplex hk
  have hn : ‖ringComplex g‖ ^ 2 * ‖ringComplex k‖ ^ 2 = ‖ringComplex P.p‖ ^ 2 := by
    rw [← mul_pow, ← norm_mul, ← map_mul, h]
  nlinarith [sq_nonneg ‖ringComplex g‖]

/-- **The Hecke points at `p` of a ramified point are ramified.** -/
theorem sourceTheta_hecke_ramified (a : ℝ) (ha : 0 < a) :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 < β ∧ ∀ (M : SL(2, O)), colRes (M 0 0) (M 1 0) ≠ 0 →
      ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
        ‖sourceTheta (P.dilation • integralComplexMatrix M • upperPoint z v hv)‖ ≤
            C * Real.exp (-(β / ‖ringComplex P.p‖) * v) ∧
        ‖sourceTheta (P.contraction • integralComplexMatrix M • upperPoint z v hv)‖ ≤
          C * Real.exp (-(β / ‖ringComplex P.p‖) * v) := by
  have hn := P.norm_pos
  obtain ⟨C, β, hC, hβ, hdec⟩ := sourceTheta_ramified_decay (a / ‖ringComplex P.p‖) (div_pos ha hn)
  have hM : ∀ M : SL(2, O), M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := fun M => by
    rw [← Matrix.det_fin_two]; exact M.det_coe
  have hfin : ∀ (g : O) (N' : SL(2, O)) (U : SL(2, ℂ)), g ≠ 0 → U 1 0 = 0 →
      ‖U 0 0‖ ^ 2 = ‖ringComplex g‖ ^ 2 / ‖ringComplex P.p‖ → colRes (N' 0 0) (N' 1 0) ≠ 0 →
      ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
        ‖sourceTheta (integralComplexMatrix N' • U • upperPoint z v hv)‖ ≤
          C * Real.exp (-(β / ‖ringComplex P.p‖) * v) := by
    intro g N' U hg hU10 hU00 hcol z v hv hav
    have hg1 := one_le_norm_sq_ringComplex hg
    obtain ⟨z', v', hv', hpt⟩ := upperPoint_surjective (U • upperPoint z v hv)
    have hvv : v' = v * (‖ringComplex g‖ ^ 2 / ‖ringComplex P.p‖) := by
      have h := height_upper_triangular_complex U hU10 z v hv
      rw [← hpt, hyperbolicHeight_upperPoint, hU00] at h
      exact h
    have hvlow : v / ‖ringComplex P.p‖ ≤ v' := by
      rw [hvv, mul_div_assoc']
      exact div_le_div_of_nonneg_right (by nlinarith) hn.le
    rw [← hpt]
    have hav' : a / ‖ringComplex P.p‖ ≤ v' :=
      le_trans (div_le_div_of_nonneg_right hav hn.le) hvlow
    refine (hdec N' hcol z' v' hv' hav').trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
    have : β * (v / ‖ringComplex P.p‖) ≤ β * v' := mul_le_mul_of_nonneg_left hvlow hβ.le
    rw [show -(β / ‖ringComplex P.p‖) * v = -(β * (v / ‖ringComplex P.p‖)) by ring]
    linarith
  refine ⟨C, β, hC, hβ, fun M hcol z v hv hav => ⟨?_, ?_⟩⟩
  · obtain ⟨N', g, hg, hp, hq, U, hU10, hU00, hfac⟩ := P.dilation_factor M
    have hc : colRes (N' 0 0) (N' 1 0) ≠ 0 := by
      refine colRes_ne_zero_of_factor hp hq ?_
      rw [P.colRes_p_left]
      exact hcol
    rw [← mul_smul, hfac, mul_smul]
    exact hfin g N' U hg hU10 hU00 hc z v hv hav
  · obtain ⟨N', g, hg, hp, hq, U, hU10, hU00, hfac⟩ := P.contraction_factor M
    have hc : colRes (N' 0 0) (N' 1 0) ≠ 0 := by
      refine colRes_ne_zero_of_factor hp hq ?_
      rw [P.colRes_p_right]
      exact hcol
    rw [← mul_smul, hfac, mul_smul]
    exact hfin g N' U hg hU10 hU00 hc z v hv hav

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
