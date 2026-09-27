import GaloisForLFunctions.RHTower.XiGaussianDerivativeNodalBudget
import GaloisForLFunctions.RHTower.XiGaussianThirdDerivativeSaving
import GaloisForLFunctions.RHTower.XiGaussianCofactorEnvelopeSaving

/-!
# A second positive correction to the actual three-by-three relative bound

The Gaussian derivative saving is charged to the constant row of the
adjugate. That row cannot vanish for distinct nodes. Its correction is
strictly positive at every positive heat time and independent of the
polynomial coefficients being tested.
-/

open scoped Real BigOperators
open Complex GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

def xiGaussianThirdDerivativeCofactorSaving (x : Fin 3 → ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : ℝ :=
  ∑ i, ((Matrix.vandermonde x).adjugate 0 i ^ 2 * t ^ 2 / 4 *
    xiGaussianDerivativeWeight 0 s) * Real.exp (t * x i)

theorem xiGaussianThirdDerivativeCofactorSaving_nonneg (x : Fin 3 → ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) :
    0 ≤ xiGaussianThirdDerivativeCofactorSaving x s t := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (by positivity)) (xiGaussianDerivativeWeight_pos 0 s).le) (Real.exp_pos _).le

theorem xiGaussianThirdDerivativeCofactorSaving_pos
    (x : {x : Fin 3 → ℝ // Function.Injective x}) (s : {s : ℝ // 0 < s})
    (t : {t : ℝ // 0 < t}) : 0 < xiGaussianThirdDerivativeCofactorSaving x.1 s t := by
  classical
  let V := Matrix.vandermonde x.1
  have hd : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr x.property
  obtain ⟨i, hi⟩ : ∃ i, V.adjugate 0 i ≠ 0 := by
    by_contra! hall
    have h := Matrix.det_eq_sum_mul_adjugate_col V 0
    simp only [hall, mul_zero, Finset.sum_const_zero] at h
    exact hd h
  have hp : 0 < (V.adjugate 0 i ^ 2 * (t : ℝ) ^ 2 / 4 *
      xiGaussianDerivativeWeight 0 s) * Real.exp ((t : ℝ) * x.1 i) :=
    mul_pos (mul_pos (div_pos (mul_pos (sq_pos_of_ne_zero hi) (sq_pos_of_pos t.property))
      (by positivity)) (xiGaussianDerivativeWeight_pos 0 s)) (Real.exp_pos _)
  exact hp.trans_le (Finset.single_le_sum
    (fun j _ => mul_nonneg (mul_nonneg (div_nonneg
      (mul_nonneg (sq_nonneg (V.adjugate 0 j)) (sq_nonneg (t : ℝ)))
        (show (0 : ℝ) ≤ 4 by positivity))
      (xiGaussianDerivativeWeight_pos 0 s).le) (Real.exp_pos ((t : ℝ) * x.1 j)).le)
        (Finset.mem_univ i))

/-- Summing the three differentiated cofactor bounds yields a positive matrix-level saving. -/
theorem xiGaussianDerivativeCofactorEnvelope_third_add_saving_le (x : Fin 3 → ℝ)
    (s : {s : ℝ // 0 < s}) (t : {t : ℝ // 0 ≤ t}) :
    xiGaussianDerivativeCofactorEnvelope x s t +
      xiGaussianThirdDerivativeCofactorSaving x s t ≤ xiGaussianCofactorRootEnvelope x s t := by
  let V := Matrix.vandermonde x
  have hi (i : Fin 3) : xiGaussianDerivativeRootEnvelope
      (∑ j : Fin 3, Polynomial.C (V.adjugate j i) * Polynomial.X ^ (j : ℕ)) s t +
        V.adjugate 0 i ^ 2 * (t : ℝ) ^ 2 / 4 * xiGaussianDerivativeWeight 0 s ≤
          xiGaussianFiniteRootEnvelope (fun j => V.adjugate j i) s t := by
    have h := xiGaussianThirdDerivativeEnvelope_add_saving_le
      (V.adjugate 0 i) (V.adjugate 1 i) (V.adjugate 2 i) s t
    rw [← xiGaussianDerivativeRootEnvelope_third] at h
    have hP : (∑ j : Fin 3, Polynomial.C (V.adjugate j i) * Polynomial.X ^ (j : ℕ)) =
        xiHeatThirdPolynomial (V.adjugate 0 i) (V.adjugate 1 i) (V.adjugate 2 i) := by
      simp [Fin.sum_univ_three, xiHeatThirdPolynomial]
    rw [hP]
    simpa [xiGaussianFiniteRootEnvelope, Fin.sum_univ_three] using h
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_right (hi i) (Real.exp_pos ((t : ℝ) * x i)).le
  simpa only [xiGaussianDerivativeCofactorEnvelope, xiGaussianThirdDerivativeCofactorSaving,
    xiGaussianCofactorRootEnvelope_eq_sum, add_mul, Finset.sum_add_distrib, V] using h

def xiGaussianThirdRelativeDerivativeSaving (F : Finset XiZeroCopy) (x : Fin 3 → ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : ℝ :=
  (Real.exp (-((t - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
    xiGaussianThirdDerivativeCofactorSaving x s t * xiResidualOrientationBudget F) /
      (2 * (Matrix.vandermonde x).det ^ 2)

theorem xiGaussianThirdRelativeDerivativeSaving_pos (F : Finset XiZeroCopy)
    (x : {x : Fin 3 → ℝ // Function.Injective x}) (s : {s : ℝ // 0 < s})
    (t : {t : ℝ // 0 < t}) :
    0 < xiGaussianThirdRelativeDerivativeSaving F x.1 s t := by
  exact div_pos (mul_pos (mul_pos (Real.exp_pos _)
    (xiGaussianThirdDerivativeCofactorSaving_pos x s t)) (xiResidualOrientationBudget_pos F))
      (mul_pos (by positivity)
        (sq_pos_of_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr x.property)))

/-- The new coefficient-uniform ceiling is strictly improved at every positive time. -/
theorem xiGaussianDerivativeNodalBudget_third_add_saving_le (F : Finset XiZeroCopy)
    (x : Fin 3 → ℝ) (s : {s : ℝ // 0 < s}) (t : {t : ℝ // 0 ≤ t}) :
    xiGaussianDerivativeNodalBudget F x s t + xiGaussianThirdRelativeDerivativeSaving F x s t ≤
      xiGaussianNodalPhaseBudget F x s t := by
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (xiGaussianDerivativeCofactorEnvelope_third_add_saving_le x s t)
      (Real.exp_pos (-(((t : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F))).le)
        (xiResidualOrientationBudget_pos F).le
  have hd := div_le_div_of_nonneg_right h
    (show 0 ≤ 2 * (Matrix.vandermonde x).det ^ 2 by positivity)
  simpa only [xiGaussianDerivativeNodalBudget, xiGaussianThirdRelativeDerivativeSaving,
    xiGaussianNodalPhaseBudget, mul_add, add_mul, add_div] using hd

/-- Both strictly positive corrections apply simultaneously to the actual complete form. -/
theorem exists_xiHeatThirdQuadratic_two_positive_relative_savings :
    ∃ (γ : Fin 3 → ℝ) (q : Fin 3 → XiZeroCopy),
      Function.Injective (fun i => γ i ^ 2) ∧
      (∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      ∀ (F : Finset XiZeroCopy) (a b c : ℝ) (t : {t : ℝ // 0 < t}),
        0 < xiGaussianThirdRelativeDerivativeSaving F (fun i => γ i ^ 2)
          (xiGaussianHalfHeat t) t ∧
        0 < xiGaussianThirdRelativeCofactorSaving F (fun i => γ i ^ 2)
          (xiGaussianHalfHeat t) t ∧
        (1 - xiGaussianOrientationPhaseBudget F 3 (xiGaussianHalfHeat t) t /
          xiCriticalSamplingHeatFloor γ t +
            xiGaussianThirdRelativeCofactorSaving F (fun i => γ i ^ 2) (xiGaussianHalfHeat t) t +
              xiGaussianThirdRelativeDerivativeSaving F (fun i => γ i ^ 2) (xiGaussianHalfHeat t) t) *
          xiGaussianRealChannelEnergy (xiHeatThirdPolynomial a b c) t ≤
            xiHeatThirdQuadratic a b c t := by
  obtain ⟨γ, q, hinj, hq, hbound⟩ := exists_xiHeatThirdQuadratic_allTime_derivative_relative_lower
  refine ⟨γ, q, hinj, hq, ?_⟩
  intro F a b c t
  let x : {x : Fin 3 → ℝ // Function.Injective x ∧ ∀ i, 0 < x i} :=
    ⟨fun i => γ i ^ 2, hinj, fun i => sq_pos_of_pos (hq i).1⟩
  have hnew := xiGaussianDerivativeNodalBudget_third_add_saving_le F x.1
    (xiGaussianHalfHeat t) ⟨t, t.property.le⟩
  have hold := xiGaussianNodalPhaseBudget_third_add_saving_le F x.1 (xiGaussianHalfHeat t) t
  rw [xiGaussianSeparatedNodalBudget_eq_floor_ratio F γ (xiGaussianHalfHeat t) t] at hold
  change xiGaussianNodalPhaseBudget F x.1 (xiGaussianHalfHeat t) t +
    xiGaussianThirdRelativeCofactorSaving F x.1 (xiGaussianHalfHeat t) t ≤ _ at hold
  have hc : 1 - xiGaussianOrientationPhaseBudget F 3 (xiGaussianHalfHeat t) t /
      xiCriticalSamplingHeatFloor γ t +
        xiGaussianThirdRelativeCofactorSaving F x.1 (xiGaussianHalfHeat t) t +
          xiGaussianThirdRelativeDerivativeSaving F x.1 (xiGaussianHalfHeat t) t ≤
      1 - xiGaussianDerivativeNodalBudget F x.1 (xiGaussianHalfHeat t) t := by
    linarith only [hold, hnew]
  exact ⟨xiGaussianThirdRelativeDerivativeSaving_pos F ⟨x.1, x.property.1⟩ (xiGaussianHalfHeat t) t,
    xiGaussianThirdRelativeCofactorSaving_pos F x (xiGaussianHalfHeat t) t,
    (mul_le_mul_of_nonneg_right hc
      (xiGaussianRealChannelEnergy_nonneg (xiHeatThirdPolynomial a b c) t)).trans (hbound F a b c t)⟩

end RHTower
