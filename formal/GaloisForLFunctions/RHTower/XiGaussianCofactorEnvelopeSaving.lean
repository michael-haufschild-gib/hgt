import GaloisForLFunctions.RHTower.XiGaussianNodalPhaseBudget
import GaloisForLFunctions.HTGeometry.ThreeNodeCauchySaving

/-!
# Quantified saving over the separated orientation/floor comparison

The complete cofactor envelope never exceeds the old product of traces.
For three distinct positive nodes, two cofactor columns force a strictly
positive, explicit saving at every anchor and every heat time.
-/

open scoped Real BigOperators
open Complex GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

theorem real_vandermonde_complex_map {N : ℕ} (x : Fin N → ℝ) :
    Complex.ofRealHom.mapMatrix (Matrix.vandermonde x) =
      Matrix.vandermonde (fun i => (x i : ℂ)) := by
  ext i j
  change ((x i ^ (j : ℕ) : ℝ) : ℂ) = (x i : ℂ) ^ (j : ℕ)
  exact Complex.ofReal_pow _ _

theorem real_vandermonde_complex_det_norm_sq {N : ℕ} (x : Fin N → ℝ) :
    ‖(Matrix.vandermonde (fun i => (x i : ℂ))).det‖ ^ 2 = (Matrix.vandermonde x).det ^ 2 := by
  have h := Complex.ofRealHom.map_det (Matrix.vandermonde x)
  rw [real_vandermonde_complex_map] at h
  rw [← h]
  change ‖((Matrix.vandermonde x).det : ℂ)‖ ^ 2 = _
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem real_vandermonde_complex_adjugate_norm_sq {N : ℕ} (x : Fin N → ℝ) (j i : Fin N) :
    ‖(Matrix.vandermonde (fun k => (x k : ℂ))).adjugate j i‖ ^ 2 =
      (Matrix.vandermonde x).adjugate j i ^ 2 := by
  have h := Complex.ofRealHom.map_adjugate (Matrix.vandermonde x)
  rw [real_vandermonde_complex_map] at h
  have he := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M j i) h
  change (((Matrix.vandermonde x).adjugate j i : ℝ) : ℂ) = _ at he
  rw [← he, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem xiGaussianCofactorRootEnvelope_le_separated {N : ℕ} (x : Fin N → ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) :
    xiGaussianCofactorRootEnvelope x s t ≤ xiGaussianOrientationEnvelope N s t *
      polynomialSamplingHeatCapacity (fun i => (x i : ℂ)) x t := by
  have h := realAdjugateHeatPhaseEnvelope_le_separated (Matrix.vandermonde x) x
    (fun j => Real.sqrt (xiGaussianOrientationMonomialEnvelope j s t)) t
  simp only [Real.sq_sqrt (xiGaussianOrientationMonomialEnvelope_nonneg _ s t)] at h
  rw [Fin.sum_univ_eq_sum_range (fun j => xiGaussianOrientationMonomialEnvelope j s t) N] at h
  simpa only [xiGaussianCofactorRootEnvelope, xiGaussianOrientationEnvelope,
    polynomialSamplingHeatCapacity, real_vandermonde_complex_adjugate_norm_sq] using h

def xiGaussianThirdCofactorSavingFloor (x : Fin 3 → ℝ) (s : {s : ℝ // 0 < s})
    (t : ℝ) : ℝ :=
  (min ((x 1 - x 2) ^ 2 * Real.exp (t * x 0))
    ((x 0 - x 2) ^ 2 * Real.exp (t * x 1)) / 2) *
      (|x 1 * x 2| - |x 0 * x 2|) ^ 2 * xiGaussianOrientationMonomialEnvelope 2 s t

/-- An explicit subtracted error term, rather than a mere alternative formulation. -/
theorem xiGaussianThirdCofactorRootEnvelope_add_saving_le (x : Fin 3 → ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) :
    xiGaussianCofactorRootEnvelope x s t + xiGaussianThirdCofactorSavingFloor x s t ≤
      xiGaussianOrientationEnvelope 3 s t *
        polynomialSamplingHeatCapacity (fun i => (x i : ℂ)) x t := by
  let r : Fin 3 → ℝ := fun j => Real.sqrt (xiGaussianOrientationMonomialEnvelope j s t)
  have hlow := realThreeVandermondeHeatDefect_lower x r t
  dsimp only [r] at hlow
  simp only [mul_pow, Real.sq_sqrt (xiGaussianOrientationMonomialEnvelope_nonneg _ s t)] at hlow
  have htwo : ((2 : Fin 3) : ℕ) = 2 := rfl
  rw [htwo] at hlow
  have hlow' : xiGaussianThirdCofactorSavingFloor x s t ≤
      realThreeAdjugateHeatDefect (Matrix.vandermonde x) x r t := by
    simpa only [xiGaussianThirdCofactorSavingFloor, mul_assoc] using hlow
  have he := realThreeAdjugateHeatDefect_identity (Matrix.vandermonde x) x r t
  dsimp only [r] at he
  simp only [Real.sq_sqrt (xiGaussianOrientationMonomialEnvelope_nonneg _ s t)] at he
  rw [Fin.sum_univ_eq_sum_range (fun j => xiGaussianOrientationMonomialEnvelope j s t) 3] at he
  have he' : xiGaussianCofactorRootEnvelope x s t +
      realThreeAdjugateHeatDefect (Matrix.vandermonde x) x r t =
        xiGaussianOrientationEnvelope 3 s t *
          polynomialSamplingHeatCapacity (fun i => (x i : ℂ)) x t := by
    simpa only [xiGaussianCofactorRootEnvelope, xiGaussianOrientationEnvelope,
      polynomialSamplingHeatCapacity, real_vandermonde_complex_adjugate_norm_sq] using he
  linarith only [hlow', he']

theorem xiGaussianOrientationMonomialEnvelope_succ_pos (j : ℕ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) :
    0 < xiGaussianOrientationMonomialEnvelope (j + 1) s t := by
  have hs := s.property
  have hf : (0 : ℝ) < ((2 * (j + 1) + 2).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * (j + 1) + 2)
  unfold xiGaussianOrientationMonomialEnvelope
  positivity

/-- Distinct positive nodes force the quantified saving to be strictly positive. -/
theorem xiGaussianThirdCofactorSavingFloor_pos
    (x : {x : Fin 3 → ℝ // Function.Injective x ∧ ∀ i, 0 < x i})
    (s : {s : ℝ // 0 < s}) (t : ℝ) : 0 < xiGaussianThirdCofactorSavingFloor x.1 s t := by
  have h01 : x.1 0 ≠ x.1 1 := x.property.1.ne (by intro h; have := congrArg Fin.val h; omega)
  have h02 : x.1 0 ≠ x.1 2 := x.property.1.ne (by intro h; have := congrArg Fin.val h; omega)
  have h12 : x.1 1 ≠ x.1 2 := x.property.1.ne (by intro h; have := congrArg Fin.val h; omega)
  have hd : |x.1 1 * x.1 2| - |x.1 0 * x.1 2| ≠ 0 := by
    rw [abs_of_pos (mul_pos (x.property.2 1) (x.property.2 2)),
      abs_of_pos (mul_pos (x.property.2 0) (x.property.2 2)), ← sub_mul]
    exact mul_ne_zero (sub_ne_zero.mpr h01.symm) (x.property.2 2).ne'
  have hw0 := mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr h12)) (Real.exp_pos (t * x.1 0))
  have hw1 := mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr h02)) (Real.exp_pos (t * x.1 1))
  unfold xiGaussianThirdCofactorSavingFloor
  exact mul_pos (mul_pos (div_pos (lt_min hw0 hw1) (by positivity)) (sq_pos_of_ne_zero hd))
    (xiGaussianOrientationMonomialEnvelope_succ_pos 1 s t)

theorem xiGaussianCofactorRootEnvelope_third_lt_separated
    (x : {x : Fin 3 → ℝ // Function.Injective x ∧ ∀ i, 0 < x i})
    (s : {s : ℝ // 0 < s}) (t : ℝ) :
    xiGaussianCofactorRootEnvelope x.1 s t < xiGaussianOrientationEnvelope 3 s t *
      polynomialSamplingHeatCapacity (fun i => (x.1 i : ℂ)) x.1 t := by
  have h := xiGaussianThirdCofactorRootEnvelope_add_saving_le x.1 s t
  have hp := xiGaussianThirdCofactorSavingFloor_pos x s t
  linarith only [h, hp]

/-- The relative ceiling never exceeds the old separated orientation/floor ceiling. -/
theorem xiGaussianNodalPhaseBudget_le_separated {N : ℕ}
    (F : Finset XiZeroCopy) (x : Fin N → ℝ) (s : {s : ℝ // 0 < s}) (t : ℝ) :
    xiGaussianNodalPhaseBudget F x s t ≤
      xiGaussianOrientationPhaseBudget F N s t *
        polynomialSamplingHeatCapacity (fun i => (x i : ℂ)) x t /
          (2 * (Matrix.vandermonde x).det ^ 2) := by
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (xiGaussianCofactorRootEnvelope_le_separated x s t)
      (Real.exp_pos (-((t - (s : ℝ)) * xiCriticalResidualPhaseGap F))).le)
        (xiResidualOrientationBudget_pos F).le
  have hd := div_le_div_of_nonneg_right h
    (show 0 ≤ 2 * (Matrix.vandermonde x).det ^ 2 by positivity)
  unfold xiGaussianNodalPhaseBudget xiGaussianOrientationPhaseBudget
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hd

/-- Quantitative improvement of the actual relative phase ceiling in degree two. -/
theorem xiGaussianNodalPhaseBudget_third_add_saving_le (F : Finset XiZeroCopy)
    (x : Fin 3 → ℝ) (s : {s : ℝ // 0 < s}) (t : ℝ) :
    xiGaussianNodalPhaseBudget F x s t +
      (Real.exp (-((t - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
        xiGaussianThirdCofactorSavingFloor x s t * xiResidualOrientationBudget F) /
          (2 * (Matrix.vandermonde x).det ^ 2) ≤
      xiGaussianOrientationPhaseBudget F 3 s t *
        polynomialSamplingHeatCapacity (fun i => (x i : ℂ)) x t /
          (2 * (Matrix.vandermonde x).det ^ 2) := by
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (xiGaussianThirdCofactorRootEnvelope_add_saving_le x s t)
      (Real.exp_pos (-((t - (s : ℝ)) * xiCriticalResidualPhaseGap F))).le)
        (xiResidualOrientationBudget_pos F).le
  have hd := div_le_div_of_nonneg_right h
    (show 0 ≤ 2 * (Matrix.vandermonde x).det ^ 2 by positivity)
  unfold xiGaussianNodalPhaseBudget xiGaussianOrientationPhaseBudget
  simpa only [mul_add, add_mul, add_div, mul_assoc, mul_left_comm, mul_comm] using hd

/-- The separated expression is exactly the previous orientation ceiling divided by its floor. -/
theorem xiGaussianSeparatedNodalBudget_eq_floor_ratio {N : ℕ} (F : Finset XiZeroCopy)
    (γ : Fin N → ℝ) (s : {s : ℝ // 0 < s}) (t : ℝ) :
    xiGaussianOrientationPhaseBudget F N s t *
        polynomialSamplingHeatCapacity (fun i => ((γ i ^ 2 : ℝ) : ℂ)) (fun i => γ i ^ 2) t /
          (2 * (Matrix.vandermonde (fun i => γ i ^ 2)).det ^ 2) =
      xiGaussianOrientationPhaseBudget F N s t / xiCriticalSamplingHeatFloor γ t := by
  unfold xiCriticalSamplingHeatFloor
  simp only [← Complex.ofReal_pow, real_vandermonde_complex_det_norm_sq]
  rw [div_div_eq_mul_div]

def xiGaussianThirdRelativeCofactorSaving (F : Finset XiZeroCopy) (x : Fin 3 → ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : ℝ :=
  (Real.exp (-((t - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
    xiGaussianThirdCofactorSavingFloor x s t * xiResidualOrientationBudget F) /
      (2 * (Matrix.vandermonde x).det ^ 2)

theorem xiGaussianThirdRelativeCofactorSaving_pos (F : Finset XiZeroCopy)
    (x : {x : Fin 3 → ℝ // Function.Injective x ∧ ∀ i, 0 < x i})
    (s : {s : ℝ // 0 < s}) (t : ℝ) :
    0 < xiGaussianThirdRelativeCofactorSaving F x.1 s t := by
  unfold xiGaussianThirdRelativeCofactorSaving
  apply div_pos
  · exact mul_pos (mul_pos (Real.exp_pos _) (xiGaussianThirdCofactorSavingFloor_pos x s t))
      (xiResidualOrientationBudget_pos F)
  · exact mul_pos (by positivity)
      (sq_pos_of_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr x.property.1))

/-- The actual three-by-three ceiling is strictly below the old orientation/floor ratio. -/
theorem xiGaussianNodalPhaseBudget_third_lt_floor_ratio (F : Finset XiZeroCopy)
    (γ : {γ : Fin 3 → ℝ // Function.Injective (fun i => γ i ^ 2) ∧ ∀ i, 0 < γ i})
    (s : {s : ℝ // 0 < s}) (t : ℝ) :
    xiGaussianNodalPhaseBudget F (fun i => γ.1 i ^ 2) s t <
      xiGaussianOrientationPhaseBudget F 3 s t / xiCriticalSamplingHeatFloor γ.1 t := by
  let x : {x : Fin 3 → ℝ // Function.Injective x ∧ ∀ i, 0 < x i} :=
    ⟨fun i => γ.1 i ^ 2, γ.property.1, fun i => sq_pos_of_pos (γ.property.2 i)⟩
  have h := xiGaussianNodalPhaseBudget_third_add_saving_le F x.1 s t
  have hp := xiGaussianThirdRelativeCofactorSaving_pos F x s t
  rw [xiGaussianSeparatedNodalBudget_eq_floor_ratio F γ.1 s t] at h
  change 0 < (Real.exp (-((t - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
    xiGaussianThirdCofactorSavingFloor x.1 s t * xiResidualOrientationBudget F) /
      (2 * (Matrix.vandermonde x.1).det ^ 2) at hp
  change xiGaussianNodalPhaseBudget F x.1 s t < _
  linarith only [h, hp]

/-- Actual nodes give a strictly positive correction to the old complete three-by-three
relative lower bound, uniformly in all coefficients and throughout positive heat time. -/
theorem exists_xiHeatThirdQuadratic_positive_cofactor_saving :
    ∃ (γ : Fin 3 → ℝ) (q : Fin 3 → XiZeroCopy),
      Function.Injective (fun i => γ i ^ 2) ∧
      (∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      ∀ (F : Finset XiZeroCopy) (a b c : ℝ) (t : {t : ℝ // 0 < t}),
        0 < xiGaussianThirdRelativeCofactorSaving F (fun i => γ i ^ 2)
          (xiGaussianHalfHeat t) t ∧
        (1 - xiGaussianOrientationPhaseBudget F 3 (xiGaussianHalfHeat t) t /
          xiCriticalSamplingHeatFloor γ t +
            xiGaussianThirdRelativeCofactorSaving F (fun i => γ i ^ 2)
              (xiGaussianHalfHeat t) t) *
          xiGaussianRealChannelEnergy (xiHeatThirdPolynomial a b c) t ≤
            xiHeatThirdQuadratic a b c t := by
  obtain ⟨γ, q, hinj, hq, hbound⟩ := exists_xiHeatHankelForm_allTime_nodal_relative_lower 3
  refine ⟨γ, q, hinj, hq, ?_⟩
  intro F a b c t
  let x : {x : Fin 3 → ℝ // Function.Injective x ∧ ∀ i, 0 < x i} :=
    ⟨fun i => γ i ^ 2, hinj, fun i => sq_pos_of_pos (hq i).1⟩
  have hs := xiGaussianNodalPhaseBudget_third_add_saving_le F x.1 (xiGaussianHalfHeat t) t
  rw [xiGaussianSeparatedNodalBudget_eq_floor_ratio F γ (xiGaussianHalfHeat t) t] at hs
  change xiGaussianNodalPhaseBudget F x.1 (xiGaussianHalfHeat t) t +
    xiGaussianThirdRelativeCofactorSaving F x.1 (xiGaussianHalfHeat t) t ≤ _ at hs
  have hc : 1 - xiGaussianOrientationPhaseBudget F 3 (xiGaussianHalfHeat t) t /
      xiCriticalSamplingHeatFloor γ t + xiGaussianThirdRelativeCofactorSaving F x.1
        (xiGaussianHalfHeat t) t ≤ 1 - xiGaussianNodalPhaseBudget F x.1 (xiGaussianHalfHeat t) t := by
    linarith only [hs]
  have hJ := xiGaussianRealChannelEnergy_nonneg (xiHeatThirdPolynomial a b c) t
  have hH := hbound F (fun n => if n = 0 then a else if n = 1 then b else c) t
  have hH' : (1 - xiGaussianNodalPhaseBudget F x.1 (xiGaussianHalfHeat t) t) *
      xiGaussianRealChannelEnergy (xiHeatThirdPolynomial a b c) t ≤ xiHeatThirdQuadratic a b c t := by
    rw [xiHeatThirdQuadratic_eq_hankel]
    simpa [Finset.sum_range_succ, xiHeatThirdPolynomial] using hH
  exact ⟨xiGaussianThirdRelativeCofactorSaving_pos F x (xiGaussianHalfHeat t) t,
    (mul_le_mul_of_nonneg_right hc hJ).trans hH'⟩

end RHTower
