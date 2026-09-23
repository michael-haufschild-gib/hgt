import GaloisForLFunctions.HTGeometry.FokasLenellsRawOddFifthCovariance

/-!
# Actual regularized reflection after two inverse spectral powers

Equation (3.63) weights the two original reflection channels differently.
The corpus's upper coefficient is the paper's r1; its lower coefficient
is -r2. After division by z^(2 : ℕ) only the upper channel carries the
compatibility pole. The lower channel always has a finite right limit.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The paper's second inverse-frequency weight on the actual regularized coefficients. -/
def regularSecondInverseReflection (q : SchwartzMap ℝ ℂ) (reverse : Bool) (z : ℝ) : ℂ :=
  (if reverse then regularReverseReflectionCoefficient q z else regularReflectionCoefficient q z)/(z : ℂ)^(2 : ℕ)

theorem regularSecondInverseReflection_measurable (q : SchwartzMap ℝ ℂ) (reverse : Bool) :
    Measurable (regularSecondInverseReflection q reverse) := by
  have hc (i j : Fin 2) : Measurable (fun z => regularScatteringMatrix q z i j) :=
    ((continuous_apply j).comp ((continuous_apply i).comp (continuous_regularScatteringMatrix q))).measurable
  cases reverse
  · exact ((hc 1 0).div (hc 0 0)).div (Complex.measurable_ofReal.pow_const 2)
  · exact ((hc 0 1).div (hc 1 1)).div (Complex.measurable_ofReal.pow_const 2)

/-- Exact gauge bridge to the already evaluated original weighted profile. -/
theorem regularSecondInverseReflection_exp_factor (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    regularSecondInverseReflection q false ((Real.exp κ)^(2 : ℕ)) =
      -2*((Real.exp κ : ℂ)^(2 : ℕ)*originWeightedReflection q ((Real.exp κ)^(2 : ℕ)))/
        regularScatteringMatrix q ((Real.exp κ)^(2 : ℕ)) 0 0 ∧
    regularSecondInverseReflection q true ((Real.exp κ)^(2 : ℕ)) =
      originWeightedReflection q ((Real.exp κ)^(2 : ℕ))/(2*regularScatteringMatrix q ((Real.exp κ)^(2 : ℕ)) 1 1) := by
  have hS := uniformizedScatteringMatrix_amplitudes q κ
  change regularScatteringMatrix q ((Real.exp κ)^(2 : ℕ)) = _ at hS
  have hd0 : regularScatteringMatrix q ((Real.exp κ)^(2 : ℕ)) 0 0 = transmission q κ := by rw [hS]; rfl
  have hd1 : regularScatteringMatrix q ((Real.exp κ)^(2 : ℕ)) 1 1 = reverseTransmission q κ := by rw [hS]; rfl
  have he : (Real.exp κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos κ))
  have h0 := (regularReflectionCoefficients_gauge q κ).1
  have h1 := (regularReflectionCoefficients_gauge q κ).2
  constructor
  · simp only [regularSecondInverseReflection,Bool.false_eq_true,↓reduceIte,h0,
      originWeightedReflection_exp,hd0,reflectionCoefficient,Complex.ofReal_pow]
    by_cases ht : transmission q κ = 0
    · simp [ht]
    · field_simp [he,ht]
  · simp only [regularSecondInverseReflection,↓reduceIte,h1,originWeightedReflection_exp,hd1,
      reverseReflectionCoefficient,reverseReflectionAmplitude_eq_neg,
      Complex.ofReal_pow]
    by_cases ht : reverseTransmission q κ = 0
    · simp [ht]
    · field_simp [he,ht]

private theorem regular_second_inverse_positive_factor (q : SchwartzMap ℝ ℂ) (z : ℝ) (hz : 0 < z) :
    regularSecondInverseReflection q false z = -2*((z : ℂ)*originWeightedReflection q z)/regularScatteringMatrix q z 0 0 ∧
    regularSecondInverseReflection q true z = originWeightedReflection q z/(2*regularScatteringMatrix q z 1 1) := by
  have hh := regularSecondInverseReflection_exp_factor q (Real.log (Real.sqrt z))
  have he : (Real.exp (Real.log (Real.sqrt z)))^(2 : ℕ) = z := by
    rw [Real.exp_log (Real.sqrt_pos.mpr hz)]
    exact Real.sq_sqrt hz.le
  have hec : (Real.exp (Real.log (Real.sqrt z)) : ℂ)^(2 : ℕ) = (z : ℂ) := by exact_mod_cast he
  simpa only [he,hec] using hh

/-- Both actual regularized transmissions tend to one at the origin. -/
theorem regularTransmission_diagonal_tendsto_zero (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Tendsto (fun z : ℝ => regularScatteringMatrix q z i i) (𝓝 0) (𝓝 1) := by
  have hc : Continuous (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i i) := by fun_prop
  have hh := (hc.tendsto 1).comp (regularScatteringMatrix_tendsto_zero q)
  change Tendsto (fun z : ℝ => regularScatteringMatrix q z i i) (𝓝 0) (𝓝 ((1 : Matrix (Fin 2) (Fin 2) ℂ) i i)) at hh
  simpa only [Matrix.one_apply_eq] using hh

/-- The weighted lower channel (-r2 in the paper) always has a finite right limit. -/
theorem regularSecondInverseReflection_lower_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (regularSecondInverseReflection q false) (𝓝[>] 0) (𝓝 (-4*compatibilityMoment q)) := by
  have ha : Tendsto (fun z : ℝ => regularScatteringMatrix q z 0 0) (𝓝[>] 0) (𝓝 1) :=
    (regularTransmission_diagonal_tendsto_zero q 0).mono_left nhdsWithin_le_nhds
  have hh := ((originWeightedReflection_mul_coordinate_tendsto q).const_mul (-2 : ℂ)).div ha one_ne_zero
  have he : (-2 : ℂ)*(2*compatibilityMoment q)/1 = -4*compatibilityMoment q := by ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (regular_second_inverse_positive_factor q z hz).1.symm

/-- The upper weighted channel (r1 in the paper) has compatibility moment as its exact reciprocal residue. -/
theorem regularSecondInverseReflection_upper_residue_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun z : ℝ => (z : ℂ)*regularSecondInverseReflection q true z)
      (𝓝[>] 0) (𝓝 (compatibilityMoment q)) := by
  have ha : Tendsto (fun z : ℝ => regularScatteringMatrix q z 1 1) (𝓝[>] 0) (𝓝 1) :=
    (regularTransmission_diagonal_tendsto_zero q 1).mono_left nhdsWithin_le_nhds
  have hh := (originWeightedReflection_mul_coordinate_tendsto q).div (ha.const_mul (2 : ℂ)) (by norm_num)
  have he : (2*compatibilityMoment q)/(2*1) = compatibilityMoment q := by ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  change ((z : ℂ)*originWeightedReflection q z)/(2*regularScatteringMatrix q z 1 1) =
    (z : ℂ)*regularSecondInverseReflection q true z
  rw [(regular_second_inverse_positive_factor q z hz).2]
  exact mul_div_assoc _ _ _

/-- Exactly compatible profiles have a finite upper weighted limit. -/
theorem regularSecondInverseReflection_upper_finite_limit_iff (q : SchwartzMap ℝ ℂ) :
    (∃ c : ℂ, Tendsto (regularSecondInverseReflection q true) (𝓝[>] 0) (𝓝 c)) ↔
      compatibilityMoment q = 0 := by
  constructor
  · rintro ⟨c,hc⟩
    have hz : Tendsto (fun z : ℝ => (z : ℂ)) (𝓝[>] 0) (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    have hh := hz.mul hc
    simp only [zero_mul] at hh
    exact tendsto_nhds_unique (regularSecondInverseReflection_upper_residue_tendsto q) hh
  · intro hm
    have ht : Tendsto (originWeightedReflection q) (𝓝[>] 0)
        (𝓝 (rawScatteringFifthCoefficient q 1 0)) := by
      simpa only [hm,mul_zero,zero_div,sub_zero] using originWeightedReflection_sub_pole_tendsto q
    have ha : Tendsto (fun z : ℝ => regularScatteringMatrix q z 1 1) (𝓝[>] 0) (𝓝 1) :=
      (regularTransmission_diagonal_tendsto_zero q 1).mono_left nhdsWithin_le_nhds
    refine ⟨rawScatteringFifthCoefficient q 1 0/2,?_⟩
    have hh := ht.div (ha.const_mul (2 : ℂ)) (by norm_num)
    simp only [mul_one] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (regular_second_inverse_positive_factor q z hz).2.symm

/-- The actual transmission factor can be restored on an origin neighborhood. -/
theorem regularSecondInverseReflection_upper_eventually_restore (q : SchwartzMap ℝ ℂ) :
    ∀ᶠ z : ℝ in 𝓝[>] 0, originWeightedReflection q z =
      (2*regularScatteringMatrix q z 1 1)*regularSecondInverseReflection q true z := by
  have hn : ∀ᶠ z : ℝ in 𝓝[>] 0, regularScatteringMatrix q z 1 1 ≠ 0 :=
    ((regularTransmission_diagonal_tendsto_zero q 1).eventually_ne one_ne_zero).filter_mono nhdsWithin_le_nhds
  filter_upwards [hn,self_mem_nhdsWithin] with z hn hz
  rw [(regular_second_inverse_positive_factor q z hz).2]
  field_simp

/-- Near zero, local integrability of the actual upper quotient controls the original compatibility pole. -/
theorem regularSecondInverseReflection_upper_eventually_controls_origin (q : SchwartzMap ℝ ℂ) :
    ∀ᶠ z : ℝ in 𝓝[>] 0, ‖originWeightedReflection q z‖ ≤ 4*‖regularSecondInverseReflection q true z‖ := by
  have hb : ∀ᶠ z : ℝ in 𝓝[>] 0, ‖regularScatteringMatrix q z 1 1‖ ≤ 2 := by
    have hh := (regularTransmission_diagonal_tendsto_zero q 1).norm.eventually_le_const
      (show ‖(1 : ℂ)‖ < 2 by norm_num)
    exact hh.filter_mono nhdsWithin_le_nhds
  filter_upwards [hb,regularSecondInverseReflection_upper_eventually_restore q] with z hb he
  rw [he,norm_mul,norm_mul]
  simp only [norm_ofNat]
  nlinarith [norm_nonneg (regularSecondInverseReflection q true z)]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
