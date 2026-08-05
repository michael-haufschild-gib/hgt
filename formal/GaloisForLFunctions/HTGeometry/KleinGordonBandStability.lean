import GaloisForLFunctions.HTGeometry.KleinGordonConditionalStability

/-!
# Stability on a frequency band, in both directions

The conditional stability estimate carries a free parameter: the probing time. It is not a
restriction — an admissible probing time always exists, and how short it must be depends only on the
frequency cut-off and on the size of the perturbations. Making the choice gives a constant with no
free parameters,

`‖W₁ − W₂‖ ≤ 8η(1+bT)(T⁻² + 8((1+R²)/2 + b e^{bT}))`,

and pairing it with the Lipschitz estimate in the other direction says that on each band the field
discrepancy and the potential discrepancy control each other. That is the classical formulation of a
well-posed inverse problem, and it holds here for every fixed band even though it fails without the
band.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Band

variable {W₁ W₂ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- An admissible probing time always exists, and `min T (8K)^{-1/2}` is one. -/
theorem exists_probe_time {R T b : ℝ} (hb0 : 0 ≤ b) (hT0 : 0 < T) :
    ∃ x : ℝ, 0 < x ∧ x ≤ T
      ∧ x ^ 2 * ((1 + R ^ 2) / 2 + b * Real.exp (b * T)) ≤ 1 / 8
      ∧ 1 / x ^ 2 ≤ 1 / T ^ 2 + 8 * ((1 + R ^ 2) / 2 + b * Real.exp (b * T)) := by
  set K : ℝ := (1 + R ^ 2) / 2 + b * Real.exp (b * T) with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  have hinv0 : (0 : ℝ) < 1 / (8 * K) := by positivity
  set c : ℝ := Real.sqrt (1 / (8 * K)) with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr hinv0
  have hcsq : c ^ 2 = 1 / (8 * K) := Real.sq_sqrt hinv0.le
  refine ⟨min T c, lt_min hT0 hc0, min_le_left _ _, ?_, ?_⟩
  · have hle : min T c ≤ c := min_le_right _ _
    have hsq : (min T c) ^ 2 ≤ c ^ 2 :=
      pow_le_pow_left₀ (le_of_lt (lt_min hT0 hc0)) hle 2
    rw [hcsq] at hsq
    have hstep : (min T c) ^ 2 * K ≤ 1 / (8 * K) * K :=
      mul_le_mul_of_nonneg_right hsq hK0.le
    have hval : 1 / (8 * K) * K = 1 / 8 := by field_simp
    linarith
  · have hK8 : (0 : ℝ) < 8 * K := by positivity
    rcases min_cases T c with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq]
      have : (0 : ℝ) ≤ 8 * K := hK8.le
      linarith
    · rw [heq, hcsq]
      have hval : 1 / (1 / (8 * K)) = 8 * K := by field_simp
      rw [hval]
      have hT2 : (0 : ℝ) < 1 / T ^ 2 := by positivity
      linarith

/-- **Conditional stability with an explicit constant.** No free parameter: the probing time has been
chosen, and what is left depends only on the frequency cut-off `R`, the size `b` of the
perturbations, and the observation window `T`. -/
theorem norm_sub_le_of_lowPass_explicit (hb0 : 0 ≤ b) (hW₁ : ‖W₁‖ ≤ b) (hW₂ : ‖W₂‖ ≤ b) {R : ℝ}
    (hAdom : ∀ v : Lp ℂ 2 (volume : Measure E),
      (W₁ - W₂) (kgLowPassOp R v) = (W₁ - W₂) v)
    (hAran : ∀ v : Lp ℂ 2 (volume : Measure E),
      kgLowPassOp R ((W₁ - W₂) v) = (W₁ - W₂) v)
    {η T : ℝ} (hη0 : 0 ≤ η) (hT0 : 0 < T)
    (hobs : ∀ (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
      ‖kgFieldMild W₁ g k t - kgFieldMild W₂ g k t‖ ≤ η * (‖g‖ + ‖k‖)) :
    ‖W₁ - W₂‖ ≤ 8 * (η * (1 + b * T))
      * (1 / T ^ 2 + 8 * ((1 + R ^ 2) / 2 + b * Real.exp (b * T))) := by
  obtain ⟨x, hx0, hxT, hxK, hxinv⟩ := exists_probe_time (R := R) (T := T) (b := b) hb0 hT0
  have hmain := norm_sub_le_of_lowPass hb0 hW₁ hW₂ hAdom hAran hη0 hx0 hxT hxK hobs
  refine hmain.trans ?_
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  have hcoef : (0 : ℝ) ≤ 8 * (η * (1 + b * T)) := by positivity
  have hrw : 8 * (η * (1 + b * T)) / x ^ 2 = 8 * (η * (1 + b * T)) * (1 / x ^ 2) := by
    field_simp
  rw [hrw]
  exact mul_le_mul_of_nonneg_left hxinv hcoef

/-- **Band stability, both directions.** On the class of perturbations that only couple frequencies
below `R`, the field discrepancy over the window `[−T,T]` and the operator-norm discrepancy of the
potentials control each other, with explicit constants. -/
theorem lowPass_band_stability (hb0 : 0 ≤ b) (hW₁ : ‖W₁‖ ≤ b) (hW₂ : ‖W₂‖ ≤ b) {R : ℝ}
    (hAdom : ∀ v : Lp ℂ 2 (volume : Measure E),
      (W₁ - W₂) (kgLowPassOp R v) = (W₁ - W₂) v)
    (hAran : ∀ v : Lp ℂ 2 (volume : Measure E),
      kgLowPassOp R ((W₁ - W₂) v) = (W₁ - W₂) v)
    {T : ℝ} (hT0 : 0 < T) :
    (∀ (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
        ‖kgFieldMild W₁ f h t - kgFieldMild W₂ f h t‖
          ≤ ‖W₁ - W₂‖ * ((‖f‖ + ‖h‖) * T) * Real.exp (2 * (b * T)))
      ∧ ∀ η : ℝ, 0 ≤ η →
          (∀ (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
            ‖kgFieldMild W₁ f h t - kgFieldMild W₂ f h t‖ ≤ η * (‖f‖ + ‖h‖)) →
          ‖W₁ - W₂‖ ≤ 8 * (η * (1 + b * T))
            * (1 / T ^ 2 + 8 * ((1 + R ^ 2) / 2 + b * Real.exp (b * T))) := by
  refine ⟨fun f h t htT => ?_, fun η hη0 hobs =>
    norm_sub_le_of_lowPass_explicit hb0 hW₁ hW₂ hAdom hAran hη0 hT0 hobs⟩
  refine (norm_kgFieldMild_sub_potential_le hb0 hW₁ hW₂ (norm_nonneg _) le_rfl f h t).trans ?_
  have hD0 : (0 : ℝ) ≤ ‖f‖ + ‖h‖ := by positivity
  have hA0 : (0 : ℝ) ≤ ‖W₁ - W₂‖ := norm_nonneg _
  have h1 : (‖f‖ + ‖h‖) * |t| ≤ (‖f‖ + ‖h‖) * T := mul_le_mul_of_nonneg_left htT hD0
  have h2 : Real.exp (2 * (b * |t|)) ≤ Real.exp (2 * (b * T)) := by
    refine Real.exp_le_exp.mpr ?_
    have : b * |t| ≤ b * T := mul_le_mul_of_nonneg_left htT hb0
    linarith
  have h3 : ‖W₁ - W₂‖ * ((‖f‖ + ‖h‖) * |t|) ≤ ‖W₁ - W₂‖ * ((‖f‖ + ‖h‖) * T) :=
    mul_le_mul_of_nonneg_left h1 hA0
  have h4 : (0 : ℝ) ≤ ‖W₁ - W₂‖ * ((‖f‖ + ‖h‖) * |t|) := by positivity
  calc ‖W₁ - W₂‖ * ((‖f‖ + ‖h‖) * |t|) * Real.exp (2 * (b * |t|))
      ≤ ‖W₁ - W₂‖ * ((‖f‖ + ‖h‖) * |t|) * Real.exp (2 * (b * T)) :=
        mul_le_mul_of_nonneg_left h2 h4
    _ ≤ ‖W₁ - W₂‖ * ((‖f‖ + ‖h‖) * T) * Real.exp (2 * (b * T)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)

end Band

end GaloisForLFunctions.HTGeometry
