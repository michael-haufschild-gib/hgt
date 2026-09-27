import GaloisForLFunctions.RHTower.XiGaussianFourthTraceEnvelope

/-!
# Complete phase debt bounded by the unspent arithmetic source

The coefficient-independent ceiling uses an explicit factorial envelope and
the fourth-trace source after exact subtraction of finite critical copies.
It applies to every positive heat time and every finite polynomial order.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

def xiGaussianResidualPhaseBudget (F : Finset XiZeroCopy) (N : ℕ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : ℝ :=
  (42 / 41 : ℝ) * xiCriticalFourthTraceResidual F *
    Real.exp (-((t - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
      xiGaussianFourthTraceEnvelope N s

theorem xiGaussianResidualPhaseBudget_nonneg (F : Finset XiZeroCopy) (N : ℕ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : 0 ≤ xiGaussianResidualPhaseBudget F N s t := by
  unfold xiGaussianResidualPhaseBudget
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by positivity) (xiCriticalFourthTraceResidual_nonneg F))
      (Real.exp_pos _).le) (xiGaussianFourthTraceEnvelope_nonneg N s)

/-- Complete polynomial phase at each copy is charged against its off-critical source atom. -/
theorem xiGaussianImaginaryAtom_le_residual_source_weight
    (F : Finset XiZeroCopy) (N : ℕ) (a : ℕ → ℝ)
    (s : {s : ℝ // 0 < s}) (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)})
    (q : XiZeroCopy) :
    xiGaussianImaginaryChannelAtom
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 q ≤
        ((42 / 41 : ℝ) *
          Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
            xiGaussianFourthTraceEnvelope N s * (∑ j ∈ Finset.range N, a j ^ 2)) *
              xiFourthTraceOffAtom q := by
  by_cases hreal : (xiSpectralPoint q).im = 0
  · rw [xiGaussianImaginaryChannelAtom_of_real _ t.1 ⟨q, hreal⟩,
      xiFourthTraceOffAtom, if_pos hreal, mul_zero]
  · let Q := ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j
    let C := Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
      xiGaussianFourthTraceEnvelope N s * (∑ j ∈ Finset.range N, a j ^ 2)
    have hC : 0 ≤ C := mul_nonneg
      (mul_nonneg (Real.exp_pos _).le (xiGaussianFourthTraceEnvelope_nonneg N s))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hnorm : 0 < ‖xiSpectralPoint q‖ ^ 4 :=
      pow_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)) _
    have hbound := xiGaussianPolynomial_mul_norm_four_le_residual_envelope F N a s t ⟨q, hreal⟩
    change ‖xiPolynomialGaussianHeatTerm Q t.1 q‖ * ‖xiSpectralPoint q‖ ^ 4 ≤ C at hbound
    have hdiv : ‖xiPolynomialGaussianHeatTerm Q t.1 q‖ ≤ C * (1 / ‖xiSpectralPoint q‖ ^ 4) := by
      rw [← div_eq_mul_one_div]
      exact (le_div_iff₀ hnorm).mpr hbound
    have hweight : (1 / ‖xiSpectralPoint q‖ ^ 4) ≤
        (42 / 41 : ℝ) * (xiZeroCopyReciprocalSquare q ^ 2).re := by
      have h := xiFourthTraceAtom_ge_reciprocal_norm_four q
      linarith only [h]
    calc
      _ ≤ ‖xiPolynomialGaussianHeatTerm Q t.1 q‖ := xiGaussianImaginaryChannelAtom_le_norm Q t.1 q
      _ ≤ C * (1 / ‖xiSpectralPoint q‖ ^ 4) := hdiv
      _ ≤ C * ((42 / 41 : ℝ) * (xiZeroCopyReciprocalSquare q ^ 2).re) :=
        mul_le_mul_of_nonneg_left hweight hC
      _ = _ := by rw [xiFourthTraceOffAtom, if_neg hreal]; dsimp only [C]; ring

/-- The entire actual imaginary channel is bounded by the unspent source, with explicit
constants and no unknown spectral anchor. -/
theorem xiGaussianImaginaryChannel_le_residual_source
    (F : Finset XiZeroCopy) (N : ℕ) (a : ℕ → ℝ)
    (s : {s : ℝ // 0 < s}) (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 q) ≤
        xiGaussianResidualPhaseBudget F N s t.1 * (∑ j ∈ Finset.range N, a j ^ 2) := by
  let C := (42 / 41 : ℝ) *
    Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
      xiGaussianFourthTraceEnvelope N s * (∑ j ∈ Finset.range N, a j ^ 2)
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
      (xiGaussianFourthTraceEnvelope_nonneg N s))
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have h := Summable.tsum_le_tsum (xiGaussianImaginaryAtom_le_residual_source_weight F N a s t)
    (summable_xiGaussianImaginaryChannelAtom _ t.1) (summable_xiFourthTraceOffAtom.mul_left C)
  rw [tsum_mul_left] at h
  calc
    _ ≤ C * ∑' q : XiZeroCopy, xiFourthTraceOffAtom q := h
    _ ≤ C * xiCriticalFourthTraceResidual F :=
      mul_le_mul_of_nonneg_left (tsum_xiFourthTraceOffAtom_le_residual F) hC
    _ = _ := by unfold C xiGaussianResidualPhaseBudget; ring

/-- Half-time anchoring covers the entire required positive heat-time range. -/
theorem xiGaussianImaginaryChannel_le_residual_source_allTime
    (F : Finset XiZeroCopy) (N : ℕ) (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t q) ≤
        xiGaussianResidualPhaseBudget F N (xiGaussianHalfHeat t) t *
          (∑ j ∈ Finset.range N, a j ^ 2) :=
  xiGaussianImaginaryChannel_le_residual_source F N a (xiGaussianHalfHeat t)
    ⟨t, by change (t : ℝ) / 2 ≤ (t : ℝ); linarith only [t.property]⟩

/-- The full finite Hankel family retains its complete real reserve and all cross terms. -/
theorem xiHeatHankelForm_ge_realChannel_sub_residualSource
    (F : Finset XiZeroCopy) (N : ℕ) (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}) :
    xiGaussianRealChannelEnergy
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t -
        xiGaussianResidualPhaseBudget F N (xiGaussianHalfHeat t) t *
          (∑ j ∈ Finset.range N, a j ^ 2) ≤ xiHeatHankelForm N a t := by
  have h := xiGaussianImaginaryChannel_le_residual_source_allTime F N a t
  have he := xiGaussianTrace_eq_realChannel_sub_imaginary
    (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t
  rw [xiPolynomialGaussianHeatTraceReal_rangeSum t.property] at he
  linarith only [h, he]

/-- Independent actual critical nodes bound the full form after the source-controlled debt. -/
theorem exists_xiHeatHankelForm_allTime_residualSource_lower (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 32 < L ∧
      ∀ (F : Finset XiZeroCopy) (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}),
        (c * Real.exp (-(L * (t : ℝ))) -
          xiGaussianResidualPhaseBudget F N (xiGaussianHalfHeat t) t) *
            (∑ j ∈ Finset.range N, a j ^ 2) ≤ xiHeatHankelForm N a t := by
  obtain ⟨c, hc, L, hL, hfloor⟩ := exists_xiGaussianRealChannel_allTime_floor N
  refine ⟨c, hc, L, hL, ?_⟩
  intro F a t
  have hf := hfloor a t
  have hb := xiHeatHankelForm_ge_realChannel_sub_residualSource F N a t
  nlinarith only [hf, hb]

/-- Complete three-by-three specialization at every positive time. -/
theorem exists_xiHeatThirdQuadratic_allTime_residualSource_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ L : ℝ, 32 < L ∧
      ∀ (F : Finset XiZeroCopy) (a b c : ℝ) (t : {t : ℝ // 0 < t}),
        (c₀ * Real.exp (-(L * (t : ℝ))) -
          xiGaussianResidualPhaseBudget F 3 (xiGaussianHalfHeat t) t) *
            (a ^ 2 + b ^ 2 + c ^ 2) ≤ xiHeatThirdQuadratic a b c t := by
  obtain ⟨c₀, hc₀, L, hL, hbound⟩ := exists_xiHeatHankelForm_allTime_residualSource_lower 3
  refine ⟨c₀, hc₀, L, hL, ?_⟩
  intro F a b c t
  rw [xiHeatThirdQuadratic_eq_hankel]
  simpa [Finset.sum_range_succ] using
    hbound F (fun n => if n = 0 then a else if n = 1 then b else c) t

end RHTower
