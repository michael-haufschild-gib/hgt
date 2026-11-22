import GaloisForLFunctions.RHTower.Sieve.GallagherRange
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGramDominationRepair

/-! Compare the physical-height mean square with logarithmic windows of length one over the height. -/

open Complex MeasureTheory FourierTransform Finset RHTower.Sieve

namespace QH.PrimeProgressions

private theorem tri_fourier_lower {δ w : ℝ} (hδ : 0 < δ)
    (hw : |2 * Real.pi * w| * δ ≤ 1) : δ ^ 2 / 2 ≤ (𝓕 (triC δ) w).re := by
  let L := -(2 * Real.pi * w)
  let f (t : ℝ) : ℂ := (tri δ t : ℂ) * exp (((t * L : ℝ) : ℂ) * I)
  have hcompact : HasCompactSupport f := by
    refine HasCompactSupport.intro (K := Set.Icc (-δ) δ) isCompact_Icc fun t ht => ?_
    have h : δ ≤ |t| := le_of_lt (lt_of_not_ge (fun hb => ht (abs_le.mp hb)))
    simp only [f, tri_eq_zero h, ofReal_zero, zero_mul]
  have hf : Integrable f := (continuous_triPhase δ L).integrable_of_hasCompactSupport hcompact
  have htri : Integrable (tri δ) := by
    have h := (integrable_triC hδ.le).re
    change Integrable (fun t => ((tri δ t : ℝ) : ℂ).re) at h
    simpa only [ofReal_re] using h
  have hmass : (∫ t, tri δ t) = δ ^ 2 := by
    have h := congrArg Complex.re (integral_tri_phase hδ (0 : ℝ))
    simp only [mul_zero, ofReal_zero, zero_mul, exp_zero, mul_one,
      fejerWeightAt_zero hδ] at h
    change (∫ t, triC δ t).re = _ at h
    simpa only [triC, integral_complex_ofReal, ← ofReal_mul, ofReal_re, pow_two] using h
  have hpoint (t : ℝ) : (1 / 2 : ℝ) * tri δ t ≤ (f t).re := by
    change (1 / 2 : ℝ) * tri δ t ≤
      (((tri δ t : ℝ) : ℂ) * exp (((t * L : ℝ) : ℂ) * I)).re
    rw [re_ofReal_mul, exp_ofReal_mul_I_re]
    by_cases ht : |t| ≤ δ
    · have htL : |t * L| ≤ 1 := by
        rw [abs_mul, show |L| = |2 * Real.pi * w| by simp only [L, abs_neg], mul_comm]
        exact (mul_le_mul_of_nonneg_left ht (abs_nonneg _)).trans hw
      have hsq : (t * L) ^ 2 ≤ 1 := by
        rw [← sq_abs]
        exact (pow_le_pow_left₀ (abs_nonneg _) htL 2).trans_eq (one_pow _)
      have hc : (1 / 2 : ℝ) ≤ Real.cos (t * L) := by
        linarith only [Real.one_sub_sq_div_two_le_cos (x := t * L), hsq]
      simpa only [mul_comm (1 / 2 : ℝ)] using
        (mul_le_mul_of_nonneg_left hc (tri_nonneg δ t))
    · rw [tri_eq_zero (le_of_lt (lt_of_not_ge ht)), mul_zero, zero_mul]
  have h := integral_mono (htri.const_mul (1 / 2)) hf.re hpoint
  rw [integral_const_mul, hmass, integral_re hf] at h
  rw [fourier_triC hδ, ← integral_tri_phase hδ L]
  exact (show δ ^ 2 / 2 = (1 / 2 : ℝ) * δ ^ 2 by ring).le.trans h

/-- Gallagher's comparison in the physical-height variable, with the position integral
left in logarithmic coordinates. -/
theorem prime_gallagher_mean (a : ℕ → ℂ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) {T : ℝ} (hT : 0 < T) :
    (∫ t in (-T)..T, ‖∑ n ∈ S, a n * (n : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      4 * Real.pi * T ^ 2 * ∫ u : ℝ, ‖logWindowSum a S (1 / T) u‖ ^ 2 := by
  let δ : ℝ := 1 / T
  let W : ℝ := T / (2 * Real.pi)
  let G (w : ℝ) := ‖logPoly a S w‖ ^ 2
  let K (w : ℝ) := (𝓕 (triC δ) w).re * G w
  have hδ : 0 < δ := one_div_pos.mpr hT
  have hπ : 0 < 2 * Real.pi := by positivity
  have hW : 0 < W := div_pos hT hπ
  have hWW : -W ≤ W := by linarith only [hW]
  have hG : Continuous G := (continuous_logPoly a S).norm.pow 2
  have hK : Continuous K := (Complex.continuous_re.comp (continuous_fourier_triC hδ.le)).mul hG
  have hlower (w : ℝ) (hw : w ∈ Set.Icc (-W) W) : δ ^ 2 / 2 * G w ≤ K w := by
    have habs : |w| ≤ W := abs_le.mpr hw
    have hphase : |2 * Real.pi * w| * δ ≤ 1 := by
      rw [abs_mul, abs_of_pos hπ]
      refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs hπ.le) hδ.le).trans_eq ?_
      dsimp only [δ, W]
      field_simp
    exact mul_le_mul_of_nonneg_right (tri_fourier_lower hδ hphase) (sq_nonneg _)
  have hcompare := intervalIntegral.integral_mono_on hWW
    ((hG.const_mul (δ ^ 2 / 2)).intervalIntegrable (μ := volume) (-W) W)
    (hK.intervalIntegrable (μ := volume) (-W) W) hlower
  rw [intervalIntegral.integral_const_mul] at hcompare
  have hwhole : (∫ w in (-W)..W, K w) ≤ ∫ w, K w := by
    rw [intervalIntegral.integral_of_le hWW]
    exact setIntegral_le_integral (integrable_gallagher_weight_mul hδ a S)
      (Filter.Eventually.of_forall fun w => mul_nonneg (fourier_triC_re_nonneg hδ w) (sq_nonneg _))
  have hpiece := mul_le_mul_of_nonneg_left (hcompare.trans hwhole)
    (show 0 ≤ 2 * T ^ 2 by positivity)
  have hscale : 2 * T ^ 2 * (δ ^ 2 / 2) = 1 := by
    dsimp only [δ]
    field_simp
  rw [← mul_assoc, hscale, one_mul] at hpiece
  have heq (t : ℝ) :
      (∑ n ∈ S, a n * (n : ℂ) ^ (-(t * I))) = logPoly a S (-t / (2 * Real.pi)) := by
    unfold logPoly
    refine sum_congr rfl fun n hn => ?_
    have hn₀ : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hS n hn))
    rw [cpow_def_of_ne_zero hn₀, ← Complex.natCast_log]
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero]
    <;> ring
  simp_rw [heq]
  change (∫ t in (-T)..T, G (-t / (2 * Real.pi))) ≤ _
  rw [RHTower.intervalIntegral_comp_neg_div_two_pi, gallagher_identity a S hδ]
  exact (mul_le_mul_of_nonneg_left hpiece hπ.le).trans_eq (by ring)

end QH.PrimeProgressions
