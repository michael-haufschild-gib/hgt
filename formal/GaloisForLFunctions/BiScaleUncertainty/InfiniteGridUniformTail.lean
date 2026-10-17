import GaloisForLFunctions.BiScaleUncertainty.LogarithmicIncrementEnergy

/-!
# Uniform logarithmic continuity and infinite-grid tails

The singular Lévy energy controls correlation increments at every location. At logarithmic
grid zeros this yields a uniform inverse-square-root tail bound for arbitrary compact C²
sources, with no support, derivative, or packet-shape parameter. The same bound gives
decaying window integrals. These are unweighted estimates, not hyperbolic moment estimates.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-- A global logarithmic modulus controlled only by source mass and Lévy energy. -/
theorem autocorr_difference_sq_mul_log_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {x y : ℝ}
    (hd : 0 < |x - y|) (hd1 : |x - y| ≤ 1) :
    Real.exp (-(1 / 2 : ℝ)) * (-Real.log |x - y|) *
      (autocorr f x - autocorr f y) ^ 2 ≤ 8 * autocorr f 0 * biScaleLevyEnergy f := by
  have heven : autocorr f (x - y) = autocorr f |x - y| := by
    by_cases h : 0 ≤ x - y
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), autocorr_neg]
  have hk := autocorr_krein_increment_sq_le hfc hf.continuous x y
  rw [heven] at hk
  have hw : 0 ≤ Real.exp (-(1 / 2 : ℝ)) * (-Real.log |x - y|) :=
    mul_nonneg (Real.exp_pos _).le (neg_nonneg.mpr (Real.log_nonpos hd.le hd1))
  calc
    _ ≤ Real.exp (-(1 / 2 : ℝ)) * (-Real.log |x - y|) *
        (2 * autocorr f 0 * (autocorr f 0 - autocorr f |x - y|)) :=
      mul_le_mul_of_nonneg_left hk hw
    _ = (2 * autocorr f 0) * (Real.exp (-(1 / 2 : ℝ)) *
        (autocorr f 0 - autocorr f |x - y|) * (-Real.log |x - y|)) := by ring
    _ ≤ (2 * autocorr f 0) * (4 * biScaleLevyEnergy f) :=
      mul_le_mul_of_nonneg_left (autocorr_increment_mul_log_le hf hfc hd hd1)
        (mul_nonneg (by norm_num) (autocorr_zero_nonneg f))
    _ = _ := by ring

private theorem normalize_correlation_sq_bound {f : ℝ → ℝ}
    (hR : 0 < autocorr f 0) {w z : ℝ}
    (h : w * z ^ 2 ≤ 8 * autocorr f 0 * biScaleLevyEnergy f) :
    w * (z / autocorr f 0) ^ 2 ≤ 8 * normalizedArchEnergy f := by
  have hm := div_le_div_of_nonneg_right h (sq_nonneg (autocorr f 0))
  unfold normalizedArchEnergy
  calc
    _ = (w * z ^ 2) / autocorr f 0 ^ 2 := by ring
    _ ≤ (8 * autocorr f 0 * biScaleLevyEnergy f) / autocorr f 0 ^ 2 := hm
    _ = _ := by field_simp

/-- The normalized modulus is uniform over sources of bounded normalized energy. -/
theorem normalized_autocorr_difference_sq_mul_log_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {x y : ℝ} (hd : 0 < |x - y|) (hd1 : |x - y| ≤ 1) :
    Real.exp (-(1 / 2 : ℝ)) * (-Real.log |x - y|) *
      (autocorr f x / autocorr f 0 - autocorr f y / autocorr f 0) ^ 2 ≤
        8 * normalizedArchEnergy f := by
  rw [← sub_div]
  exact normalize_correlation_sq_bound hR (autocorr_difference_sq_mul_log_le hf hfc hd hd1)

/-- Bounded normalized energy gives one continuity radius for every source and every
pair of locations. This assertion needs no grid constraints. -/
theorem exists_uniform_autocorr_continuity_radius {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      0 < autocorr f 0 → normalizedArchEnergy f ≤ K → ∀ x y : ℝ, |x - y| < δ →
      |autocorr f x / autocorr f 0 - autocorr f y / autocorr f 0| < ε := by
  let c := Real.exp (-(1 / 2 : ℝ))
  have hc : 0 < c := Real.exp_pos _
  have hd : 0 < c * ε ^ 2 := mul_pos hc (sq_pos_of_pos hε)
  let q := 1 + 8 * K / (c * ε ^ 2)
  have hq : 0 < q := by
    dsimp [q]
    linarith [div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hK) hd.le]
  refine ⟨Real.exp (-q), Real.exp_pos _, ?_⟩
  intro f hf hfc hR hE x y hxy
  by_cases heq : x = y
  · simpa only [heq, sub_self, abs_zero] using hε
  have hp : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr heq)
  have h1 : |x - y| ≤ 1 :=
    hxy.le.trans (Real.exp_le_one_iff.mpr (by linarith))
  have hl := Real.log_lt_log hp hxy
  rw [Real.log_exp] at hl
  have hb := normalized_autocorr_difference_sq_mul_log_le hf hfc hR hp h1
  change c * (-Real.log |x - y|) *
    (autocorr f x / autocorr f 0 - autocorr f y / autocorr f 0) ^ 2 ≤
      8 * normalizedArchEnergy f at hb
  by_contra hn
  have he : ε ≤ |autocorr f x / autocorr f 0 - autocorr f y / autocorr f 0| :=
    le_of_not_gt hn
  have hs : ε ^ 2 ≤ (autocorr f x / autocorr f 0 - autocorr f y / autocorr f 0) ^ 2 := by
    nlinarith [sq_abs (autocorr f x / autocorr f 0 - autocorr f y / autocorr f 0)]
  have hw : 0 ≤ c * (-Real.log |x - y|) :=
    mul_nonneg hc.le (by linarith)
  have hm := mul_le_mul_of_nonneg_left hs hw
  have hqeq : q * (c * ε ^ 2) = c * ε ^ 2 + 8 * K := by
    dsimp [q]
    field_simp
  have hstrict := mul_lt_mul_of_pos_right (show q < -Real.log |x - y| by linarith) hd
  nlinarith

/-- The error in sampling any source at its next logarithmic node has inverse-linear
squared size in the location, independently of the source's shape. -/
theorem autocorr_logarithmicCeilNode_error_sq_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {T : ℝ} (hT : 0 ≤ T) :
    Real.exp (-(1 / 2 : ℝ)) * T *
      (autocorr f T - autocorr f (Real.log (logarithmicCeilNode T : ℝ))) ^ 2 ≤
        8 * autocorr f 0 * biScaleLevyEnergy f := by
  have hk := autocorr_krein_increment_sq_le hfc hf.continuous
    (Real.log (logarithmicCeilNode T : ℝ)) T
  change (autocorr f (Real.log (logarithmicCeilNode T : ℝ)) - autocorr f T) ^ 2 ≤
    2 * autocorr f 0 * (autocorr f 0 - autocorr f (logarithmicCeilLag T)) at hk
  calc
    _ = Real.exp (-(1 / 2 : ℝ)) * T *
        (autocorr f (Real.log (logarithmicCeilNode T : ℝ)) - autocorr f T) ^ 2 := by ring
    _ ≤ Real.exp (-(1 / 2 : ℝ)) * T *
        (2 * autocorr f 0 * (autocorr f 0 - autocorr f (logarithmicCeilLag T))) :=
      mul_le_mul_of_nonneg_left hk (mul_nonneg (Real.exp_pos _).le hT)
    _ = (2 * autocorr f 0) * (Real.exp (-(1 / 2 : ℝ)) * T *
        (autocorr f 0 - autocorr f (logarithmicCeilLag T))) := by ring
    _ ≤ (2 * autocorr f 0) * (4 * biScaleLevyEnergy f) :=
      mul_le_mul_of_nonneg_left (autocorr_logarithmicCeilLag_energy_bound hf hfc hT)
        (mul_nonneg (by norm_num) (autocorr_zero_nonneg f))
    _ = _ := by ring

/-- All logarithmic-grid zeros force a tail law for every compact C² source. -/
theorem autocorr_sq_mul_location_le_of_infinite_grid {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hzeros : ∀ n : ℕ, 2 ≤ n → autocorr f (Real.log (n : ℝ)) = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    Real.exp (-(1 / 2 : ℝ)) * T * autocorr f T ^ 2 ≤
      8 * autocorr f 0 * biScaleLevyEnergy f := by
  rcases eq_or_lt_of_le hT with hz | hp
  · rw [← hz]
    simp only [mul_zero, zero_mul]
    exact mul_nonneg (mul_nonneg (by norm_num) (autocorr_zero_nonneg f))
      (biScaleLevyEnergy_nonneg hfc hf.continuous)
  · have h := autocorr_logarithmicCeilNode_error_sq_le hf hfc hT
    simpa only [hzeros _ (logarithmicCeilNode_ge_two hp), sub_zero] using h

/-- Two-sided tail control, including zero source mass and the origin. -/
theorem autocorr_sq_mul_abs_location_le_of_infinite_grid {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hzeros : ∀ n : ℕ, 2 ≤ n → autocorr f (Real.log (n : ℝ)) = 0) (T : ℝ) :
    Real.exp (-(1 / 2 : ℝ)) * |T| * autocorr f T ^ 2 ≤
      8 * autocorr f 0 * biScaleLevyEnergy f := by
  have h := autocorr_sq_mul_location_le_of_infinite_grid hf hfc hzeros (abs_nonneg T)
  by_cases hT : 0 ≤ T
  · simpa only [abs_of_nonneg hT] using h
  · simpa only [abs_of_neg (lt_of_not_ge hT), autocorr_neg] using h

/-- Normalized squared correlations decay like energy divided by distance. -/
theorem normalized_autocorr_sq_mul_abs_location_le_of_infinite_grid {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    (hzeros : ∀ n : ℕ, 2 ≤ n → autocorr f (Real.log (n : ℝ)) = 0) (T : ℝ) :
    Real.exp (-(1 / 2 : ℝ)) * |T| * (autocorr f T / autocorr f 0) ^ 2 ≤
      8 * normalizedArchEnergy f :=
  normalize_correlation_sq_bound hR
    (autocorr_sq_mul_abs_location_le_of_infinite_grid hf hfc hzeros T)

/-- One radius works for every source of bounded normalized energy satisfying the full grid. -/
theorem exists_uniform_infinite_grid_tail_radius {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      0 < autocorr f 0 → normalizedArchEnergy f ≤ K →
      (∀ n : ℕ, 2 ≤ n → autocorr f (Real.log (n : ℝ)) = 0) →
      ∀ T : ℝ, A ≤ |T| → |autocorr f T / autocorr f 0| < ε := by
  let c := Real.exp (-(1 / 2 : ℝ))
  have hc : 0 < c := Real.exp_pos _
  have hd : 0 < c * ε ^ 2 := mul_pos hc (sq_pos_of_pos hε)
  let A := 1 + 8 * K / (c * ε ^ 2)
  have hA : 0 < A := by
    dsimp [A]
    linarith [div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hK) hd.le]
  refine ⟨A, hA, ?_⟩
  intro f hf hfc hR hE hzeros T hT
  have hb := normalized_autocorr_sq_mul_abs_location_le_of_infinite_grid hf hfc hR hzeros T
  change c * |T| * (autocorr f T / autocorr f 0) ^ 2 ≤ 8 * normalizedArchEnergy f at hb
  by_contra hn
  have he : ε ≤ |autocorr f T / autocorr f 0| := le_of_not_gt hn
  have hs : ε ^ 2 ≤ (autocorr f T / autocorr f 0) ^ 2 := by
    nlinarith [sq_abs (autocorr f T / autocorr f 0)]
  have h1 := mul_le_mul_of_nonneg_left hs (mul_nonneg hc.le (abs_nonneg T))
  have h2 := mul_le_mul_of_nonneg_right hT hd.le
  have hAeq : A * (c * ε ^ 2) = c * ε ^ 2 + 8 * K := by
    dsimp [A]
    field_simp
  nlinarith

/-- Integrating the tail law gives a window bound with inverse-linear dependence on its
left endpoint and no derivative-dependent constant. -/
theorem integral_autocorr_sq_window_mul_left_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hzeros : ∀ n : ℕ, 2 ≤ n → autocorr f (Real.log (n : ℝ)) = 0)
    {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    Real.exp (-(1 / 2 : ℝ)) * A * (∫ x in A..B, autocorr f x ^ 2) ≤
      8 * (B - A) * autocorr f 0 * biScaleLevyEnergy f := by
  have hi : IntervalIntegrable
      (fun x => Real.exp (-(1 / 2 : ℝ)) * A * autocorr f x ^ 2) volume A B :=
    ((continuous_autocorr hf hfc).pow 2).intervalIntegrable A B |>.const_mul _
  have hj : IntervalIntegrable
      (fun _ : ℝ => 8 * autocorr f 0 * biScaleLevyEnergy f) volume A B := intervalIntegrable_const
  have hm := intervalIntegral.integral_mono_on hAB hi hj fun x hx => by
    have hb := autocorr_sq_mul_location_le_of_infinite_grid hf hfc hzeros
      (le_trans hA.le hx.1)
    have hs := mul_le_mul_of_nonneg_right hx.1
      (mul_nonneg (Real.exp_pos (-(1 / 2 : ℝ))).le (sq_nonneg (autocorr f x)))
    nlinarith
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hm
  nlinarith

/-- On logarithmic dyadic windows the squared-correlation integral decays as `1 / log N`. -/
theorem integral_autocorr_sq_dyadic_mul_log_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hzeros : ∀ n : ℕ, 2 ≤ n → autocorr f (Real.log (n : ℝ)) = 0)
    {N : ℕ} (hN : 2 ≤ N) :
    Real.exp (-(1 / 2 : ℝ)) * Real.log (N : ℝ) *
      (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), autocorr f x ^ 2) ≤
        8 * Real.log 2 * autocorr f 0 * biScaleLevyEnergy f := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog : Real.log ((2 * N : ℕ) : ℝ) = Real.log 2 + Real.log (N : ℝ) := by
    push_cast
    exact Real.log_mul (by norm_num) hNp.ne'
  have hAB : Real.log (N : ℝ) ≤ Real.log ((2 * N : ℕ) : ℝ) := by
    rw [hlog]
    linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]
  have h := integral_autocorr_sq_window_mul_left_le hf hfc hzeros (Real.log_pos hN1) hAB
  simpa only [hlog, add_sub_cancel_right] using h

end

end GaloisForLFunctions.BiScaleUncertainty
