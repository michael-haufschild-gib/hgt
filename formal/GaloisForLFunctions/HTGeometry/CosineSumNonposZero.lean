import Mathlib

/-!
# A finite cosine sum with distinct positive frequencies that is nonpositive everywhere vanishes

For `F(t) = ∑_{i ∈ s} c i · cos(a i · t)` with pairwise distinct positive frequencies `a i`, the
Cesàro means `(1/T) ∫_0^T F(t)(1 ± cos(a j t)) dt` tend to `± c j / 2`.  If `F ≤ 0` everywhere, both
limits are `≤ 0`, so every coefficient vanishes.  This is the uniqueness of Fourier–Bohr
coefficients in the only case needed: finitely many frequencies and a sign condition.
-/

open Filter Topology intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-- `∫_0^T cos(c t) dt = sin(c T)/c` for `c ≠ 0`. -/
theorem integral_cos_mul_eq {c : ℝ} (hc : c ≠ 0) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, Real.cos (c * t) = Real.sin (c * T) / c := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc]
  simp [integral_cos]
  ring

theorem abs_integral_cos_mul_le {c : ℝ} (hc : c ≠ 0) (T : ℝ) :
    |∫ t in (0 : ℝ)..T, Real.cos (c * t)| ≤ 1 / |c| := by
  rw [integral_cos_mul_eq hc, abs_div]
  gcongr
  exact Real.abs_sin_le_one _

/-- The Cesàro mean of `cos(c t)` tends to `0` for `c ≠ 0`. -/
theorem tendsto_integral_cos_mul_div {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, Real.cos (c * t)) / T) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => (1 / |c|) / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hT]
  gcongr
  exact abs_integral_cos_mul_le hc T

theorem intervalIntegrable_cos_mul (c T : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.cos (c * t)) MeasureTheory.volume 0 T :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

/-- Product-to-sum for the integral of `cos(a t) cos(b t)`. -/
theorem integral_cos_mul_cos_mul (a b T : ℝ) :
    ∫ t in (0 : ℝ)..T, Real.cos (a * t) * Real.cos (b * t) =
      ((∫ t in (0 : ℝ)..T, Real.cos ((a - b) * t)) +
        ∫ t in (0 : ℝ)..T, Real.cos ((a + b) * t)) / 2 := by
  have hpt : ∀ t : ℝ, Real.cos (a * t) * Real.cos (b * t) =
      (Real.cos ((a - b) * t) + Real.cos ((a + b) * t)) / 2 := by
    intro t
    have := Real.two_mul_cos_mul_cos (a * t) (b * t)
    rw [show a * t - b * t = (a - b) * t by ring, show a * t + b * t = (a + b) * t by ring] at this
    linarith
  simp_rw [hpt]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (intervalIntegrable_cos_mul _ _)
    (intervalIntegrable_cos_mul _ _)]

/-- Distinct positive frequencies: the Cesàro mean of the product tends to `0`. -/
theorem tendsto_integral_cos_mul_cos_div_of_ne {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, Real.cos (a * t) * Real.cos (b * t)) / T) atTop
      (𝓝 0) := by
  have h1 := tendsto_integral_cos_mul_div (c := a - b) (sub_ne_zero.mpr hab)
  have h2 := tendsto_integral_cos_mul_div (c := a + b) (add_pos ha hb).ne'
  have h := (h1.add h2).div_const 2
  rw [add_zero, zero_div] at h
  refine Tendsto.congr' ?_ h
  filter_upwards with T
  rw [integral_cos_mul_cos_mul]
  ring

/-- Equal positive frequencies: the Cesàro mean of `cos²(a t)` tends to `1/2`. -/
theorem tendsto_integral_cos_sq_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, Real.cos (a * t) * Real.cos (a * t)) / T) atTop
      (𝓝 (1 / 2)) := by
  have h2 := tendsto_integral_cos_mul_div (c := a + a) (add_pos ha ha).ne'
  have hlim : Tendsto (fun T : ℝ =>
      (1 + (∫ t in (0 : ℝ)..T, Real.cos ((a + a) * t)) / T) / 2) atTop (𝓝 ((1 + 0) / 2)) :=
    (tendsto_const_nhds.add h2).div_const 2
  rw [show (1 + 0 : ℝ) / 2 = 1 / 2 by norm_num] at hlim
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [integral_cos_mul_cos_mul, sub_self]
  simp only [zero_mul, Real.cos_zero, intervalIntegral.integral_const, smul_eq_mul, sub_zero,
    mul_one]
  field_simp

/-- The Cesàro mean of `F(t) cos(a j t)` for the cosine sum `F` tends to `c j / 2`. -/
theorem tendsto_cosineSum_mul_cos_div {ι : Type*} [DecidableEq ι] (s : Finset ι) (c a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hinj : Set.InjOn a s) {j : ι} (hj : j ∈ s) :
    Tendsto (fun T : ℝ =>
      (∫ t in (0 : ℝ)..T, (∑ i ∈ s, c i * Real.cos (a i * t)) * Real.cos (a j * t)) / T) atTop
      (𝓝 (c j / 2)) := by
  have hint : ∀ T : ℝ,
      ∫ t in (0 : ℝ)..T, (∑ i ∈ s, c i * Real.cos (a i * t)) * Real.cos (a j * t) =
        ∑ i ∈ s, c i * ∫ t in (0 : ℝ)..T, Real.cos (a i * t) * Real.cos (a j * t) := by
    intro T
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [intervalIntegral.integral_finsetSum
      (f := fun i t => c i * (Real.cos (a i * t) * Real.cos (a j * t))) fun i _ =>
      ((intervalIntegrable_cos_mul (a i) T).mul_continuousOn
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).const_mul
        (c i)]
    exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
  have hlim : Tendsto (fun T : ℝ => ∑ i ∈ s, c i *
      ((∫ t in (0 : ℝ)..T, Real.cos (a i * t) * Real.cos (a j * t)) / T)) atTop
      (𝓝 (∑ i ∈ s, c i * (if i = j then 1 / 2 else 0))) := by
    refine tendsto_finsetSum s fun i hi => ?_
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      exact (tendsto_integral_cos_sq_div (ha i hi)).const_mul _
    · simp only [hij, if_false, mul_zero]
      simpa using (tendsto_integral_cos_mul_cos_div_of_ne (ha i hi) (ha j hj)
        (fun h => hij (hinj hi hj h))).const_mul (c i)
  have hsum : ∑ i ∈ s, c i * (if i = j then (1 : ℝ) / 2 else 0) = c j / 2 := by
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' s j (fun i => c i * (1 / 2)), if_pos hj]
    ring
  rw [hsum] at hlim
  refine Tendsto.congr' ?_ hlim
  filter_upwards with T
  rw [hint, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The Cesàro mean of the cosine sum itself tends to `0`. -/
theorem tendsto_cosineSum_div {ι : Type*} (s : Finset ι) (c a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ∑ i ∈ s, c i * Real.cos (a i * t)) / T) atTop
      (𝓝 0) := by
  have hint : ∀ T : ℝ, ∫ t in (0 : ℝ)..T, ∑ i ∈ s, c i * Real.cos (a i * t) =
      ∑ i ∈ s, c i * ∫ t in (0 : ℝ)..T, Real.cos (a i * t) := by
    intro T
    rw [intervalIntegral.integral_finsetSum (f := fun i t => c i * Real.cos (a i * t))
      fun i _ => (intervalIntegrable_cos_mul (a i) T).const_mul (c i)]
    exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
  have hlim : Tendsto (fun T : ℝ => ∑ i ∈ s, c i *
      ((∫ t in (0 : ℝ)..T, Real.cos (a i * t)) / T)) atTop (𝓝 (∑ i ∈ s, c i * 0)) :=
    tendsto_finsetSum s fun i hi => (tendsto_integral_cos_mul_div (ha i hi).ne').const_mul _
  simp only [mul_zero, Finset.sum_const_zero] at hlim
  refine Tendsto.congr' ?_ hlim
  filter_upwards with T
  rw [hint, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Cesàro bounds for the coefficients of a finite cosine sum bounded above by `ε`.** -/
theorem cosineSum_coeff_le_of_le {ι : Type*} (s : Finset ι) (c a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hinj : Set.InjOn a s) {ε : ℝ}
    (hF : ∀ t : ℝ, ∑ i ∈ s, c i * Real.cos (a i * t) ≤ ε) :
    ∀ j ∈ s, c j / 2 ≤ ε ∧ -(c j / 2) ≤ ε := by
  classical
  intro j hj
  set F : ℝ → ℝ := fun t => ∑ i ∈ s, c i * Real.cos (a i * t) with hFdef
  have hFcont : Continuous F :=
    continuous_finsetSum s fun i _ =>
      continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hFi : ∀ T : ℝ, IntervalIntegrable F MeasureTheory.volume 0 T :=
    fun T => hFcont.intervalIntegrable _ _
  have hFci : ∀ T : ℝ, IntervalIntegrable (fun t => F t * Real.cos (a j * t))
      MeasureTheory.volume 0 T :=
    fun T => (hFcont.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
      |>.intervalIntegrable _ _
  have hlimF := tendsto_cosineSum_div s c a ha
  have hlimC := tendsto_cosineSum_mul_cos_div s c a ha hinj hj
  have hlimcos := tendsto_integral_cos_mul_div (ha j hj).ne'
  have hRHS : ∀ T : ℝ, ∀ sgn : ℝ, ε * (T + sgn * ∫ t in (0 : ℝ)..T, Real.cos (a j * t)) =
      ∫ t in (0 : ℝ)..T, (ε + ε * sgn * Real.cos (a j * t)) := by
    intro T sgn
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((intervalIntegrable_cos_mul _ _).const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hplus_int : ∀ T : ℝ, 0 < T →
      (∫ t in (0 : ℝ)..T, F t) + ∫ t in (0 : ℝ)..T, F t * Real.cos (a j * t) ≤
        ε * (T + 1 * ∫ t in (0 : ℝ)..T, Real.cos (a j * t)) := by
    intro T hT
    rw [← intervalIntegral.integral_add (hFi T) (hFci T), hRHS]
    refine intervalIntegral.integral_mono_on hT.le ((hFi T).add (hFci T))
      (intervalIntegrable_const.add ((intervalIntegrable_cos_mul _ _).const_mul _)) fun t _ => ?_
    have h1 := hF t
    have h2 := Real.neg_one_le_cos (a j * t)
    nlinarith
  have hminus_int : ∀ T : ℝ, 0 < T →
      (∫ t in (0 : ℝ)..T, F t) - ∫ t in (0 : ℝ)..T, F t * Real.cos (a j * t) ≤
        ε * (T + (-1) * ∫ t in (0 : ℝ)..T, Real.cos (a j * t)) := by
    intro T hT
    rw [← intervalIntegral.integral_sub (hFi T) (hFci T), hRHS]
    refine intervalIntegral.integral_mono_on hT.le ((hFi T).sub (hFci T))
      (intervalIntegrable_const.add ((intervalIntegrable_cos_mul _ _).const_mul _)) fun t _ => ?_
    have h1 := hF t
    have h3 := Real.cos_le_one (a j * t)
    nlinarith
  have hev_plus : ∀ᶠ T in atTop, (∫ t in (0 : ℝ)..T, F t) / T +
      (∫ t in (0 : ℝ)..T, F t * Real.cos (a j * t)) / T ≤
        ε * (1 + (∫ t in (0 : ℝ)..T, Real.cos (a j * t)) / T) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hT' : T ≠ 0 := hT.ne'
    have h := hplus_int T hT
    rw [← add_div, div_le_iff₀ hT]
    have e : ε * (1 + (∫ t in (0 : ℝ)..T, Real.cos (a j * t)) / T) * T =
        ε * (T + 1 * ∫ t in (0 : ℝ)..T, Real.cos (a j * t)) := by
      field_simp
    rw [e]
    exact h
  have hev_minus : ∀ᶠ T in atTop, (∫ t in (0 : ℝ)..T, F t) / T -
      (∫ t in (0 : ℝ)..T, F t * Real.cos (a j * t)) / T ≤
        ε * (1 - (∫ t in (0 : ℝ)..T, Real.cos (a j * t)) / T) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hT' : T ≠ 0 := hT.ne'
    have h := hminus_int T hT
    rw [← sub_div, div_le_iff₀ hT]
    have e : ε * (1 - (∫ t in (0 : ℝ)..T, Real.cos (a j * t)) / T) * T =
        ε * (T + (-1) * ∫ t in (0 : ℝ)..T, Real.cos (a j * t)) := by
      field_simp
      ring
    rw [e]
    exact h
  refine ⟨?_, ?_⟩
  · have hplus := hlimF.add hlimC
    rw [zero_add] at hplus
    have hlim : Tendsto (fun T : ℝ => ε * (1 + (∫ t in (0 : ℝ)..T, Real.cos (a j * t)) / T))
        atTop (𝓝 ε) := by
      have := (hlimcos.const_add 1).const_mul ε
      rw [add_zero, mul_one] at this
      exact this
    exact le_of_tendsto_of_tendsto hplus hlim hev_plus
  · have hminus := hlimF.sub hlimC
    rw [zero_sub] at hminus
    have hlim : Tendsto (fun T : ℝ => ε * (1 - (∫ t in (0 : ℝ)..T, Real.cos (a j * t)) / T))
        atTop (𝓝 ε) := by
      have := (hlimcos.const_sub 1).const_mul ε
      rw [sub_zero, mul_one] at this
      exact this
    exact le_of_tendsto_of_tendsto hminus hlim hev_minus

/-- **A nonpositive finite cosine sum with distinct positive frequencies has zero coefficients.** -/
theorem cosineSum_coeff_eq_zero_of_nonpos {ι : Type*} (s : Finset ι) (c a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hinj : Set.InjOn a s)
    (hF : ∀ t : ℝ, ∑ i ∈ s, c i * Real.cos (a i * t) ≤ 0) : ∀ j ∈ s, c j = 0 := by
  intro j hj
  obtain ⟨h1, h2⟩ := cosineSum_coeff_le_of_le s c a ha hinj hF j hj
  linarith

end GaloisForLFunctions.HTGeometry
