/-
# The torus upper law for the logarithmic mean of a Dirichlet polynomial

For a Dirichlet polynomial `F(t) = ∑_{n∈s} a_n n^{-it}` with real coefficients, the even-moment
Bohr tower (`tendsto_evenMoment_average_steinhaus`) identifies every `‖F‖^{2k}` time average with
the Steinhaus-model moment. Weierstrass approximation lifts this to every continuous function of
`‖F‖²` (`tendsto_contMoment_average_steinhaus`), on Cesàro averages and on dyadic windows.
Applied to the continuous majorant `½ log max(‖F‖², ε²)` of `log ‖F‖` (an inequality off the
finitely many zeros of `F` on the window), this gives the **torus upper law**

  `limsup_T (1/T)∫_T^{2T} log ‖F(t)‖ dt ≤ ½ E_χ log max(‖∑ a_n χ(n)‖², ε²)`   for every `ε > 0`,

the one-sided Bohr–Jessen–Tornehave law that the outer-law bookkeeping for `ζΨ` needs.
-/
import GaloisForLFunctions.RHTower.BohrMomentDensity
import GaloisForLFunctions.RHTower.EntireDirichletPolynomial
import GaloisForLFunctions.RHTower.LevinsonLittlewoodZeroCount
import GaloisForLFunctions.RHTower.EntireWeightedLittlewoodRectangle
import Mathlib.Topology.ContinuousMap.Weierstrass

open MeasureTheory intervalIntegral Filter Topology Complex Finset
open scoped Classical

namespace RHTower

open SteinhausModel

noncomputable section

/-- The Steinhaus-model amplitude `∑_{n∈s} a_n X_n(ω)`. -/
def steinhausAmp (a : ℕ → ℝ) (s : Finset ℕ) (ω : Omega) : ℂ :=
  ∑ n ∈ s, (a n : ℂ) * X n ω

theorem measurable_steinhausAmp (a : ℕ → ℝ) (s : Finset ℕ) : Measurable (steinhausAmp a s) := by
  unfold steinhausAmp
  exact Finset.measurable_sum s fun n _ => (measurable_X n).const_mul _

theorem norm_steinhausAmp_le (a : ℕ → ℝ) (s : Finset ℕ) (ω : Omega) :
    ‖steinhausAmp a s ω‖ ≤ ∑ n ∈ s, |a n| := by
  unfold steinhausAmp
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, norm_X, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem norm_dpoly_le_dirichletPolynomialTorusLogUpperLaw (a : ℕ → ℝ) (s : Finset ℕ) (t : ℝ) :
    ‖dpoly a s t‖ ≤ ∑ n ∈ s, |a n| := by
  unfold dpoly cterm
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have hre : (-(t : ℂ) * Complex.I * (Real.log n : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hre, Real.exp_zero, mul_one]

/-- The coefficient-sum bound. -/
def coeffBound (a : ℕ → ℝ) (s : Finset ℕ) : ℝ := (∑ n ∈ s, |a n|) ^ (2 : ℕ)

theorem normSq_dpoly_mem (a : ℕ → ℝ) (s : Finset ℕ) (t : ℝ) :
    ‖dpoly a s t‖ ^ (2 : ℕ) ∈ Set.Icc (0 : ℝ) (coeffBound a s) :=
  ⟨by positivity, pow_le_pow_left₀ (norm_nonneg _) (norm_dpoly_le_dirichletPolynomialTorusLogUpperLaw a s t) 2⟩

theorem normSq_steinhausAmp_mem (a : ℕ → ℝ) (s : Finset ℕ) (ω : Omega) :
    ‖steinhausAmp a s ω‖ ^ (2 : ℕ) ∈ Set.Icc (0 : ℝ) (coeffBound a s) :=
  ⟨by positivity, pow_le_pow_left₀ (norm_nonneg _) (norm_steinhausAmp_le a s ω) 2⟩

theorem integrable_comp_normSq_steinhausAmp (a : ℕ → ℝ) (s : Finset ℕ) {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) :
    Integrable (fun ω => ψ (‖steinhausAmp a s ω‖ ^ (2 : ℕ))) steinhausMeasure := by
  have hmeas : Measurable (fun ω => ψ (‖steinhausAmp a s ω‖ ^ (2 : ℕ))) :=
    hψ.measurable.comp ((measurable_steinhausAmp a s).norm.pow_const 2)
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := coeffBound a s)).exists_bound_of_continuousOn
    hψ.continuousOn
  refine Integrable.of_bound hmeas.aestronglyMeasurable K ?_
  filter_upwards with ω
  exact hK _ (normSq_steinhausAmp_mem a s ω)

/-- Polynomial evaluation as a finite power sum. -/
theorem polynomial_eval_normSq (q : Polynomial ℝ) (x : ℂ) :
    q.eval (‖x‖ ^ (2 : ℕ)) = ∑ j ∈ range (q.natDegree + 1), q.coeff j * ‖x‖ ^ (2 * j) := by
  rw [Polynomial.eval_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_mul]

/-- **Continuous Bohr transfer (Cesàro form).** For every continuous `φ`, the time average of
`φ(‖F‖²)` converges to the Steinhaus-model expectation of `φ(‖∑ a_n X_n‖²)`. -/
theorem tendsto_contMoment_average_steinhaus (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n)
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    Tendsto (fun U : ℝ => U⁻¹ * ∫ t in (0:ℝ)..U, φ (‖dpoly a s t‖ ^ (2 : ℕ))) atTop
      (𝓝 (∫ ω, φ (‖steinhausAmp a s ω‖ ^ (2 : ℕ)) ∂steinhausMeasure)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set B := coeffBound a s with hB
  have hB0 : 0 ≤ B := by rw [hB, coeffBound]; positivity
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn 0 B φ hφ.continuousOn (ε / 4)
    (by positivity)
  -- the polynomial moment converges
  have hpoly := tendsto_polyMoment_average_steinhaus a s hs q.natDegree q.coeff
  have hcontD : Continuous (dpoly a s) := by
    unfold dpoly cterm
    exact continuous_finset_sum _ fun n _ => by fun_prop
  have hcontF : Continuous (fun t : ℝ => ‖dpoly a s t‖ ^ (2 : ℕ)) := by fun_prop
  -- rewrite the polynomial moment as q evaluated at ‖·‖²
  have hrwF : ∀ U : ℝ, U⁻¹ * ∫ t in (0:ℝ)..U,
      ∑ j ∈ range (q.natDegree + 1), q.coeff j * ‖dpoly a s t‖ ^ (2 * j)
      = U⁻¹ * ∫ t in (0:ℝ)..U, q.eval (‖dpoly a s t‖ ^ (2 : ℕ)) := by
    intro U
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    rw [polynomial_eval_normSq]
  have hint_pow : ∀ j : ℕ, Integrable (fun ω => q.coeff j * ‖steinhausAmp a s ω‖ ^ (2 * j))
      steinhausMeasure := by
    intro j
    have := integrable_comp_normSq_steinhausAmp a s (ψ := fun x => q.coeff j * x ^ j)
      (by fun_prop)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [pow_mul]
  have hrwM : ∑ j ∈ range (q.natDegree + 1),
      q.coeff j * ∫ ω, ‖steinhausAmp a s ω‖ ^ (2 * j) ∂steinhausMeasure
      = ∫ ω, q.eval (‖steinhausAmp a s ω‖ ^ (2 : ℕ)) ∂steinhausMeasure := by
    have : ∀ j : ℕ, q.coeff j * ∫ ω, ‖steinhausAmp a s ω‖ ^ (2 * j) ∂steinhausMeasure
        = ∫ ω, q.coeff j * ‖steinhausAmp a s ω‖ ^ (2 * j) ∂steinhausMeasure := by
      intro j
      rw [MeasureTheory.integral_const_mul]
    simp_rw [this]
    rw [← MeasureTheory.integral_finset_sum _ (fun j _ => hint_pow j)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ω
    rw [polynomial_eval_normSq]
  simp_rw [steinhausAmp] at hrwM
  simp_rw [hrwF, hrwM] at hpoly
  rw [Metric.tendsto_atTop] at hpoly
  obtain ⟨U₀, hU₀⟩ := hpoly (ε / 4) (by positivity)
  refine ⟨max U₀ 1, fun U hU => ?_⟩
  have hU0 : 0 < U := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hU)
  have hU1 := hU₀ U (le_trans (le_max_left _ _) hU)
  -- the three pieces
  have hqφ : ∀ x ∈ Set.Icc (0 : ℝ) B, |q.eval x - φ x| < ε / 4 := hq
  have hpiece1 : |(U⁻¹ * ∫ t in (0:ℝ)..U, φ (‖dpoly a s t‖ ^ (2 : ℕ)))
      - (U⁻¹ * ∫ t in (0:ℝ)..U, q.eval (‖dpoly a s t‖ ^ (2 : ℕ)))| ≤ ε / 4 := by
    rw [← mul_sub]
    have hcφ : Continuous (fun t : ℝ => φ (‖dpoly a s t‖ ^ (2 : ℕ))) := hφ.comp hcontF
    have hcq : Continuous (fun t : ℝ => q.eval (‖dpoly a s t‖ ^ (2 : ℕ))) :=
      (Polynomial.continuous q).comp hcontF
    rw [← intervalIntegral.integral_sub (hcφ.intervalIntegrable _ _) (hcq.intervalIntegrable _ _)]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hU0)]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := U) (C := ε / 4)
      (f := fun t => φ (‖dpoly a s t‖ ^ (2 : ℕ)) - q.eval (‖dpoly a s t‖ ^ (2 : ℕ))) (by
        intro t _
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact (hqφ _ (normSq_dpoly_mem a s t)).le)
    rw [Real.norm_eq_abs] at hbound
    calc U⁻¹ * |∫ t in (0:ℝ)..U, φ (‖dpoly a s t‖ ^ (2 : ℕ)) - q.eval (‖dpoly a s t‖ ^ (2 : ℕ))|
        ≤ U⁻¹ * (ε / 4 * |U - 0|) := by gcongr
      _ = ε / 4 := by
          rw [sub_zero, abs_of_pos hU0]
          field_simp
  have hpiece3 : |(∫ ω, q.eval (‖steinhausAmp a s ω‖ ^ (2 : ℕ)) ∂steinhausMeasure)
      - (∫ ω, φ (‖steinhausAmp a s ω‖ ^ (2 : ℕ)) ∂steinhausMeasure)| ≤ ε / 4 := by
    rw [← integral_sub (integrable_comp_normSq_steinhausAmp a s (Polynomial.continuous q))
      (integrable_comp_normSq_steinhausAmp a s hφ)]
    have hbound := norm_integral_le_of_norm_le_const (μ := steinhausMeasure) (C := ε / 4)
      (f := fun ω => q.eval (‖steinhausAmp a s ω‖ ^ (2 : ℕ)) - φ (‖steinhausAmp a s ω‖ ^ (2 : ℕ))) (by
        filter_upwards with ω
        rw [Real.norm_eq_abs]
        exact (hqφ _ (normSq_steinhausAmp_mem a s ω)).le)
    rw [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] at hbound
    exact hbound
  rw [Real.dist_eq] at hU1 ⊢
  set IF : ℝ := U⁻¹ * ∫ t in (0:ℝ)..U, φ (‖dpoly a s t‖ ^ (2 : ℕ)) with hIF
  set IQ : ℝ := U⁻¹ * ∫ t in (0:ℝ)..U, q.eval (‖dpoly a s t‖ ^ (2 : ℕ)) with hIQ
  set MQ : ℝ := ∫ ω, q.eval (‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ (2 : ℕ)) ∂steinhausMeasure with hMQ
  set MF : ℝ := ∫ ω, φ (‖steinhausAmp a s ω‖ ^ (2 : ℕ)) ∂steinhausMeasure with hMF
  have hMQ' : (∫ ω, q.eval (‖steinhausAmp a s ω‖ ^ (2 : ℕ)) ∂steinhausMeasure) = MQ := by
    rw [hMQ]; rfl
  rw [hMQ'] at hpiece3
  have h1 : |IF - IQ| ≤ ε / 4 := hpiece1
  have h2 : |IQ - MQ| < ε / 4 := hU1
  have h3 : |MQ - MF| ≤ ε / 4 := hpiece3
  calc |IF - MF| = |(IF - IQ) + (IQ - MQ) + (MQ - MF)| := by ring_nf
    _ ≤ |IF - IQ| + |IQ - MQ| + |MQ - MF| := abs_add_three _ _ _
    _ < ε / 4 + ε / 4 + ε / 4 := by linarith
    _ < ε := by linarith


/-- **Continuous Bohr transfer on dyadic windows.** -/
theorem tendsto_contMoment_window_steinhaus (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n)
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in T..(2 * T), φ (‖dpoly a s t‖ ^ (2 : ℕ))) atTop
      (𝓝 (∫ ω, φ (‖steinhausAmp a s ω‖ ^ (2 : ℕ)) ∂steinhausMeasure)) := by
  have hcontD : Continuous (dpoly a s) := by
    unfold dpoly cterm
    exact continuous_finset_sum _ fun n _ => by fun_prop
  have hc : Continuous (fun t : ℝ => φ (‖dpoly a s t‖ ^ (2 : ℕ))) := by fun_prop
  have hlim := tendsto_contMoment_average_steinhaus a s hs φ hφ
  set L := ∫ ω, φ (‖steinhausAmp a s ω‖ ^ (2 : ℕ)) ∂steinhausMeasure with hL
  have h2 : Tendsto (fun T : ℝ => (2 * T)⁻¹ * ∫ t in (0:ℝ)..(2 * T), φ (‖dpoly a s t‖ ^ (2 : ℕ)))
      atTop (𝓝 L) :=
    hlim.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hcomb : Tendsto (fun T : ℝ =>
      2 * ((2 * T)⁻¹ * ∫ t in (0:ℝ)..(2 * T), φ (‖dpoly a s t‖ ^ (2 : ℕ)))
        - T⁻¹ * ∫ t in (0:ℝ)..T, φ (‖dpoly a s t‖ ^ (2 : ℕ))) atTop (𝓝 (2 * L - L)) :=
    (h2.const_mul 2).sub hlim
  rw [show 2 * L - L = L by ring] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hsplit : (∫ t in (0:ℝ)..(2 * T), φ (‖dpoly a s t‖ ^ (2 : ℕ)))
      - ∫ t in (0:ℝ)..T, φ (‖dpoly a s t‖ ^ (2 : ℕ)) = ∫ t in T..(2 * T), φ (‖dpoly a s t‖ ^ (2 : ℕ)) :=
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)
  have h2T : (2 : ℝ) * (2 * T)⁻¹ = T⁻¹ := by
    field_simp
  rw [← hsplit, ← mul_assoc, h2T, ← mul_sub]

/-- The real Dirichlet polynomial on the imaginary axis is the entire Dirichlet polynomial. -/
theorem edPoly_ofReal_imaginaryAxis (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (t : ℝ) :
    edPoly (fun n => (a n : ℂ)) s (((0 : ℝ) : ℂ) + (t : ℂ) * I) = dpoly a s t := by
  unfold edPoly dpoly cterm
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : ((n : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hs n hn
    exact_mod_cast this.ne'
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  congr 2
  push_cast
  ring

/-- The zeros of a nondegenerate Dirichlet polynomial on a window are finite. -/
theorem finite_window_zeros_dpoly (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n)
    (hne : ∃ z : ℂ, edPoly (fun n => (a n : ℂ)) s z ≠ 0) (T₁ T₂ : ℝ) :
    {t : ℝ | t ∈ Set.Icc T₁ T₂ ∧ dpoly a s t = 0}.Finite := by
  have hf : AnalyticOnNhd ℂ (edPoly (fun n => (a n : ℂ)) s) Set.univ :=
    analyticOnNhd_edPoly _ hs
  have hfin := entire_zeros_closedRectangle_finite hf hne ((T₁ : ℂ) * I) ((T₂ : ℂ) * I)
  refine (hfin.image Complex.im).subset ?_
  intro t ht
  refine ⟨((0 : ℝ) : ℂ) + (t : ℂ) * I, ⟨?_, ?_⟩, ?_⟩
  · rw [Complex.mem_reProdIm]
    constructor
    · simp
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.mul_re, sub_zero,
        zero_mul, add_zero]
      rw [Set.uIcc_of_le (ht.1.1.trans ht.1.2)]
      exact ht.1
  · rw [edPoly_ofReal_imaginaryAxis a s hs t]
    exact ht.2
  · simp

/-- Interval integrability of `log ‖F‖` on any window. -/
theorem intervalIntegrable_log_norm_dpoly (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n)
    (T₁ T₂ : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖dpoly a s t‖) volume T₁ T₂ := by
  have hf : AnalyticOnNhd ℂ (edPoly (fun n => (a n : ℂ)) s) Set.univ :=
    analyticOnNhd_edPoly _ hs
  have := intervalIntegrable_log_norm_vertical_of_entire hf 0 T₁ T₂
  refine this.congr ?_
  intro t _
  simp only
  rw [edPoly_ofReal_imaginaryAxis a s hs t]

/-- The truncated logarithm `½ log max(x, ε²)`. -/
def logMaxHalf (ε : ℝ) (x : ℝ) : ℝ := (1 / 2) * Real.log (max x (ε ^ (2 : ℕ)))

theorem continuous_logMaxHalf {ε : ℝ} (hε : 0 < ε) : Continuous (logMaxHalf ε) := by
  unfold logMaxHalf
  refine continuous_const.mul (Continuous.log (continuous_id.max continuous_const) ?_)
  intro x
  have : 0 < max x (ε ^ (2 : ℕ)) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  exact this.ne'

theorem log_norm_le_logMaxHalf {ε : ℝ} (hε : 0 < ε) {w : ℂ} (hw : w ≠ 0) :
    Real.log ‖w‖ ≤ logMaxHalf ε (‖w‖ ^ (2 : ℕ)) := by
  unfold logMaxHalf
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have h1 : Real.log ‖w‖ = (1 / 2) * Real.log (‖w‖ ^ (2 : ℕ)) := by
    rw [Real.log_pow]; push_cast; ring
  rw [h1]
  gcongr
  exact le_max_left _ _

/-- **The torus upper law on dyadic windows.**  For every `ε > 0` and `η > 0`, eventually
`(1/T)∫_T^{2T} log ‖F(t)‖ dt ≤ ½ E_χ log max(‖∑ aₙ χ(n)‖², ε²) + η`. -/
theorem eventually_window_logMean_dpoly_le (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n)
    (hne : ∃ z : ℂ, edPoly (fun n => (a n : ℂ)) s z ≠ 0) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ T in atTop, T⁻¹ * ∫ t in T..(2 * T), Real.log ‖dpoly a s t‖ ≤
      (∫ ω, logMaxHalf ε (‖steinhausAmp a s ω‖ ^ (2 : ℕ)) ∂steinhausMeasure) + η := by
  have hlim := tendsto_contMoment_window_steinhaus a s hs (logMaxHalf ε) (continuous_logMaxHalf hε)
  have hev := (Metric.tendsto_atTop.mp hlim) η hη
  obtain ⟨T₀, hT₀⟩ := hev
  filter_upwards [eventually_ge_atTop T₀, eventually_gt_atTop (0 : ℝ)] with T hT hTpos
  have h1 := hT₀ T hT
  rw [Real.dist_eq, abs_lt] at h1
  have hcontD : Continuous (dpoly a s) := by
    unfold dpoly cterm
    exact continuous_finset_sum _ fun n _ => by fun_prop
  have hcφ : Continuous (fun t : ℝ => logMaxHalf ε (‖dpoly a s t‖ ^ (2 : ℕ))) :=
    (continuous_logMaxHalf hε).comp (by fun_prop)
  have hmono : (∫ t in T..(2 * T), Real.log ‖dpoly a s t‖) ≤
      ∫ t in T..(2 * T), logMaxHalf ε (‖dpoly a s t‖ ^ (2 : ℕ)) := by
    refine intervalIntegral.integral_mono_ae_restrict (by linarith : T ≤ 2 * T)
      (intervalIntegrable_log_norm_dpoly a s hs T (2 * T)) (hcφ.intervalIntegrable _ _) ?_
    have hfin := finite_window_zeros_dpoly a s hs hne T (2 * T)
    have hnull := hfin.measure_zero volume
    rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at hnull
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr ?_
    filter_upwards [hnull] with t ht hmem
    have hne0 : dpoly a s t ≠ 0 := fun h0 => ht ⟨hmem, h0⟩
    exact log_norm_le_logMaxHalf hε hne0
  calc T⁻¹ * ∫ t in T..(2 * T), Real.log ‖dpoly a s t‖
      ≤ T⁻¹ * ∫ t in T..(2 * T), logMaxHalf ε (‖dpoly a s t‖ ^ (2 : ℕ)) := by
        gcongr
    _ ≤ (∫ ω, logMaxHalf ε (‖steinhausAmp a s ω‖ ^ (2 : ℕ)) ∂steinhausMeasure) + η := by
        linarith [h1.2]

end

end RHTower
