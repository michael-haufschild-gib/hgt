import GaloisForLFunctions.HTGeometry.EinastoShapeSource

/-!
# The sharp Einasto shape threshold for the actual quadratic source

The two explicit profiles expose a complete classification. For q=exp(-a),
the actual source tends to negative infinity when q<2. At q=2 it has the
Gaussian finite limit. For q>2 only the bounded algebraic-sign defect survives.
Thus finite source regularity holds exactly for q≥2, or Einasto α≤1/2.
The same threshold holds for the literal appendix source near the center.
-/
noncomputable section
open Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- The finite core value, used only on the regular side of the classification. -/
def einastoShapeSourceCoreValue (d l a σ : ℝ) : ℝ :=
  (if exp (-a) = 2 then -72 * exp d * exp (-2 * l) else 0) +
    64 * Real.pi * (σ - 1) * exp d ^ 2

/-- Complete source limit without any assumed bound on the profile's shape. -/
theorem einastoShapeSource_complete_limit (d l a σ : ℝ) :
    Tendsto (fun t => quadraticRadialSource σ (einastoMetric d l a) (exp t)) atBot
      (if exp (-a) < 2 then atBot else 𝓝 (einastoShapeSourceCoreValue d l a σ)) := by
  have he : (fun t => quadraticRadialSource σ (einastoMetric d l a) (exp t)) =
      (fun t => exp ((exp (-a) - 2) * t - exp (-a) * l) * einastoShapeSourceFactor d l a (exp t) +
        einastoShapeSourceDefect d l a σ (exp t)) := by
    funext t
    exact einastoShapeSource_exp_decomposition d l a σ t
  rw [he]
  have hF := einastoShapeSourceFactor_core_limit d l a
  have hD := einastoShapeSourceDefect_core_limit d l a σ
  by_cases hs : exp (-a) < 2
  · rw [if_pos hs]
    have hlin : Tendsto (fun t : ℝ => (exp (-a) - 2) * t) atBot atTop :=
      tendsto_id.const_mul_atBot_of_neg (sub_neg.mpr hs)
    have hx : Tendsto (fun t : ℝ => exp ((exp (-a) - 2) * t - exp (-a) * l)) atBot atTop := by
      simpa only [exp_sub, Function.comp_def] using
        (tendsto_exp_atTop.comp hlin).atTop_div_const (exp_pos (exp (-a) * l))
    rw [← einastoShapeSourceFactor_core d l a] at hF
    exact (hx.atTop_mul_neg (einastoShapeSourceFactor_core_neg d l a) hF).atBot_add hD
  · rw [if_neg hs]
    by_cases hq : exp (-a) = 2
    · have hx (t : ℝ) : exp ((exp (-a) - 2) * t - exp (-a) * l) = exp (-2 * l) := by
        rw [hq]
        congr 1
        ring
      simp_rw [hx]
      have h := (hF.const_mul (exp (-2 * l))).add hD
      have hc : exp (-2 * l) * (-2 * exp (-a) * exp d * (exp (-a) + 1) * (exp (-a) + 4)) +
          64 * Real.pi * (σ - 1) * exp d ^ 2 = einastoShapeSourceCoreValue d l a σ := by
        unfold einastoShapeSourceCoreValue
        rw [if_pos hq, hq]
        ring
      rwa [hc] at h
    · have hq' : 2 < exp (-a) := lt_of_le_of_ne (not_lt.mp hs) (Ne.symm hq)
      have hlin : Tendsto (fun t : ℝ => (exp (-a) - 2) * t) atBot atBot :=
        tendsto_id.const_mul_atBot (sub_pos.mpr hq')
      have hx : Tendsto (fun t : ℝ => exp ((exp (-a) - 2) * t - exp (-a) * l)) atBot (𝓝 0) := by
        simpa only [exp_sub, Function.comp_def, zero_div] using
          (tendsto_exp_atBot.comp hlin).div_const (exp (exp (-a) * l))
      have h := (hx.mul hF).add hD
      simpa only [zero_mul, zero_add, einastoShapeSourceCoreValue, if_neg hq] using h

/-- No finite source limit is possible below the exact shape threshold. -/
theorem einastoShapeSource_finite_limit_iff (d l a σ k : ℝ) :
    Tendsto (fun t => quadraticRadialSource σ (einastoMetric d l a) (exp t)) atBot (𝓝 k) ↔
      2 ≤ exp (-a) ∧ k = einastoShapeSourceCoreValue d l a σ := by
  have h := einastoShapeSource_complete_limit d l a σ
  by_cases hs : exp (-a) < 2
  · rw [if_pos hs] at h
    constructor
    · intro hk
      exact (not_tendsto_nhds_of_tendsto_atBot h k hk).elim
    · rintro ⟨hq, _⟩
      exact (not_le.mpr hs hq).elim
  · rw [if_neg hs] at h
    constructor
    · intro hk
      exact ⟨not_lt.mp hs, tendsto_nhds_unique hk h⟩
    · rintro ⟨_, rfl⟩
      exact h

/-- A finite source limit exists exactly for shape exponent at least two. -/
theorem einastoShapeSource_regular_iff (d l a σ : ℝ) :
    (∃ k : ℝ, Tendsto (fun t => quadraticRadialSource σ (einastoMetric d l a) (exp t)) atBot (𝓝 k)) ↔
      2 ≤ exp (-a) := by
  simp only [einastoShapeSource_finite_limit_iff, exists_eq_right]

/-- The singular side is divergence to negative infinity, not just failure of a chosen finite limit. -/
theorem einastoShapeSource_diverges_iff (d l a σ : ℝ) :
    Tendsto (fun t => quadraticRadialSource σ (einastoMetric d l a) (exp t)) atBot atBot ↔
      exp (-a) < 2 := by
  have h := einastoShapeSource_complete_limit d l a σ
  by_cases hs : exp (-a) < 2
  · rw [if_pos hs] at h
    exact iff_of_true h hs
  · rw [if_neg hs] at h
    constructor
    · intro hb
      exact (not_tendsto_nhds_of_tendsto_atBot hb _ h).elim
    · intro hq
      exact (hs hq).elim

/-- The logarithmic shape parameter has the same sharp boundary as the Gaussian profile. -/
theorem einastoShapeSource_log_shape_iff (d l a σ : ℝ) :
    (∃ k : ℝ, Tendsto (fun t => quadraticRadialSource σ (einastoMetric d l a) (exp t)) atBot (𝓝 k)) ↔
      a ≤ -log 2 := by
  rw [einastoShapeSource_regular_iff]
  constructor
  · intro h
    have he : exp (log 2) ≤ exp (-a) := by
      simpa only [exp_log (by norm_num : (0 : ℝ) < 2)] using h
    have hl := exp_le_exp.mp he
    linarith
  · intro h
    have hl : log 2 ≤ -a := by linarith
    have he := exp_le_exp.mpr hl
    simpa only [exp_log (by norm_num : (0 : ℝ) < 2)] using he

/-- The paper's literal source obeys the same complete finite-limit classification. -/
theorem einastoAppendixSource_finite_limit_iff (d l a k : ℝ) :
    Tendsto (fun t => quadraticAppendixSource (einastoMetric d l a) (exp t)) atBot (𝓝 k) ↔
      2 ≤ exp (-a) ∧ k = einastoShapeSourceCoreValue d l a (-1) := by
  have he := quadraticAppendixSource_einasto_all_shapes_eventually d l a
  rw [tendsto_congr' he]
  exact einastoShapeSource_finite_limit_iff d l a (-1) k

theorem einastoAppendixSource_regular_iff (d l a : ℝ) :
    (∃ k : ℝ, Tendsto (fun t => quadraticAppendixSource (einastoMetric d l a) (exp t)) atBot (𝓝 k)) ↔
      2 ≤ exp (-a) := by
  simp only [einastoAppendixSource_finite_limit_iff, exists_eq_right]

theorem einastoAppendixSource_diverges_iff (d l a : ℝ) :
    Tendsto (fun t => quadraticAppendixSource (einastoMetric d l a) (exp t)) atBot atBot ↔
      exp (-a) < 2 := by
  have he := quadraticAppendixSource_einasto_all_shapes_eventually d l a
  rw [tendsto_congr' he]
  exact einastoShapeSource_diverges_iff d l a (-1)

/-- The shape-one source lies strictly on the singular side, with every algebraic sign. -/
theorem einastoShapeSource_exponential_diverges (d l σ : ℝ) :
    Tendsto (fun t => quadraticRadialSource σ (einastoMetric d l 0) (exp t)) atBot atBot := by
  apply (einastoShapeSource_diverges_iff d l 0 σ).mpr
  norm_num

/-- Every super-Gaussian shape has a finite source; no central derivative bounds are assumed. -/
theorem einastoShapeSource_superGaussian_regular (d l σ s : ℝ) :
    ∃ k : ℝ, Tendsto (fun t => quadraticRadialSource σ (einastoMetric d l (-log (2 + exp s))) (exp t)) atBot (𝓝 k) := by
  apply (einastoShapeSource_regular_iff d l (-log (2 + exp s)) σ).mpr
  rw [neg_neg, exp_log (by positivity : 0 < 2 + exp s)]
  linarith [exp_pos s]

/-- Above the threshold, only the algebraic sign discrepancy contributes to the core source. -/
theorem einastoShapeSource_superGaussian_limit (d l σ s : ℝ) :
    Tendsto (fun t => quadraticRadialSource σ (einastoMetric d l (-log (2 + exp s))) (exp t)) atBot
      (𝓝 (64 * Real.pi * (σ - 1) * exp d ^ 2)) := by
  apply (einastoShapeSource_finite_limit_iff d l (-log (2 + exp s)) σ _).mpr
  have hq : exp (-(-log (2 + exp s))) = 2 + exp s := by
    rw [neg_neg, exp_log (by positivity : 0 < 2 + exp s)]
  have hn : exp (-(-log (2 + exp s))) ≠ 2 := by
    rw [hq]
    linarith [exp_pos s]
  constructor
  · rw [hq]
    linarith [exp_pos s]
  · simp only [einastoShapeSourceCoreValue, if_neg hn, zero_add]

/-- At the exact Gaussian boundary, a nonzero derivative contribution remains. -/
theorem einastoShapeSource_gaussian_limit (d l σ : ℝ) :
    Tendsto (fun t => quadraticRadialSource σ (einastoMetric d l (-log 2)) (exp t)) atBot
      (𝓝 (-72 * exp d * exp (-2 * l) + 64 * Real.pi * (σ - 1) * exp d ^ 2)) := by
  apply (einastoShapeSource_finite_limit_iff d l (-log 2) σ _).mpr
  have hq : exp (-(-log 2)) = 2 := by
    rw [neg_neg, exp_log (by norm_num : (0 : ℝ) < 2)]
  constructor
  · rw [hq]
  · simp only [einastoShapeSourceCoreValue, if_pos hq]

end GaloisForLFunctions.HTGeometry
