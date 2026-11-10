import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Quadratic scaling of a joint analytic germ

A finite limit after division by the square of a real parameter forces
the constant and linear Taylor terms to vanish along that direction.
The limit is therefore the quadratic homogeneous Taylor term. In two
complex variables its restriction to directions `(1,w)` is entire.
-/

open Complex Filter Topology Set
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

private theorem quadratic_partialSum (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (t : ℂ) (v : ℂ × ℂ) :
    p.partialSum 3 (t • v) = p 0 (fun _ => v) + t * p 1 (fun _ => v) +
      t ^ 2 * p 2 (fun _ => v) := by
  simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add]
  simp only [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, pow_zero, pow_one, one_mul]

private theorem real_parameter_tendsto :
    Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
  simpa only [Complex.ofReal_zero] using
    (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds

/-- A finite quadratic Laurent limit removes both negative powers. -/
private theorem quadratic_laurent_limit {a b c L : ℂ}
    (h : Tendsto (fun t : ℝ => (a + (t : ℂ) * b + (t : ℂ) ^ 2 * c) / (t : ℂ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 L)) : a = 0 ∧ b = 0 ∧ L = c := by
  have ht := real_parameter_tendsto
  have ha : a = 0 := by
    have hmul := h.mul (ht.pow 2)
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at hmul
    have he : (fun t : ℝ =>
        ((a + (t : ℂ) * b + (t : ℂ) ^ 2 * c) / (t : ℂ) ^ 2) * (t : ℂ) ^ 2) =ᶠ[𝓝[>] 0]
        (fun t : ℝ => a + (t : ℂ) * b + (t : ℂ) ^ 2 * c) := by
      filter_upwards [self_mem_nhdsWithin] with t ht0
      exact div_mul_cancel₀ _ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt ht0)))
    have hp := ((tendsto_const_nhds.add (ht.mul_const b)).add ((ht.pow 2).mul_const c))
    simp only [zero_mul, add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hp
    exact tendsto_nhds_unique hp (hmul.congr' he)
  have hb : b = 0 := by
    have hmul := h.mul ht
    simp only [mul_zero] at hmul
    have he : (fun t : ℝ =>
        ((a + (t : ℂ) * b + (t : ℂ) ^ 2 * c) / (t : ℂ) ^ 2) * (t : ℂ)) =ᶠ[𝓝[>] 0]
        (fun t : ℝ => b + (t : ℂ) * c) := by
      filter_upwards [self_mem_nhdsWithin] with t ht0
      have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht0)
      rw [ha]
      field_simp [htC]
      <;> ring
    have hp := tendsto_const_nhds.add (ht.mul_const c)
    simp only [zero_mul, add_zero] at hp
    exact tendsto_nhds_unique hp (hmul.congr' he)
  refine ⟨ha, hb, ?_⟩
  have he : (fun t : ℝ => (a + (t : ℂ) * b + (t : ℂ) ^ 2 * c) / (t : ℂ) ^ 2) =ᶠ[𝓝[>] 0]
      (fun _ : ℝ => c) := by
    filter_upwards [self_mem_nhdsWithin] with t ht0
    rw [ha, hb, mul_zero, zero_add, zero_add]
    exact mul_div_cancel_left₀ c (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt ht0)))
  exact tendsto_nhds_unique (h.congr' he) tendsto_const_nhds

private theorem cubic_remainder_scaled {U : ℂ × ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ} {x : ℂ × ℂ}
    (hU : HasFPowerSeriesAt U p x) (v : ℂ × ℂ) :
    Tendsto (fun t : ℝ => (U (x + (t : ℂ) • v) - p.partialSum 3 ((t : ℂ) • v)) / (t : ℂ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hray : Tendsto (fun t : ℝ => (t : ℂ) • v) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_smul] using real_parameter_tendsto.smul_const v
  obtain ⟨C, hC⟩ := ((hU.isBigO_sub_partialSum_pow 3).comp_tendsto hray).bound
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ‖(U (x + (t : ℂ) • v) - p.partialSum 3 ((t : ℂ) • v)) / (t : ℂ) ^ 2‖ ≤
        (C * ‖v‖ ^ 3) * t := by
    filter_upwards [hC, self_mem_nhdsWithin] with t hCt ht
    change 0 < t at ht
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
    have hnorm : ‖(t : ℂ) • v‖ = t * ‖v‖ := by
      rw [norm_smul, norm_real, Real.norm_eq_abs, abs_of_pos ht]
    change ‖U (x + (t : ℂ) • v) - p.partialSum 3 ((t : ℂ) • v)‖ ≤ C * ‖‖(t : ℂ) • v‖ ^ 3‖ at hCt
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hnorm] at hCt
    rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos ht]
    apply (div_le_div_of_nonneg_right hCt ht2.le).trans_eq
    field_simp [ht.ne']
    ring
  apply squeeze_zero_norm' hb
  simpa only [mul_zero] using
    (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun t : ℝ => (C * ‖v‖ ^ 3) * t) (𝓝[>] 0) (𝓝 ((C * ‖v‖ ^ 3) * 0)))

/-- The quadratic rescaling limit of a joint analytic germ is its second
homogeneous Taylor coefficient on each direction. -/
theorem joint_quadratic_limit_eq_coefficient {U : ℂ × ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ} {x : ℂ × ℂ}
    (hU : HasFPowerSeriesAt U p x) (v : ℂ × ℂ) {L : ℂ}
    (hlim : Tendsto (fun t : ℝ => U (x + (t : ℂ) • v) / (t : ℂ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 L)) : L = p 2 (fun _ => v) := by
  have hh := hlim.sub (cubic_remainder_scaled hU v)
  simp only [sub_zero] at hh
  have he : (fun t : ℝ => U (x + (t : ℂ) • v) / (t : ℂ) ^ 2 -
      (U (x + (t : ℂ) • v) - p.partialSum 3 ((t : ℂ) • v)) / (t : ℂ) ^ 2) =
      (fun t : ℝ => (p 0 (fun _ => v) + (t : ℂ) * p 1 (fun _ => v) +
        (t : ℂ) ^ 2 * p 2 (fun _ => v)) / (t : ℂ) ^ 2) := by
    funext t
    rw [← sub_div, sub_sub_cancel, quadratic_partialSum]
  rw [he] at hh
  exact (quadratic_laurent_limit hh).2.2

/-- A jointly analytic endpoint germ can have only an entire directional
quadratic scaling profile. -/
theorem joint_quadratic_limit_entire {U : ℂ × ℂ → ℂ} (hU : AnalyticAt ℂ U (0, 1))
    {Q : ℂ → ℂ}
    (hlim : ∀ w : ℂ, 0 < w.re →
      Tendsto (fun t : ℝ => U ((t : ℂ), 1 + (t : ℂ) * w) / (t : ℂ) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (Q w))) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F univ ∧ ∀ w : ℂ, 0 < w.re → Q w = F w := by
  obtain ⟨p, hp⟩ := hU
  refine ⟨fun w => p 2 (fun _ => (1, w)), ?_, ?_⟩
  · intro w _
    exact (p 2).analyticAt.comp (by fun_prop)
  · intro w hw
    apply joint_quadratic_limit_eq_coefficient hp (1, w)
    simpa only [Prod.smul_mk, smul_eq_mul, mul_one, Prod.mk_add_mk, zero_add] using hlim w hw

#print axioms joint_quadratic_limit_eq_coefficient
#print axioms joint_quadratic_limit_entire
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
