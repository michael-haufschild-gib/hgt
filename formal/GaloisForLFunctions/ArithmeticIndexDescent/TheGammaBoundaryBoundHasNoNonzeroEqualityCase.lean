import GaloisForLFunctions.ArithmeticIndexDescent.TheGammaBoundaryReserveIsAnExactSquare
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Rigidity of equality in the Gamma boundary bound

The exact Schur weight has a nonintegrable square at the boundary. Vanishing
of the square reserve forces an L2 profile to be a constant multiple of that
weight, hence to vanish. Every nonzero profile therefore has a strict quadratic
deficit. This does not assert a uniform gap in the operator norm.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped ENNReal InnerProduct
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

local notation "μ₊" => (volume.restrict (Ioi (0 : ℝ)))

/-- The boundary square is the reciprocal hyperbolic density. -/
theorem gammaBoundarySchurWeight_sq {t : ℝ} (ht : 0 < t) :
    gammaBoundarySchurWeight t ^ 2 = Real.exp (-t) / (1 - Real.exp (-2 * t)) := by
  have hd : 0 < 1 - Real.exp (-2 * t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [ht]))
  rw [gammaBoundarySchurWeight_eq, div_pow, Real.sq_sqrt hd.le,
    pow_two, ← Real.exp_add, show -t / 2 + -t / 2 = -t by ring]

/-- The critical boundary singularity has a fixed reciprocal lower bound. -/
theorem gammaBoundarySchurWeight_sq_ge_inv {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (Real.exp (-1) / 2) * t⁻¹ ≤ gammaBoundarySchurWeight t ^ 2 := by
  have hd : 0 < 1 - Real.exp (-2 * t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [ht]))
  have hden : 1 - Real.exp (-2 * t) ≤ 2 * t := by
    have he := Real.add_one_le_exp (-2 * t)
    linarith only [he]
  have hnum : Real.exp (-1) ≤ Real.exp (-t) :=
    Real.exp_le_exp.mpr (by linarith only [ht1])
  rw [gammaBoundarySchurWeight_sq ht,
    show (Real.exp (-1) / 2) * t⁻¹ = Real.exp (-1) / (2 * t) by ring]
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * t) hd).mpr
  exact (mul_le_mul_of_nonneg_left hden (Real.exp_pos (-1)).le).trans
    (mul_le_mul_of_nonneg_right hnum (by positivity))

/-- A reciprocal majorant controls the same weight on the entire positive ray. -/
theorem gammaBoundarySchurWeight_sq_le_inv {t : ℝ} (ht : 0 < t) :
    gammaBoundarySchurWeight t ^ 2 ≤ t⁻¹ := by
  have hd : 0 < 1 - Real.exp (-2 * t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [ht]))
  have hm := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) (Real.exp_pos (-t)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
  have he : Real.exp (-2 * t) ≤ Real.exp (-t) :=
    Real.exp_le_exp.mpr (by linarith only [ht])
  rw [gammaBoundarySchurWeight_sq ht, inv_eq_one_div]
  apply (div_le_div_iff₀ hd ht).mpr
  nlinarith only [hm, he]

/-- The exact positive Schur weight is not an L2 boundary vector. -/
theorem not_integrable_gammaBoundarySchurWeight_sq :
    ¬ IntegrableOn (fun t => gammaBoundarySchurWeight t ^ 2) (Ioi (0 : ℝ)) := by
  intro hi
  let c : ℝ := Real.exp (-1) / 2
  have hc : 0 < c := div_pos (Real.exp_pos _) (by norm_num)
  have hsmall : IntegrableOn (fun t => gammaBoundarySchurWeight t ^ 2) (Ioo (0 : ℝ) 1) :=
    hi.mono_set fun _ ht => ht.1
  have hscaled : IntegrableOn (fun t : ℝ => c * t⁻¹) (Ioo 0 1) := by
    refine hsmall.mono' (measurable_const.mul measurable_inv).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg hc.le (inv_nonneg.mpr ht.1.le))]
    exact gammaBoundarySchurWeight_sq_ge_inv ht.1 ht.2.le
  have hinv : IntegrableOn (fun t : ℝ => t⁻¹) (Ioo 0 1) := by
    refine (hscaled.const_mul (1 / c)).congr ?_
    filter_upwards [] with t
    change (1 / c) * (c * t⁻¹) = t⁻¹
    rw [← mul_assoc, one_div_mul_cancel hc.ne', one_mul]
  have hp : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioo 0 1) := by
    simpa only [Real.rpow_neg_one] using hinv
  have hb := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mp hp
  exact lt_irrefl (-1 : ℝ) hb

/-- Only the zero constant multiple of the Schur weight has finite square mass. -/
theorem integrable_sq_mul_gammaBoundarySchurWeight_iff (c : ℂ) :
    IntegrableOn (fun t => ‖c * (gammaBoundarySchurWeight t : ℂ)‖ ^ 2) (Ioi (0 : ℝ)) ↔
      c = 0 := by
  constructor
  · intro hi
    by_contra hc
    have hcn : 0 < ‖c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hc)
    apply not_integrable_gammaBoundarySchurWeight_sq
    refine (hi.const_mul (1 / ‖c‖ ^ 2)).congr ?_
    filter_upwards [] with t
    change (1 / ‖c‖ ^ 2) * ‖c * (gammaBoundarySchurWeight t : ℂ)‖ ^ 2 = _
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      ← mul_assoc, one_div_mul_cancel hcn.ne', one_mul]
  · rintro rfl
    simp only [zero_mul, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact integrable_zero _ _ _

private theorem positiveRay_ne_zero : μ₊ ≠ 0 := by
  intro h
  have he := congrArg (fun m : Measure ℝ => m Set.univ) h
  change μ₊ Set.univ = 0 at he
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioi] at he
  exact ENNReal.top_ne_zero he

/-- Equality in the actual Gamma quadratic bound forces the zero L2 vector. -/
theorem gammaBoundary_quadratic_eq_iff (f : SuzukiPositiveL2) :
    (inner ℂ f (ccmGammaBoundaryCLM f)).re = (Real.pi / 2) * ‖f‖ ^ 2 ↔ f = 0 := by
  constructor
  · intro he
    have hpos : ∀ᵐ p : ℝ × ℝ ∂(μ₊.prod μ₊), 0 < p.1 ∧ 0 < p.2 := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
    have hnn : 0 ≤ᵐ[μ₊.prod μ₊] gammaBoundaryPairReserveDensity f f := by
      filter_upwards [hpos] with p hp
      exact gammaBoundaryPairReserveDensity_nonneg f f hp.1 hp.2
    have hI : (∫ p, gammaBoundaryPairReserveDensity f f p ∂(μ₊.prod μ₊)) = 0 := by
      rw [← gammaBoundary_quadratic_deficit f, he, sub_self]
    have hzero := (integral_eq_zero_iff_of_nonneg_ae hnn
      (integrable_gammaBoundaryPairReserveDensity f f)).mp hI
    have hratio : ∀ᵐ p : ℝ × ℝ ∂(μ₊.prod μ₊),
        f p.1 / (gammaBoundarySchurWeight p.1 : ℂ) =
          f p.2 / (gammaBoundarySchurWeight p.2 : ℂ) := by
      filter_upwards [hpos, hzero] with p hp hz
      change gammaBoundaryPairReserveDensity f f p = 0 at hz
      unfold gammaBoundaryPairReserveDensity at hz
      have hk : archLevyDensity (p.1 + p.2) * gammaBoundarySchurWeight p.1 *
          gammaBoundarySchurWeight p.2 ≠ 0 :=
        mul_ne_zero (mul_ne_zero (archLevyDensity_pos (add_pos hp.1 hp.2)).ne'
          (gammaBoundarySchurWeight_pos hp.1).ne') (gammaBoundarySchurWeight_pos hp.2).ne'
      have hsq : ‖f p.1 / (gammaBoundarySchurWeight p.1 : ℂ) -
          f p.2 / (gammaBoundarySchurWeight p.2 : ℂ)‖ ^ 2 = 0 :=
        (mul_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right (by norm_num))).resolve_left hk
      have hn : ‖f p.1 / (gammaBoundarySchurWeight p.1 : ℂ) -
          f p.2 / (gammaBoundarySchurWeight p.2 : ℂ)‖ = 0 := by
        nlinarith only [hsq]
      exact sub_eq_zero.mp (norm_eq_zero.mp hn)
    letI : NeZero μ₊ := ⟨positiveRay_ne_zero⟩
    obtain ⟨s, hs⟩ := (Measure.ae_ae_of_ae_prod hratio).exists
    let c : ℂ := f s / (gammaBoundarySchurWeight s : ℂ)
    have hconst : (f : ℝ → ℂ) =ᵐ[μ₊] fun t => c * (gammaBoundarySchurWeight t : ℂ) := by
      filter_upwards [hs, ae_restrict_mem measurableSet_Ioi] with t ht htp
      have hw : (gammaBoundarySchurWeight t : ℂ) ≠ 0 := by
        exact_mod_cast (gammaBoundarySchurWeight_pos htp).ne'
      exact (div_eq_iff hw).mp ht.symm
    have hi : Integrable (fun t => ‖f t‖ ^ 2) μ₊ :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
    have hic : IntegrableOn (fun t => ‖c * (gammaBoundarySchurWeight t : ℂ)‖ ^ 2)
        (Ioi (0 : ℝ)) := by
      refine hi.congr ?_
      filter_upwards [hconst] with t ht
      rw [ht]
    have hc : c = 0 := (integrable_sq_mul_gammaBoundarySchurWeight_iff c).mp hic
    apply Lp.ext
    filter_upwards [hconst, Lp.coeFn_zero ℂ 2 μ₊] with t ht hz
    rw [hc, zero_mul] at ht
    exact ht.trans hz.symm
  · rintro rfl
    simp

/-- Each nonzero profile leaves a strict reserve, with no claim of a uniform spectral gap. -/
theorem gammaBoundary_quadratic_lt_of_ne_zero {f : SuzukiPositiveL2} (hf : f ≠ 0) :
    (inner ℂ f (ccmGammaBoundaryCLM f)).re < (Real.pi / 2) * ‖f‖ ^ 2 := by
  have hnn : 0 ≤ᵐ[μ₊.prod μ₊] gammaBoundaryPairReserveDensity f f := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    exact gammaBoundaryPairReserveDensity_nonneg f f hp.1 hp.2
  have hnonneg := integral_nonneg_of_ae hnn
  rw [← gammaBoundary_quadratic_deficit f] at hnonneg
  have hle : (inner ℂ f (ccmGammaBoundaryCLM f)).re ≤ (Real.pi / 2) * ‖f‖ ^ 2 :=
    sub_nonneg.mp hnonneg
  by_contra hlt
  exact hf ((gammaBoundary_quadratic_eq_iff f).mp (le_antisymm hle (le_of_not_gt hlt)))

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.not_integrable_gammaBoundarySchurWeight_sq
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.gammaBoundary_quadratic_eq_iff
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.gammaBoundary_quadratic_lt_of_ne_zero
