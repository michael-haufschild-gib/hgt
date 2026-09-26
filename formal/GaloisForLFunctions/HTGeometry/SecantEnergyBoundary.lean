import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Nonintegrable tangents force unbounded secant energy

Fatou turns a nonintegrable squared derivative into finite translation secants with arbitrarily large energy at arbitrarily small positive steps.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.SecantBoundary

lemma secant_sq_integrable {f : ℝ → ℝ} (hc : Continuous f)
    (hi : Integrable (fun t => f t^2)) (h : ℝ) :
    Integrable (fun t => ((f (t+h)-f t)/h)^2) := by
  have hdiff : Integrable (fun t => (f (t+h)-f t)^2) := by
    apply ((hi.comp_add_right h).add hi |>.const_mul 2).mono'
      (((hc.comp (continuous_id.add continuous_const)).sub hc).pow 2).aestronglyMeasurable
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (f (t+h)-f t)^2 ≤ 2*(f (t+h)^2+f t^2)
    nlinarith [sq_nonneg (f (t+h)+f t)]
  simpa only [div_pow] using hdiff.div_const (h^2)

lemma exists_large_secant {f f' : ℝ → ℝ} (hc : Continuous f)
    (hi : Integrable (fun t => f t^2))
    (hd : ∀ t > 0, HasDerivAt f (f' t) t)
    (hn : ¬IntegrableOn (fun t => f' t^2) (Ioi 0)) (C : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h ∈ Ioo 0 δ, C < ∫ t in Ioi (0:ℝ), ((f (t+h)-f t)/h)^2 := by
  by_contra! hbound
  let u : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hu (n : ℕ) : 0 < u n := by dsimp [u]; positivity
  have hut : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hur : Tendsto u atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hut
      (Eventually.of_forall hu)
  let q : ℕ → ℝ → ℝ := fun n t => ((f (t+u n)-f t)/u n)^2
  have hq (n : ℕ) : IntegrableOn (q n) (Ioi (0:ℝ)) :=
    (secant_sq_integrable hc hi (u n)).integrableOn
  apply hn
  apply integrable_of_tendsto (G := q)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htend := ((hd t ht).tendsto_slope_zero_right.comp hur).pow 2
    simpa only [q, Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using htend
  · exact fun n => (hq n).aestronglyMeasurable
  · apply ne_of_lt
    apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
    apply liminf_le_of_frequently_le'
    apply Eventually.frequently
    filter_upwards [hut.eventually (Iio_mem_nhds hδ)] with n hnδ
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hq n)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [q, Real.norm_eq_abs, abs_pow, sq_abs] using
      hbound (u n) ⟨hu n, hnδ⟩

end GaloisForLFunctions.HTGeometry.SecantBoundary
