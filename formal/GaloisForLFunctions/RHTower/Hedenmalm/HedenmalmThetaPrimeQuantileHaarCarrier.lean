import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPrimeTranslationHaarCarrier
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPrimeTranslationQuantileFlow

/-!
# The sigma-finite Haar carrier forced by prime quantile translation

The theta quantile prime flow is conjugate through the source CDF to ordinary additive
translation.  Transporting Haar measure through that CDF therefore produces an invariant measure
on the open probability interval.  It is locally finite with compact-interval mass equal to
quantile length, but its total interior mass is infinite.

More sharply, no nonzero finite measure supported on the probability interval is invariant under
even one genuine integer flow: the bounded coordinate is a strict Lyapunov function, while
measure invariance would preserve its integral.  Thus P-G103's covariant prime connection cannot
live on any finite stationary probability fibre.  The sigma-finite Haar/quantile carrier is forced
before any Xi divisor is read.
-/

open MeasureTheory Set Filter Topology

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmPrimeTranslation HedenmalmIntervalAnomaly


namespace HedenmalmThetaSource

/-- Additive Haar measure transported to the open theta quantile interval. -/
def thetaQuantileHaarMeasure : Measure ℝ :=
  Measure.map thetaSource.cdfFun (volume : Measure ℝ)

theorem measurable_thetaIntegerQuantileFlow (n : ℕ) :
    Measurable (thetaIntegerQuantileFlow n) := by
  unfold thetaIntegerQuantileFlow
  exact thetaSource.continuous_cdfFun.measurable.comp
    (thetaSource.measurable_quantileFun.add measurable_const)

theorem thetaIntegerQuantileFlow_cdfFun
    (n : ℕ) (x : ℝ) :
    thetaIntegerQuantileFlow n (thetaSource.cdfFun x) =
      thetaSource.cdfFun (x + Real.log n) := by
  rw [thetaIntegerQuantileFlow, thetaSource.quantile_cdfFun]

theorem map_thetaIntegerQuantileFlow_thetaQuantileHaarMeasure
    (n : ℕ) :
    Measure.map (thetaIntegerQuantileFlow n) thetaQuantileHaarMeasure =
      thetaQuantileHaarMeasure := by
  rw [thetaQuantileHaarMeasure, Measure.map_map
    (measurable_thetaIntegerQuantileFlow n)
    thetaSource.continuous_cdfFun.measurable]
  have hfun : (thetaIntegerQuantileFlow n ∘ thetaSource.cdfFun) =
      thetaSource.cdfFun ∘ fun x : ℝ => x + Real.log n := by
    funext x
    exact thetaIntegerQuantileFlow_cdfFun n x
  have hadd : Measurable (fun x : ℝ => x + Real.log n) := by fun_prop
  rw [hfun, ← Measure.map_map thetaSource.continuous_cdfFun.measurable hadd,
    map_add_right_eq_self]

theorem measurePreserving_thetaIntegerQuantileFlow (n : ℕ) :
    MeasurePreserving (thetaIntegerQuantileFlow n)
      thetaQuantileHaarMeasure thetaQuantileHaarMeasure :=
  ⟨measurable_thetaIntegerQuantileFlow n,
    map_thetaIntegerQuantileFlow_thetaQuantileHaarMeasure n⟩

/-- On every compact subinterval of the probability coordinate, transported Haar mass is exactly
quantile length.  This is the interval form of `dν_theta = q(t) dt`. -/
theorem thetaQuantileHaarMeasure_Icc {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    thetaQuantileHaarMeasure (Icc a b) =
      ENNReal.ofReal (thetaSource.quantileFun b - thetaSource.quantileFun a) := by
  rw [thetaQuantileHaarMeasure,
    Measure.map_apply_of_aemeasurable
      thetaSource.continuous_cdfFun.aemeasurable measurableSet_Icc]
  have hpre : thetaSource.cdfFun ⁻¹' Icc a b =
      Icc (thetaSource.quantileFun a) (thetaSource.quantileFun b) := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor
    · rintro ⟨hax, hxb⟩
      constructor
      · exact (thetaSource.strictMono_cdfFun.le_iff_le.mp
          (by simpa [thetaSource.cdfFun_quantile ha] using hax))
      · exact (thetaSource.strictMono_cdfFun.le_iff_le.mp
          (by simpa [thetaSource.cdfFun_quantile hb] using hxb))
    · rintro ⟨hax, hxb⟩
      constructor
      · have h := thetaSource.strictMono_cdfFun.monotone hax
        simpa [thetaSource.cdfFun_quantile ha] using h
      · have h := thetaSource.strictMono_cdfFun.monotone hxb
        simpa [thetaSource.cdfFun_quantile hb] using h
  rw [hpre, Real.volume_Icc]

theorem thetaQuantileHaarMeasure_compl_Ioo :
    thetaQuantileHaarMeasure (Ioo (0 : ℝ) 1)ᶜ = 0 := by
  rw [thetaQuantileHaarMeasure,
    Measure.map_apply_of_aemeasurable
      thetaSource.continuous_cdfFun.aemeasurable measurableSet_Ioo.compl]
  have hpre : thetaSource.cdfFun ⁻¹' (Ioo (0 : ℝ) 1)ᶜ = ∅ := by
    ext x
    simp only [mem_preimage, mem_compl_iff, mem_Ioo, not_and_or, not_lt, mem_empty_iff_false]
    constructor
    · exact (not_or_intro (not_le_of_gt (thetaSource.cdfFun_mem_Ioo x).1)
        (not_le_of_gt (thetaSource.cdfFun_mem_Ioo x).2))
    · intro h
      contradiction
  rw [hpre, measure_empty]

theorem thetaQuantileHaarMeasure_Ioo :
    thetaQuantileHaarMeasure (Ioo (0 : ℝ) 1) = ⊤ := by
  rw [thetaQuantileHaarMeasure,
    Measure.map_apply_of_aemeasurable
      thetaSource.continuous_cdfFun.aemeasurable measurableSet_Ioo]
  have hpre : thetaSource.cdfFun ⁻¹' Ioo (0 : ℝ) 1 = Set.univ := by
    ext x
    simp only [mem_preimage, mem_Ioo, mem_univ, iff_true]
    exact thetaSource.cdfFun_mem_Ioo x
  rw [hpre]
  simp

/-- No nonzero finite measure supported on the quantile interval can be invariant under one
genuine integer prime flow.  The bounded coordinate `t` is a strict Lyapunov function, whereas
invariance would preserve its integral. -/
theorem finiteMeasure_eq_zero_of_map_thetaIntegerQuantileFlow_eq_self
    (μ : Measure ℝ) [IsFiniteMeasure μ] {n : ℕ} (hn : 1 < n)
    (hsupp : μ (Ioo (0 : ℝ) 1)ᶜ = 0)
    (hinv : Measure.map (thetaIntegerQuantileFlow n) μ = μ) :
    μ = 0 := by
  have hae : ∀ᵐ t ∂μ, t ∈ Ioo (0 : ℝ) 1 := mem_ae_iff.mpr hsupp
  have hid : Integrable (fun t : ℝ => t) μ := by
    refine Integrable.mono' (integrable_const (μ := μ) (1 : ℝ))
      continuous_id.aestronglyMeasurable ?_
    filter_upwards [hae] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg ht.1.le]
    exact ht.2.le
  have hflow : Integrable (thetaIntegerQuantileFlow n) μ := by
    refine Integrable.mono' (integrable_const (μ := μ) (1 : ℝ))
      (measurable_thetaIntegerQuantileFlow n).aestronglyMeasurable ?_
    filter_upwards with t
    have ht := thetaIntegerQuantileFlow_mem_Ioo n t
    rw [Real.norm_eq_abs, abs_of_nonneg ht.1.le]
    exact ht.2.le
  have hintegral :
      (∫ t, thetaIntegerQuantileFlow n t ∂μ) = ∫ t, t ∂μ := by
    calc
      (∫ t, thetaIntegerQuantileFlow n t ∂μ) =
          ∫ t, t ∂Measure.map (thetaIntegerQuantileFlow n) μ := by
        symm
        exact integral_map (measurable_thetaIntegerQuantileFlow n).aemeasurable
          continuous_id.aestronglyMeasurable
      _ = ∫ t, t ∂μ := by rw [hinv]
  have hdiff_nonneg :
      0 ≤ᵐ[μ] fun t => thetaIntegerQuantileFlow n t - t := by
    filter_upwards [hae] with t ht
    exact sub_nonneg.mpr (thetaIntegerQuantileFlow_gt hn ht).le
  have hdiff_int : Integrable
      (fun t => thetaIntegerQuantileFlow n t - t) μ := hflow.sub hid
  have hdiff_zero :
      (∫ t, thetaIntegerQuantileFlow n t - t ∂μ) = 0 := by
    rw [integral_sub hflow hid, hintegral, sub_self]
  have hdiff_ae_zero :
      (fun t => thetaIntegerQuantileFlow n t - t) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hdiff_nonneg hdiff_int).mp hdiff_zero
  have hfalse : ∀ᵐ _t ∂μ, False := by
    filter_upwards [hae, hdiff_ae_zero] with t ht hzero
    have hpos := sub_pos.mpr (thetaIntegerQuantileFlow_gt hn ht)
    exact (ne_of_gt hpos) hzero
  rw [ae_iff] at hfalse
  have huniv : μ Set.univ = 0 := by simpa using hfalse
  exact Measure.measure_univ_eq_zero.mp huniv

end HedenmalmThetaSource
end
end RHTower
