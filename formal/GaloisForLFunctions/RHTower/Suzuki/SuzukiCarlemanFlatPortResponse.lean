import GaloisForLFunctions.RHTower.Suzuki.SuzukiCarlemanFlatPortChart
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The Carleman response of the flat port

In the logarithmic chart the one-sided cross-boundary Carleman response of the flat profile is

`B(L) = ∫_{v > 1} F(v) / (1 + e^{v-L}) dv`,

whose `L`-derivative is the logistic average `∫ F(v) k(v-L) dv`.  The logistic kernel is a
probability density, so differentiating under the integral sign and passing to the limit gives the
exact derivative rate `B'(L) / F(L) → 1`: the response is as flat as the profile.  Consequently no
positive exponential weight makes the derivative square integrable — Carleman boundedness plus the
endpoint counterterm cannot produce a Gamma strip.
-/

open Set MeasureTheory Filter Topology

namespace RHTower

noncomputable section

/-- The Carleman cutoff factor `(1 + e^{v-L})⁻¹`. -/
def carlemanCutoffFactor (L v : ℝ) : ℝ := (1 + Real.exp (v - L))⁻¹

theorem carlemanCutoffFactor_pos (L v : ℝ) : 0 < carlemanCutoffFactor L v := by
  have := Real.exp_pos (v - L)
  unfold carlemanCutoffFactor
  positivity

theorem carlemanCutoffFactor_le_one (L v : ℝ) : carlemanCutoffFactor L v ≤ 1 := by
  have hpos := Real.exp_pos (v - L)
  unfold carlemanCutoffFactor
  rw [inv_le_one_iff₀]
  right
  linarith

/-- The logistic kernel is at most `1/4`. -/
theorem logisticKernel_le_quarter (y : ℝ) : logisticKernel y ≤ 1 / 4 := by
  have hpos := Real.exp_pos y
  simp only [logisticKernel]
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [sq_nonneg (1 - Real.exp y)]

/-- The `L`-derivative of the cutoff factor is the logistic kernel. -/
theorem hasDerivAt_carlemanCutoffFactor (v L : ℝ) :
    HasDerivAt (fun M : ℝ => carlemanCutoffFactor M v) (logisticKernel (v - L)) L := by
  have hpos : (0:ℝ) < 1 + Real.exp (v - L) := by
    have := Real.exp_pos (v - L)
    linarith
  have hne : (1 + Real.exp (v - L)) ≠ 0 := ne_of_gt hpos
  have hinner : HasDerivAt (fun M : ℝ => v - M) (-1) L := by
    simpa using (hasDerivAt_id L).const_sub v
  have hexp : HasDerivAt (fun M : ℝ => Real.exp (v - M)) (Real.exp (v - L) * (-1)) L := hinner.exp
  have hbase : HasDerivAt (fun M : ℝ => 1 + Real.exp (v - M)) (Real.exp (v - L) * (-1)) L := by
    simpa using hexp.const_add (1:ℝ)
  have hinv : HasDerivAt (fun M : ℝ => (1 + Real.exp (v - M))⁻¹)
      (-(Real.exp (v - L) * (-1)) / (1 + Real.exp (v - L)) ^ (2 : ℕ)) L := hbase.inv hne
  have hval : -(Real.exp (v - L) * (-1)) / (1 + Real.exp (v - L)) ^ (2 : ℕ) = logisticKernel (v - L) := by
    simp only [logisticKernel]
    ring
  have hfun : (fun M : ℝ => carlemanCutoffFactor M v)
      = fun M : ℝ => (1 + Real.exp (v - M))⁻¹ := by
    funext M
    rw [carlemanCutoffFactor]
  rw [hfun, ← hval]
  exact hinv

/-- The Carleman response of the flat profile in the logarithmic chart. -/
def carlemanLogResponse (L : ℝ) : ℝ :=
  ∫ v in Ioi (1:ℝ), flatPortProfile v * carlemanCutoffFactor L v

/-- The endpoint counterterm: the response at infinitely deep cutoff. -/
def carlemanLogResponseLimit : ℝ := ∫ v in Ioi (1:ℝ), flatPortProfile v

theorem integrableOn_flatPortProfile_one :
    IntegrableOn flatPortProfile (Ioi (1:ℝ)) volume :=
  integrableOn_flatPortProfile 1 zero_lt_one

theorem integrableOn_carlemanIntegrand (L : ℝ) :
    IntegrableOn (fun v => flatPortProfile v * carlemanCutoffFactor L v) (Ioi (1:ℝ)) volume := by
  refine Integrable.mono' integrableOn_flatPortProfile_one ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold flatPortProfile carlemanCutoffFactor
    fun_prop
  · filter_upwards [] with v
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (flatPortProfile_pos v).le (carlemanCutoffFactor_pos L v).le)]
    have h1 := carlemanCutoffFactor_le_one L v
    have h2 := (flatPortProfile_pos v).le
    nlinarith [carlemanCutoffFactor_pos L v]

theorem integrableOn_carlemanDerivIntegrand (L : ℝ) :
    IntegrableOn (fun v => flatPortProfile v * logisticKernel (v - L)) (Ioi (1:ℝ)) volume := by
  refine Integrable.mono' (g := fun v => (1/4 : ℝ) * flatPortProfile v)
    (integrableOn_flatPortProfile_one.const_mul (1/4)) ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold flatPortProfile logisticKernel
    fun_prop
  · filter_upwards [] with v
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (flatPortProfile_pos v).le (logisticKernel_pos (v - L)).le)]
    have h1 := logisticKernel_le_quarter (v - L)
    have h2 := (flatPortProfile_pos v).le
    nlinarith [logisticKernel_pos (v - L)]

/-- **`(20)`: the response differentiates to the logistic average of the profile.** -/
theorem hasDerivAt_carlemanLogResponse (L : ℝ) :
    HasDerivAt carlemanLogResponse
      (∫ v in Ioi (1:ℝ), flatPortProfile v * logisticKernel (v - L)) L := by
  have hmeas : ∀ᶠ M in 𝓝 L, AEStronglyMeasurable
      (fun v => flatPortProfile v * carlemanCutoffFactor M v) (volume.restrict (Ioi (1:ℝ))) := by
    filter_upwards with M
    apply Measurable.aestronglyMeasurable
    unfold flatPortProfile carlemanCutoffFactor
    fun_prop
  have hint : IntegrableOn (fun v => flatPortProfile v * carlemanCutoffFactor L v)
      (Ioi (1:ℝ)) volume := integrableOn_carlemanIntegrand L
  have hmeas' : AEStronglyMeasurable (fun v => flatPortProfile v * logisticKernel (v - L))
      (volume.restrict (Ioi (1:ℝ))) := by
    apply Measurable.aestronglyMeasurable
    unfold flatPortProfile logisticKernel
    fun_prop
  have hbound : ∀ᵐ v ∂(volume.restrict (Ioi (1:ℝ))), ∀ M ∈ Metric.ball L 1,
      ‖flatPortProfile v * logisticKernel (v - M)‖ ≤ flatPortProfile v * (1/4) := by
    filter_upwards with v M _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (flatPortProfile_pos v).le (logisticKernel_pos (v - M)).le)]
    have h1 := logisticKernel_le_quarter (v - M)
    have h2 := (flatPortProfile_pos v).le
    nlinarith
  have hboundint : Integrable (fun v => flatPortProfile v * (1/4 : ℝ))
      (volume.restrict (Ioi (1:ℝ))) := by
    simpa [mul_comm] using integrableOn_flatPortProfile_one.const_mul (1/4 : ℝ)
  have hdiff : ∀ᵐ v ∂(volume.restrict (Ioi (1:ℝ))), ∀ M ∈ Metric.ball L 1,
      HasDerivAt (fun M : ℝ => flatPortProfile v * carlemanCutoffFactor M v)
        (flatPortProfile v * logisticKernel (v - M)) M := by
    filter_upwards with v M _
    exact (hasDerivAt_carlemanCutoffFactor v M).const_mul _
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds L one_pos)
    hmeas hint hmeas' hbound hboundint hdiff).2

end

end RHTower
