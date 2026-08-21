import GaloisForLFunctions.RHTower.SuzukiApertureFourierDecay
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The logarithmic frequency window of a small boundary cut-off

A boundary cut-off supported on two intervals of total length `2ε` obeys the two Fourier bounds

* `|ŵ(z)| ≤ 2ε` (total mass), and
* `|ŵ(z)| ≤ M/|z|` with `M` independent of `ε` (integration by parts).

Splitting the frequency line at `|z| = 1/ε` and using the first bound below the split, the second
above it, the logarithmic window integral obeys

`∫ log(3 + |z|) |ŵ(z)|² dz ≤ 8 ε log(3 + 1/ε) + 2M² ε (log(3 + 1/ε) + 1)`,

which tends to `0` with `ε`.  This is the estimate that makes the smooth interior functions dense
in the form domain of a localized Weil quadratic form.

The tail estimate rests on the closed evaluation

`∫_R^∞ ( log(3+R) + log z - log R ) / z² dz = ( log(3+R) + 1 ) / R`,

whose integrand dominates `log(3+z)/z²` because `3 + z ≤ (3+R)·z/R` for `z ≥ R > 0`.
-/

open MeasureTheory Set Filter Real

noncomputable section

namespace RHTower

/-! ## The frequency tail -/

theorem log_add_three_le {R z : ℝ} (hR : 0 < R) (hz : R ≤ z) :
    Real.log (3 + z) ≤ Real.log (3 + R) + Real.log z - Real.log R := by
  have hz0 : 0 < z := lt_of_lt_of_le hR hz
  have hprod : 3 + z ≤ (3 + R) * z / R := by
    rw [le_div_iff₀ hR]
    nlinarith
  have h1 : Real.log (3 + z) ≤ Real.log ((3 + R) * z / R) :=
    Real.log_le_log (by linarith) hprod
  have h2 : Real.log ((3 + R) * z / R)
      = Real.log (3 + R) + Real.log z - Real.log R := by
    rw [Real.log_div (by positivity) (ne_of_gt hR), Real.log_mul (by positivity) (ne_of_gt hz0)]
  linarith [h1, h2.le, h2.ge]

/-- The closed evaluation of the dominating tail integral. -/
theorem integral_logMajorant_Ioi {R : ℝ} (hR : 0 < R) :
    (∫ z in Ioi R, (Real.log (3 + R) + Real.log z - Real.log R) / z ^ 2)
      = (Real.log (3 + R) + 1) / R := by
  set c : ℝ := Real.log (3 + R) - Real.log R + 1 with hc
  have hderiv : ∀ z ∈ Ioi R,
      HasDerivAt (fun v : ℝ => -((c + Real.log v) * v⁻¹))
        ((Real.log (3 + R) + Real.log z - Real.log R) / z ^ 2) z := by
    intro z hz
    have hz0 : 0 < z := lt_trans hR hz
    have hlog : HasDerivAt (fun v : ℝ => c + Real.log v) z⁻¹ z := by
      simpa using (Real.hasDerivAt_log (ne_of_gt hz0)).const_add c
    have hinv : HasDerivAt (fun v : ℝ => v⁻¹) (-(z ^ 2)⁻¹) z := by
      simpa using hasDerivAt_inv (ne_of_gt hz0)
    have hmul := (hlog.mul hinv).neg
    refine hmul.congr_deriv ?_
    field_simp [hc]
    ring
  have hcont : ContinuousWithinAt (fun v : ℝ => -((c + Real.log v) * v⁻¹)) (Ici R) R := by
    have h1 : ContinuousAt (fun v : ℝ => c + Real.log v) R :=
      continuousAt_const.add (Real.continuousAt_log (ne_of_gt hR))
    have h2 : ContinuousAt (fun v : ℝ => v⁻¹) R := continuousAt_inv₀ (ne_of_gt hR)
    exact ((h1.mul h2).neg).continuousWithinAt
  have htend : Tendsto (fun v : ℝ => -((c + Real.log v) * v⁻¹)) atTop (nhds 0) := by
    have hlog : Tendsto (fun v : ℝ => (c + Real.log v) / v) atTop (nhds 0) := by
      have hbase : Tendsto (fun v : ℝ => Real.log v / v) atTop (nhds 0) := by
        simpa [Function.comp_def] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
      have hconst : Tendsto (fun v : ℝ => c / v) atTop (nhds 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
      have := hconst.add hbase
      simpa [add_div] using this
    have := hlog.neg
    simpa [div_eq_mul_inv] using this
  have hpos : ∀ z ∈ Ioi R,
      (0 : ℝ) ≤ (Real.log (3 + R) + Real.log z - Real.log R) / z ^ 2 := by
    intro z hz
    have hz0 : 0 < z := lt_trans hR hz
    have hlz : Real.log R ≤ Real.log z := Real.log_le_log hR (le_of_lt hz)
    have h3 : (0 : ℝ) ≤ Real.log (3 + R) := Real.log_nonneg (by linarith)
    have hnum : (0 : ℝ) ≤ Real.log (3 + R) + Real.log z - Real.log R := by linarith
    positivity
  have hint : IntegrableOn
      (fun z : ℝ => (Real.log (3 + R) + Real.log z - Real.log R) / z ^ 2) (Ioi R) volume :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos htend
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend
  rw [h]
  field_simp [hc]
  ring

/-! ## The window bound tends to zero -/

/-- `ε · log(3 + 1/ε) → 0` as `ε → 0+`. -/
theorem tendsto_mul_log_window : Tendsto (fun ε : ℝ => ε * Real.log (3 + 1 / ε))
    (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hu : Tendsto (fun ε : ℝ => ε⁻¹) (nhdsWithin (0 : ℝ) (Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hlog : Tendsto (fun u : ℝ => Real.log (3 + u) / u) atTop (nhds 0) := by
    have hbase : Tendsto (fun v : ℝ => Real.log v / v) atTop (nhds 0) := by
      simpa [Function.comp_def] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have hshift : Tendsto (fun u : ℝ => Real.log (3 + u) / (3 + u)) atTop (nhds 0) :=
      hbase.comp (tendsto_atTop_add_const_left _ 3 tendsto_id)
    have hratio : Tendsto (fun u : ℝ => (3 + u) / u) atTop (nhds 1) := by
      have h1 : Tendsto (fun u : ℝ => 1 + 3 / u) atTop (nhds 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ))).add
          (Filter.Tendsto.div_atTop (tendsto_const_nhds (x := (3 : ℝ))) tendsto_id)
        simpa using this
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      field_simp
      ring
    have := hshift.mul hratio
    simp only [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have h3 : (3 : ℝ) + u ≠ 0 := by linarith
    field_simp
  have hcomp := hlog.comp hu
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  simp only [Function.comp_apply, one_div]
  field_simp


/-! ## The two displayed window estimates -/

theorem integrableOn_logMajorant {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun z : ℝ => (Real.log (3 + R) + Real.log z - Real.log R) / z ^ 2)
      (Ioi R) volume := by
  have hcont : ContinuousWithinAt
      (fun v : ℝ => -((Real.log (3 + R) - Real.log R + 1 + Real.log v) * v⁻¹)) (Ici R) R := by
    have h1 : ContinuousAt
        (fun v : ℝ => Real.log (3 + R) - Real.log R + 1 + Real.log v) R :=
      continuousAt_const.add (Real.continuousAt_log (ne_of_gt hR))
    have h2 : ContinuousAt (fun v : ℝ => v⁻¹) R := continuousAt_inv₀ (ne_of_gt hR)
    exact ((h1.mul h2).neg).continuousWithinAt
  have hderiv : ∀ z ∈ Ioi R,
      HasDerivAt (fun v : ℝ =>
          -((Real.log (3 + R) - Real.log R + 1 + Real.log v) * v⁻¹))
        ((Real.log (3 + R) + Real.log z - Real.log R) / z ^ 2) z := by
    intro z hz
    have hz0 : 0 < z := lt_trans hR hz
    have hlog : HasDerivAt
        (fun v : ℝ => Real.log (3 + R) - Real.log R + 1 + Real.log v) z⁻¹ z := by
      simpa using (Real.hasDerivAt_log (ne_of_gt hz0)).const_add
        (Real.log (3 + R) - Real.log R + 1)
    have hinv : HasDerivAt (fun v : ℝ => v⁻¹) (-(z ^ 2)⁻¹) z := by
      simpa using hasDerivAt_inv (ne_of_gt hz0)
    refine ((hlog.mul hinv).neg).congr_deriv ?_
    field_simp
    ring
  have hpos : ∀ z ∈ Ioi R,
      (0 : ℝ) ≤ (Real.log (3 + R) + Real.log z - Real.log R) / z ^ 2 := by
    intro z hz
    have hz0 : 0 < z := lt_trans hR hz
    have hlz : Real.log R ≤ Real.log z := Real.log_le_log hR (le_of_lt hz)
    have h3 : (0 : ℝ) ≤ Real.log (3 + R) := Real.log_nonneg (by linarith)
    have hnum : (0 : ℝ) ≤ Real.log (3 + R) + Real.log z - Real.log R := by linarith
    positivity
  have htend : Tendsto
      (fun v : ℝ => -((Real.log (3 + R) - Real.log R + 1 + Real.log v) * v⁻¹))
      atTop (nhds 0) := by
    have hlog : Tendsto
        (fun v : ℝ => (Real.log (3 + R) - Real.log R + 1 + Real.log v) / v)
        atTop (nhds 0) := by
      have hbase : Tendsto (fun v : ℝ => Real.log v / v) atTop (nhds 0) := by
        simpa [Function.comp_def] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
      have hconst : Tendsto
          (fun v : ℝ => (Real.log (3 + R) - Real.log R + 1) / v) atTop (nhds 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
      have := hconst.add hbase
      simpa [add_div] using this
    have := hlog.neg
    simpa [div_eq_mul_inv] using this
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos htend

theorem continuous_logWindowWeight : Continuous fun z : ℝ => Real.log (3 + |z|) := by
  have h : Continuous fun z : ℝ => 3 + |z| := by fun_prop
  exact h.log (fun z => by positivity)

theorem integrableOn_logWindow_tail {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun z : ℝ => Real.log (3 + z) / z ^ 2) (Ioi R) volume := by
  have hmeas : AEStronglyMeasurable (fun z : ℝ => Real.log (3 + z) / z ^ 2)
      (volume.restrict (Ioi R)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro z hz
    have hz0 : 0 < z := lt_trans hR hz
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.div ?_ (by fun_prop) (by positivity)
    exact (Real.continuousAt_log (by linarith)).comp (by fun_prop)
  refine (integrableOn_logMajorant hR).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hz0 : 0 < z := lt_trans hR hz
  have h3 : (0 : ℝ) ≤ Real.log (3 + z) := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := log_add_three_le hR (le_of_lt hz)
  gcongr

/-- The frequency-tail estimate: `∫_R^∞ log(3+z)/z² dz ≤ (log(3+R) + 1)/R`. -/
theorem integral_logWindow_tail_le {R : ℝ} (hR : 0 < R) :
    (∫ z in Ioi R, Real.log (3 + z) / z ^ 2) ≤ (Real.log (3 + R) + 1) / R := by
  have hmono : (∫ z in Ioi R, Real.log (3 + z) / z ^ 2)
      ≤ ∫ z in Ioi R, (Real.log (3 + R) + Real.log z - Real.log R) / z ^ 2 := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ (integrableOn_logMajorant hR) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      have hz0 : 0 < z := lt_trans hR hz
      have h3 : (0 : ℝ) ≤ Real.log (3 + z) := Real.log_nonneg (by linarith)
      positivity
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      have hz0 : 0 < z := lt_trans hR hz
      have := log_add_three_le hR (le_of_lt hz)
      gcongr
  rw [integral_logMajorant_Ioi hR] at hmono
  exact hmono

/-- The low-frequency estimate: the logarithmic weight on `[-R,R]` has total mass at most
`2R log(3+R)`. -/
theorem integral_logWindow_head_le {R : ℝ} (hR : 0 ≤ R) :
    (∫ z in (-R)..R, Real.log (3 + |z|)) ≤ 2 * R * Real.log (3 + R) := by
  have hle : -R ≤ R := by linarith
  have hbound : ∀ z ∈ Set.Icc (-R) R, Real.log (3 + |z|) ≤ Real.log (3 + R) := by
    intro z hz
    have habs : |z| ≤ R := abs_le.mpr ⟨hz.1, hz.2⟩
    exact Real.log_le_log (by positivity) (by linarith)
  have hmono := intervalIntegral.integral_mono_on hle
    (continuous_logWindowWeight.intervalIntegrable (μ := volume) _ _)
    (Continuous.intervalIntegrable (by fun_prop : Continuous fun _ : ℝ => Real.log (3 + R)) _ _)
    hbound
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  have : (R - -R) * Real.log (3 + R) = 2 * R * Real.log (3 + R) := by ring
  linarith [hmono, this.le, this.ge]

/-! ## The assembled bound tends to zero -/

/-- The bound produced by the two window estimates at scale `ε`. -/
def cutoffLogWindowBound (M ε : ℝ) : ℝ :=
  8 * ε * Real.log (3 + 1 / ε) + 2 * M ^ 2 * (ε * Real.log (3 + 1 / ε) + ε)

theorem tendsto_cutoffLogWindowBound (M : ℝ) :
    Tendsto (cutoffLogWindowBound M) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have h1 : Tendsto (fun ε : ℝ => 8 * (ε * Real.log (3 + 1 / ε)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using tendsto_mul_log_window.const_mul (8 : ℝ)
  have hid : Tendsto (fun ε : ℝ => ε) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun ε : ℝ => 2 * M ^ 2 * (ε * Real.log (3 + 1 / ε) + ε))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have := (tendsto_mul_log_window.add hid).const_mul (2 * M ^ 2)
    simpa using this
  have hadd := h1.add h2
  rw [add_zero] at hadd
  refine hadd.congr ?_
  intro ε
  rw [cutoffLogWindowBound]
  ring


/-! ## The two-sided tail -/

theorem setIntegral_Iic_neg_eq_Ioi_of_even {g : ℝ → ℝ} (hg : ∀ z, g (-z) = g z) (R : ℝ) :
    (∫ z in Iic (-R), g z) = ∫ z in Ioi R, g z := by
  have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
  have h := hmp.setIntegral_preimage_emb (Homeomorph.neg ℝ).measurableEmbedding g (Ioi R)
  have hpre : (fun x : ℝ => -x) ⁻¹' (Ioi R) = Iio (-R) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · intro hx; linarith
    · intro hx; linarith
  have hIio : (∫ z in Iio (-R), g z) = ∫ z in Iic (-R), g z := by
    rw [← MeasureTheory.integral_Iic_eq_integral_Iio]
  rw [hpre] at h
  simp only [hg] at h
  rw [← hIio, h]

theorem logWindowMajorant_even (M : ℝ) (z : ℝ) :
    Real.log (3 + |(-z)|) * (M / |(-z)|) ^ 2 = Real.log (3 + |z|) * (M / |z|) ^ 2 := by
  rw [abs_neg]

/-! ## The assembled window bound -/

/-- **The logarithmic window estimate.**  A frequency profile obeying the total-mass bound `2ε`
and the integration-by-parts bound `M/|z|` has logarithmic window integral at most
`8 ε log(3 + 1/ε) + 2M² (ε log(3 + 1/ε) + ε)`, which tends to `0` with `ε`. -/
theorem integral_logWindow_le {ε M : ℝ} (hε : 0 < ε) {w : ℝ → ℂ}
    (hw1 : ∀ z, ‖w z‖ ≤ 2 * ε)
    (hw2 : ∀ z, z ≠ 0 → ‖w z‖ ≤ M / |z|)
    (hint : Integrable (fun z : ℝ => Real.log (3 + |z|) * ‖w z‖ ^ 2) volume) :
    (∫ z : ℝ, Real.log (3 + |z|) * ‖w z‖ ^ 2) ≤ cutoffLogWindowBound M ε := by
  set R : ℝ := 1 / ε with hR_def
  have hR : 0 < R := by rw [hR_def]; positivity
  have hRε : R * ε = 1 := by rw [hR_def]; field_simp
  set f : ℝ → ℝ := fun z => Real.log (3 + |z|) * ‖w z‖ ^ 2 with hf
  have hfnonneg : ∀ z : ℝ, 0 ≤ f z := by
    intro z
    have h3 : (0 : ℝ) ≤ Real.log (3 + |z|) := Real.log_nonneg (by linarith [abs_nonneg z])
    have hfz : f z = Real.log (3 + |z|) * ‖w z‖ ^ 2 := rfl
    rw [hfz]
    positivity
  -- the tail majorant
  have hmajI : IntegrableOn (fun z : ℝ => M ^ 2 * (Real.log (3 + z) / z ^ 2)) (Ioi R) volume :=
    (integrableOn_logWindow_tail hR).const_mul _
  have htailR : (∫ z in Ioi R, f z) ≤ M ^ 2 * ((Real.log (3 + R) + 1) / R) := by
    have hmono : (∫ z in Ioi R, f z)
        ≤ ∫ z in Ioi R, M ^ 2 * (Real.log (3 + z) / z ^ 2) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ hmajI ?_
      · filter_upwards with z using hfnonneg z
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
        have hz0 : 0 < z := lt_trans hR hz
        have habs : |z| = z := abs_of_pos hz0
        have hbd : ‖w z‖ ≤ M / z := by
          have := hw2 z (ne_of_gt hz0)
          rwa [habs] at this
        have hnn : (0 : ℝ) ≤ ‖w z‖ := norm_nonneg _
        have hsq : ‖w z‖ ^ 2 ≤ (M / z) ^ 2 := pow_le_pow_left₀ hnn hbd 2
        have h3 : (0 : ℝ) ≤ Real.log (3 + z) := Real.log_nonneg (by linarith)
        have hfz : f z = Real.log (3 + |z|) * ‖w z‖ ^ 2 := rfl
        rw [hfz, habs]
        calc Real.log (3 + z) * ‖w z‖ ^ 2 ≤ Real.log (3 + z) * (M / z) ^ 2 := by
              exact mul_le_mul_of_nonneg_left hsq h3
          _ = M ^ 2 * (Real.log (3 + z) / z ^ 2) := by
              rw [div_pow]; ring
    have hscale : (∫ z in Ioi R, M ^ 2 * (Real.log (3 + z) / z ^ 2))
        = M ^ 2 * ∫ z in Ioi R, Real.log (3 + z) / z ^ 2 :=
      MeasureTheory.integral_const_mul _ _
    rw [hscale] at hmono
    refine hmono.trans ?_
    have := integral_logWindow_tail_le hR
    nlinarith [sq_nonneg M]
  -- the reflected tail
  have htailL : (∫ z in Iic (-R), f z) ≤ M ^ 2 * ((Real.log (3 + R) + 1) / R) := by
    have hmajEven : IntegrableOn
        (fun z : ℝ => Real.log (3 + |z|) * (M / |z|) ^ 2) (Iic (-R)) volume := by
      have hrefl : (fun z : ℝ => Real.log (3 + |z|) * (M / |z|) ^ 2)
          = fun z : ℝ => Real.log (3 + |z|) * (M / |z|) ^ 2 := rfl
      have hcongr : ∀ z ∈ Ioi R,
          Real.log (3 + |z|) * (M / |z|) ^ 2 = M ^ 2 * (Real.log (3 + z) / z ^ 2) := by
        intro z hz
        have hz0 : 0 < z := lt_trans hR hz
        rw [abs_of_pos hz0, div_pow]
        ring
      have hIoi : IntegrableOn (fun z : ℝ => Real.log (3 + |z|) * (M / |z|) ^ 2)
          (Ioi R) volume := by
        refine hmajI.congr_fun (fun z hz => (hcongr z hz).symm) measurableSet_Ioi
      have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
      have h := (hmp.integrableOn_comp_preimage (Homeomorph.neg ℝ).measurableEmbedding
        (f := fun z : ℝ => Real.log (3 + |z|) * (M / |z|) ^ 2) (s := Ioi R)).2 hIoi
      have hpre : (fun x : ℝ => -x) ⁻¹' (Ioi R) = Iio (-R) := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]
        constructor
        · intro hx; linarith
        · intro hx; linarith
      rw [hpre] at h
      simp only [Function.comp_def, abs_neg] at h
      have hIic : Iic (-R) =ᵐ[volume] Iio (-R) := (Iio_ae_eq_Iic (a := -R)).symm
      exact h.congr_set_ae hIic
    have hmono : (∫ z in Iic (-R), f z)
        ≤ ∫ z in Iic (-R), Real.log (3 + |z|) * (M / |z|) ^ 2 := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ hmajEven ?_
      · filter_upwards with z using hfnonneg z
      · filter_upwards [ae_restrict_mem measurableSet_Iic] with z hz
        have hz0 : z < 0 := lt_of_le_of_lt hz (by linarith)
        have hzne : z ≠ 0 := ne_of_lt hz0
        have hbd := hw2 z hzne
        have hnn : (0 : ℝ) ≤ ‖w z‖ := norm_nonneg _
        have hsq : ‖w z‖ ^ 2 ≤ (M / |z|) ^ 2 := pow_le_pow_left₀ hnn hbd 2
        have h3 : (0 : ℝ) ≤ Real.log (3 + |z|) := Real.log_nonneg (by linarith [abs_nonneg z])
        have hfz : f z = Real.log (3 + |z|) * ‖w z‖ ^ 2 := rfl
        rw [hfz]
        exact mul_le_mul_of_nonneg_left hsq h3
    have heq : (∫ z in Iic (-R), Real.log (3 + |z|) * (M / |z|) ^ 2)
        = ∫ z in Ioi R, Real.log (3 + |z|) * (M / |z|) ^ 2 :=
      setIntegral_Iic_neg_eq_Ioi_of_even (fun z => logWindowMajorant_even M z) R
    have hval : (∫ z in Ioi R, Real.log (3 + |z|) * (M / |z|) ^ 2)
        = M ^ 2 * ∫ z in Ioi R, Real.log (3 + z) / z ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro z hz
      have hz0 : 0 < z := lt_trans hR hz
      dsimp only
      rw [abs_of_pos hz0, div_pow]
      ring
    rw [heq, hval] at hmono
    refine hmono.trans ?_
    have := integral_logWindow_tail_le hR
    nlinarith [sq_nonneg M]
  -- the low-frequency block
  have hmid : (∫ z in Ioc (-R) R, f z) ≤ 4 * ε ^ 2 * (2 * R * Real.log (3 + R)) := by
    have hconst : IntegrableOn (fun _ : ℝ => Real.log (3 + R) * (2 * ε) ^ 2)
        (Ioc (-R) R) volume := continuous_const.integrableOn_Ioc
    have hmono : (∫ z in Ioc (-R) R, f z)
        ≤ ∫ _ in Ioc (-R) R, Real.log (3 + R) * (2 * ε) ^ 2 := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ hconst ?_
      · filter_upwards with z using hfnonneg z
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
        have habs : |z| ≤ R := abs_le.mpr ⟨le_of_lt hz.1, hz.2⟩
        have hlog : Real.log (3 + |z|) ≤ Real.log (3 + R) :=
          Real.log_le_log (by positivity) (by linarith)
        have hnn : (0 : ℝ) ≤ ‖w z‖ := norm_nonneg _
        have hsq : ‖w z‖ ^ 2 ≤ (2 * ε) ^ 2 := pow_le_pow_left₀ hnn (hw1 z) 2
        have h3 : (0 : ℝ) ≤ Real.log (3 + |z|) := Real.log_nonneg (by linarith [abs_nonneg z])
        have hfz : f z = Real.log (3 + |z|) * ‖w z‖ ^ 2 := rfl
        rw [hfz]
        calc Real.log (3 + |z|) * ‖w z‖ ^ 2 ≤ Real.log (3 + |z|) * (2 * ε) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq h3
          _ ≤ Real.log (3 + R) * (2 * ε) ^ 2 := by
              have : (0 : ℝ) ≤ (2 * ε) ^ 2 := by positivity
              exact mul_le_mul_of_nonneg_right hlog this
    have hvol : (∫ _ in Ioc (-R) R, Real.log (3 + R) * (2 * ε) ^ 2)
        = (2 * R) * (Real.log (3 + R) * (2 * ε) ^ 2) := by
      rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith)]
      simp only [smul_eq_mul]
      ring
    rw [hvol] at hmono
    refine hmono.trans (le_of_eq ?_)
    ring
  -- assemble
  have hIoiInt : IntegrableOn f (Ioi R) volume := hint.integrableOn
  have hIicInt : IntegrableOn f (Iic (-R)) volume := hint.integrableOn
  have hIocInt : IntegrableOn f (Ioc (-R) R) volume := hint.integrableOn
  have hdisj1 : Disjoint (Ioc (-R) R) (Ioi R) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx' (not_lt.mpr hx.2)
  have hunion1 := MeasureTheory.setIntegral_union (μ := volume) (f := f)
    hdisj1 measurableSet_Ioi hIocInt hIoiInt
  rw [Set.Ioc_union_Ioi_eq_Ioi (by linarith : -R ≤ R)] at hunion1
  have hdisj2 : Disjoint (Iic (-R)) (Ioi (-R)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : x ≤ -R := hx
    have h2 : -R < x := hx'
    linarith
  have hIoiNeg : IntegrableOn f (Ioi (-R)) volume := hint.integrableOn
  have hunion2 := MeasureTheory.setIntegral_union (μ := volume) (f := f)
    hdisj2 measurableSet_Ioi hIicInt hIoiNeg
  rw [Set.Iic_union_Ioi, MeasureTheory.setIntegral_univ] at hunion2
  rw [hunion2, hunion1, cutoffLogWindowBound]
  have hlog : Real.log (3 + R) = Real.log (3 + 1 / ε) := by rw [hR_def]
  have hRinv : (Real.log (3 + R) + 1) / R = ε * Real.log (3 + 1 / ε) + ε := by
    rw [hlog, hR_def]
    field_simp
  have hmid' : 4 * ε ^ 2 * (2 * R * Real.log (3 + R)) = 8 * ε * Real.log (3 + 1 / ε) := by
    rw [hlog, hR_def]
    field_simp
    ring
  rw [hRinv] at htailR htailL
  rw [hmid'] at hmid
  linarith

end RHTower
