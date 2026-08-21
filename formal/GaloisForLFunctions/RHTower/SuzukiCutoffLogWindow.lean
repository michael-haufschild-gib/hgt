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
      HasDerivAt (fun v : ℝ => -(c + Real.log v) * v⁻¹)
        ((Real.log (3 + R) + Real.log z - Real.log R) / z ^ 2) z := by
    intro z hz
    have hz0 : 0 < z := lt_trans hR hz
    have hlog : HasDerivAt (fun v : ℝ => c + Real.log v) z⁻¹ z := by
      simpa using (Real.hasDerivAt_log (ne_of_gt hz0)).const_add c
    have hinv : HasDerivAt (fun v : ℝ => v⁻¹) (-(z ^ 2)⁻¹) z := by
      simpa using hasDerivAt_inv (ne_of_gt hz0)
    have hmul := (hlog.neg).mul hinv
    refine hmul.congr_deriv ?_
    field_simp [hc]
    ring
  have hcont : ContinuousWithinAt (fun v : ℝ => -(c + Real.log v) * v⁻¹) (Ici R) R := by
    have h1 : ContinuousAt (fun v : ℝ => -(c + Real.log v)) R := by
      exact (ContinuousAt.add continuousAt_const (Real.continuousAt_log (ne_of_gt hR))).neg
    have h2 : ContinuousAt (fun v : ℝ => v⁻¹) R := continuousAt_inv₀ (ne_of_gt hR)
    exact (h1.mul h2).continuousWithinAt
  have hint : IntegrableOn
      (fun z : ℝ => (Real.log (3 + R) + Real.log z - Real.log R) / z ^ 2) (Ioi R) volume := by
    have hmeas : AEStronglyMeasurable
        (fun z : ℝ => (Real.log (3 + R) + Real.log z - Real.log R) / z ^ 2)
        (volume.restrict (Ioi R)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro z hz
      have hz0 : 0 < z := lt_trans hR hz
      refine ContinuousAt.continuousWithinAt ?_
      exact ContinuousAt.div
        (by exact ((continuousAt_const.add (Real.continuousAt_log (ne_of_gt hz0))).sub
          continuousAt_const))
        (by fun_prop) (by positivity)
    have hmono : Monotone (fun _ : ℝ => (0 : ℝ)) := monotone_const
    refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg (f := fun v : ℝ =>
      -(c + Real.log v) * v⁻¹) (g := fun z : ℝ =>
      (Real.log (3 + R) + Real.log z - Real.log R) / z ^ 2) ?_ ?_ ?_ ?_
    · exact hcont
    · intro z hz
      exact hderiv z hz
    · intro z hz
      have hz0 : 0 < z := lt_trans hR hz
      have := log_add_three_le hR (le_of_lt hz)
      have hlogpos : (0 : ℝ) ≤ Real.log (3 + R) + Real.log z - Real.log R := by
        have hlz : Real.log R ≤ Real.log z := Real.log_le_log hR (le_of_lt hz)
        have : (0 : ℝ) ≤ Real.log (3 + R) := Real.log_nonneg (by linarith)
        linarith
      positivity
    · have hlog : Tendsto (fun v : ℝ => (c + Real.log v) / v) atTop (nhds 0) := by
        have hbase : Tendsto (fun v : ℝ => Real.log v / v) atTop (nhds 0) := by
          simpa [Function.comp_def] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
        have hconst : Tendsto (fun v : ℝ => c / v) atTop (nhds 0) :=
          Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
        have := hconst.add hbase
        simpa [add_div] using this
      have := hlog.neg
      simpa [div_eq_mul_inv] using this
  have htend : Tendsto (fun v : ℝ => -(c + Real.log v) * v⁻¹) atTop (nhds 0) := by
    have hlog : Tendsto (fun v : ℝ => (c + Real.log v) / v) atTop (nhds 0) := by
      have hbase : Tendsto (fun v : ℝ => Real.log v / v) atTop (nhds 0) := by
        simpa [Function.comp_def] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
      have hconst : Tendsto (fun v : ℝ => c / v) atTop (nhds 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
      have := hconst.add hbase
      simpa [add_div] using this
    have := hlog.neg
    simpa [div_eq_mul_inv] using this
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

end RHTower
