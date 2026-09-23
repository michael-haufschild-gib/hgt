import GaloisForLFunctions.RHTower.XiSquaredSeamPowerSixtyFourMassCriterion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Power-64 Jensen kernel for the shift-one squared-Xi seam

This module proves the exact radial Tonelli kernel behind the Cassini--Jensen source coordinate.
For a reciprocal seam atom `z`, its inverse radius is `a = ‖z⁻¹‖`.  The elementary identity

`∫_a^∞ log (r/a) / r^(65 : ℕ) dr = 1 / (4096 a^(64 : ℕ))`

turns the summed radial divisor integral into `1/4096` of the Hermitian power-64 mass.  No zero
location, estimate, or numerical computation occurs.  Identifying this doubled divisor profile
with the circle-average profile of the translated even entire source is a separate analytic weld.
-/

open Real MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace RHTower

noncomputable section

theorem integrableOn_log_sub_div_pow_sixtyFive {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ =>
      (Real.log x - Real.log a) / x ^ 65) (Ioi a) := by
  have hpow : IntegrableOn (fun x : ℝ =>
      (1 / a) * x ^ (-64 : ℝ)) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (a := (-64 : ℝ)) (by norm_num) ha).const_mul (1 / a)
  refine hpow.mono' ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := ha.trans hx
    exact (((Real.continuousAt_log hxpos.ne').sub continuousAt_const).div
      (continuousAt_id.pow 65) (pow_ne_zero 65 hxpos.ne')).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := ha.trans hx
    have hlognonneg : 0 ≤ Real.log x - Real.log a :=
      sub_nonneg.mpr (Real.log_le_log ha hx.le)
    have hlogle : Real.log x - Real.log a ≤ x / a := by
      rw [← Real.log_div hxpos.ne' ha.ne']
      have hratio : 0 < x / a := div_pos hxpos ha
      have h := Real.log_le_sub_one_of_pos hratio
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg hlognonneg (pow_nonneg hxpos.le 65))]
    calc
      (Real.log x - Real.log a) / x ^ 65 ≤ (x / a) / x ^ 65 := by
        exact div_le_div_of_nonneg_right hlogle (pow_nonneg hxpos.le 65)
      _ = 1 / a * (x ^ 64)⁻¹ := by
        field_simp [hxpos.ne', ha.ne']
      _ = 1 / a * (x ^ (64 : ℝ))⁻¹ := by
        exact congrArg (fun y : ℝ => 1 / a * y⁻¹) (Real.rpow_natCast x 64).symm
      _ = 1 / a * x ^ (-64 : ℝ) := by
        rw [Real.rpow_neg (le_of_lt hxpos)]

theorem integral_Ioi_log_div_pow_sixtyFive {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ in Ioi a, Real.log (x / a) / x ^ 65 =
      1 / (4096 * a ^ 64) := by
  let F : ℝ → ℝ := fun x =>
    -(1 / 64 : ℝ) * (Real.log x - Real.log a) / x ^ 64 -
      (1 / 4096 : ℝ) / x ^ 64
  have hderiv : ∀ x ∈ Ici a,
      HasDerivAt F ((Real.log x - Real.log a) / x ^ 65) x := by
    intro x hx
    have hxpos : 0 < x := ha.trans_le hx
    dsimp [F]
    have hlog := (Real.hasDerivAt_log hxpos.ne').sub_const (Real.log a)
    have hpow := hasDerivAt_pow 64 x
    have hfirst := (hlog.const_mul (-(1 / 64 : ℝ))).div hpow
      (pow_ne_zero 64 hxpos.ne')
    have hsecond := (hasDerivAt_const x (1 / 4096 : ℝ)).div hpow
      (pow_ne_zero 64 hxpos.ne')
    convert hfirst.sub hsecond using 1
    all_goals first | rfl | field_simp
    all_goals ring_nf
  have hint := integrableOn_log_sub_div_pow_sixtyFive ha
  have htend : Tendsto F atTop (nhds 0) := by
    have hrpow : (fun x : ℝ => x ^ (64 : ℝ)) =ᶠ[atTop]
        fun x => x ^ (64 : ℕ) :=
      Filter.Eventually.of_forall fun x => Real.rpow_natCast x 64
    have hpowtop : Tendsto (fun x : ℝ => x ^ (64 : ℕ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 64)).congr' hrpow
    have hlog : Tendsto (fun x : ℝ =>
        (Real.log x - Real.log a) / x ^ 64) atTop (nhds 0) := by
      have hbaseR :=
        (isLittleO_log_rpow_atTop (r := (64 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
      have hbase : Tendsto (fun x : ℝ =>
          Real.log x / x ^ (64 : ℕ)) atTop (nhds 0) :=
        hbaseR.congr' (Filter.Eventually.of_forall fun x =>
          congrArg (fun y : ℝ => Real.log x / y) (Real.rpow_natCast x 64))
      have hconst : Tendsto (fun x : ℝ =>
          Real.log a / x ^ 64) atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using hpowtop.inv_tendsto_atTop.const_mul (Real.log a)
      simpa [sub_div] using hbase.sub hconst
    have hpowzero : Tendsto (fun x : ℝ => 1 / x ^ 64) atTop (nhds 0) := by
      simp only [one_div]
      exact hpowtop.inv_tendsto_atTop
    have hcomb := (hlog.const_mul (-(1 / 64 : ℝ))).add
      (hpowzero.const_mul (-(1 / 4096 : ℝ)))
    convert hcomb using 1
    · funext x
      dsimp [F]
      ring
    · ring
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  have hrewrite : (∫ x : ℝ in Ioi a, Real.log (x / a) / x ^ 65) =
      ∫ x : ℝ in Ioi a, (Real.log x - Real.log a) / x ^ 65 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.log_div (ha.trans hx).ne' ha.ne']
  rw [hrewrite, hmain]
  dsimp [F]
  simp only [sub_self, mul_zero, zero_div, zero_sub]
  field_simp

/-- Radius of the zero of the translated squared-seam entire source corresponding to one seam
atom, before functional-equation pairs are identified. -/
def xiSquaredSeamInverseRadius (q : XiZeroCopy) : ℝ :=
  ‖(xiSquaredSeamOneCoordinate q)⁻¹‖

theorem xiSquaredSeamOneCoordinate_ne_zero (q : XiZeroCopy) :
    xiSquaredSeamOneCoordinate q ≠ 0 := by
  rw [← xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate]
  exact xiShiftedReciprocalSquare_ne_zero (y := 1) (by norm_num) q

theorem xiSquaredSeamInverseRadius_pos (q : XiZeroCopy) :
    0 < xiSquaredSeamInverseRadius q := by
  rw [xiSquaredSeamInverseRadius, norm_pos_iff]
  exact inv_ne_zero (xiSquaredSeamOneCoordinate_ne_zero q)

/-- The exponent-64 radial Jensen kernel of one multiplicity-exact seam atom. -/
def xiSquaredSeamPowerSixtyFourJensenKernel
    (q : XiZeroCopy) (r : ℝ) : ℝ≥0∞ :=
  if xiSquaredSeamInverseRadius q ≤ r then
    ENNReal.ofReal
      (Real.log (r / xiSquaredSeamInverseRadius q) / r ^ 65)
  else 0

theorem aemeasurable_xiSquaredSeamPowerSixtyFourJensenKernel (q : XiZeroCopy) :
    AEMeasurable (xiSquaredSeamPowerSixtyFourJensenKernel q) := by
  apply Measurable.aemeasurable
  unfold xiSquaredSeamPowerSixtyFourJensenKernel
  apply Measurable.ite (measurableSet_le measurable_const measurable_id)
  · apply ENNReal.measurable_ofReal.comp
    fun_prop
  · exact measurable_const

theorem lintegral_xiSquaredSeamPowerSixtyFourJensenKernel (q : XiZeroCopy) :
    ∫⁻ r : ℝ in Ioi 0, xiSquaredSeamPowerSixtyFourJensenKernel q r =
      ENNReal.ofReal (‖xiSquaredSeamOneCoordinate q ^ 64‖ / 4096) := by
  let a := xiSquaredSeamInverseRadius q
  have ha : 0 < a := xiSquaredSeamInverseRadius_pos q
  let f : ℝ → ℝ := fun r => Real.log (r / a) / r ^ 65
  have hint : IntegrableOn f (Ioi a) := by
    have h := integrableOn_log_sub_div_pow_sixtyFive ha
    apply h.congr_fun
    · intro r hr
      dsimp [f]
      rw [Real.log_div (ha.trans hr).ne' ha.ne']
    · exact measurableSet_Ioi
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi a)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    dsimp [f]
    have hrpos : 0 < r := ha.trans hr
    exact div_nonneg (Real.log_nonneg (by
      rw [one_le_div ha]
      exact hr.le)) (pow_nonneg hrpos.le 65)
  calc
    (∫⁻ r : ℝ in Ioi 0, xiSquaredSeamPowerSixtyFourJensenKernel q r) =
        ∫⁻ r : ℝ in Ioi a, ENNReal.ofReal (f r) := by
      rw [← lintegral_indicator measurableSet_Ioi,
        ← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro r
      simp only [Set.indicator_apply, mem_Ioi]
      change
        (if 0 < r then if a ≤ r then ENNReal.ofReal (f r) else 0 else 0) =
          if a < r then ENNReal.ofReal (f r) else 0
      by_cases hlt : a < r
      · simp [hlt, hlt.le, ha.trans hlt]
      · simp only [hlt, ↓reduceIte]
        by_cases hle : a ≤ r
        · have heq : r = a := le_antisymm (not_lt.mp hlt) hle
          subst r
          simp [ha, f]
        · simp [hle]
    _ = ENNReal.ofReal (∫ r : ℝ in Ioi a, f r) := by
      exact (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = ENNReal.ofReal (1 / (4096 * a ^ 64)) := by
      rw [show (∫ r : ℝ in Ioi a, f r) = 1 / (4096 * a ^ 64) by
        simpa [f] using integral_Ioi_log_div_pow_sixtyFive ha]
    _ = ENNReal.ofReal (‖xiSquaredSeamOneCoordinate q ^ 64‖ / 4096) := by
      congr 1
      have hz := xiSquaredSeamOneCoordinate_ne_zero q
      dsimp [a]
      rw [xiSquaredSeamInverseRadius, norm_inv, norm_pow]
      field_simp [norm_ne_zero_iff.mpr hz]

/-- Radial divisor integral before the functional-equation pair quotient is taken. -/
def xiSquaredSeamPowerSixtyFourJensenDivisorIntegral : ℝ≥0∞ :=
  ∫⁻ r : ℝ in Ioi 0,
    ∑' q : XiZeroCopy, xiSquaredSeamPowerSixtyFourJensenKernel q r

/-- **Exact exponent-64 Tonelli law.**  The doubled radial divisor integral is `1/4096` of the
Hermitian power-64 mass. -/
theorem xiSquaredSeamPowerSixtyFourJensenDivisorIntegral_eq_hermitianMass :
    xiSquaredSeamPowerSixtyFourJensenDivisorIntegral =
      ENNReal.ofReal (xiSquaredSeamPowerSixtyFourHermitianMass / 4096) := by
  rw [xiSquaredSeamPowerSixtyFourJensenDivisorIntegral]
  rw [lintegral_tsum (fun q =>
    (aemeasurable_xiSquaredSeamPowerSixtyFourJensenKernel q).mono_measure
      (Measure.restrict_le_self))]
  simp_rw [lintegral_xiSquaredSeamPowerSixtyFourJensenKernel]
  have hsum : Summable (fun q : XiZeroCopy =>
      ‖xiSquaredSeamOneCoordinate q ^ 64‖ / 4096) :=
    summable_xiSquaredSeamOneCoordinate_pow_sixtyFour.norm.div_const 4096
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => by positivity) hsum]
  congr 1
  rw [xiSquaredSeamPowerSixtyFourHermitianMass, tsum_div_const]

end

end RHTower
