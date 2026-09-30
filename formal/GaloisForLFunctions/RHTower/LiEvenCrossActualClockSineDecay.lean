import GaloisForLFunctions.RHTower.LiEvenCrossActualClockSineSource
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds


/-!
# RH-conditional decay of the literal actual-current clock

Under RH every reciprocal Xi frequency is real.  The normalized sine atoms
converge pointwise to zero and are dominated by the complete summable squared
reciprocal mass.  Tannery's theorem gives sublinear response; the exact clock
substitution then gives decay of the literal series.  No zero-counting estimate
or independent RH producer is asserted.
-/

open Filter Topology
open scoped BigOperators
namespace RHTower
noncomputable section

private theorem exists_real_reciprocal_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    ∃ r : ℝ, (xiSpectralPoint q)⁻¹ = (r : ℂ) := by
  obtain ⟨a, ha⟩ := xiSpectralPoint_real_of_rh hRH q
  exact ⟨a⁻¹, by rw [ha, Complex.ofReal_inv]⟩

/-- Under RH the normalized sine atom is dominated by its squared reciprocal frequency. -/
theorem norm_liEvenCrossActualClockSineAtom_div_le_of_rh (hRH : RiemannHypothesis)
    {t : ℝ} (ht : 0 < t) (q : XiZeroCopy) :
    ‖liEvenCrossActualClockSineAtom t q / (t : ℂ)‖ ≤ ‖(xiSpectralPoint q)⁻¹‖ ^ 2 := by
  obtain ⟨r, hr⟩ := exists_real_reciprocal_of_rh hRH q
  unfold liEvenCrossActualClockSineAtom
  rw [hr]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sin, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos ht]
  rw [div_le_iff₀ ht]
  have hs := Real.abs_sin_le_abs (x := t * r)
  rw [abs_mul, abs_of_pos ht] at hs
  have h := mul_le_mul_of_nonneg_left hs (abs_nonneg r)
  nlinarith

/-- A fixed real reciprocal-frequency sine atom divided by the clock tends to zero. -/
theorem tendsto_liEvenCrossActualClockSineAtom_div_atTop_zero_of_rh
    (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    Tendsto (fun t : ℝ => liEvenCrossActualClockSineAtom t q / (t : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨r, hr⟩ := exists_real_reciprocal_of_rh hRH q
  have hz : Tendsto (fun t : ℝ => |r| / t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_inv_atTop_zero.const_mul |r|
  apply squeeze_zero_norm' _ hz
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  unfold liEvenCrossActualClockSineAtom
  rw [hr]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sin, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos ht]
  exact div_le_div_of_nonneg_right
    (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (t * r)) (abs_nonneg r)) ht.le

/-- Complete multiplicity-exact dominated convergence gives sublinear sine response under RH. -/
theorem tendsto_liEvenCrossActualClockResponse_div_atTop_zero_of_rh
    (hRH : RiemannHypothesis) :
    Tendsto (fun t : ℝ => liEvenCrossActualClockResponse t / t) atTop (𝓝 0) := by
  have hsq : Summable (fun q : XiZeroCopy => ‖(xiSpectralPoint q)⁻¹‖ ^ 2) := by
    simpa only [norm_inv, one_div, inv_pow] using xiSpectralPoint_inv_sq_summable
  have h : Tendsto (fun t : ℝ => ∑' q : XiZeroCopy,
      liEvenCrossActualClockSineAtom t q / (t : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence
      (f := fun t : ℝ => fun q : XiZeroCopy => liEvenCrossActualClockSineAtom t q / (t : ℂ))
      (g := fun _ : XiZeroCopy => (0 : ℂ)) hsq
      (tendsto_liEvenCrossActualClockSineAtom_div_atTop_zero_of_rh hRH)
      (by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht q
        exact norm_liEvenCrossActualClockSineAtom_div_le_of_rh hRH ht q)
  simp_rw [tsum_div_const, ← liEvenCrossActualClockResponse_ofReal_eq_tsum_sine] at h
  simpa only [Function.comp_def, Complex.div_ofReal_re, Complex.ofReal_re,
    Complex.zero_re] using (Complex.continuous_re.tendsto (0 : ℂ)).comp h

/-- RH implies decay of the literal actual-current clock series at positive infinity. -/
theorem tendsto_liEvenCrossActualCurrentClockSeries_atTop_zero_of_rh
    (hRH : RiemannHypothesis) :
    Tendsto liEvenCrossActualCurrentClockSeries atTop (𝓝 0) := by
  have ht : Tendsto (fun w : ℝ => 4 * Real.sqrt w) atTop atTop :=
    Real.tendsto_sqrt_atTop.const_mul_atTop (by norm_num)
  have h := (tendsto_liEvenCrossActualClockResponse_div_atTop_zero_of_rh hRH).comp ht
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
  have hclock : (4 * Real.sqrt w) ^ 2 / 16 = w := by
    rw [mul_pow, Real.sq_sqrt hw.le]
    ring
  have ht0 : (4 : ℝ) * Real.sqrt w ≠ 0 := by positivity
  dsimp only [Function.comp_def]
  rw [liEvenCrossActualClockResponse, hclock]
  exact mul_div_cancel_left₀ _ ht0

end
end RHTower
