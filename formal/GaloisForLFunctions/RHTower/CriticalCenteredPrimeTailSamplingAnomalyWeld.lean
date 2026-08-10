import GaloisForLFunctions.RHTower.CriticalCenteredPrimeTailPositiveCompletionWall
import GaloisForLFunctions.RHTower.XiMassCriticalDiscreteRemainder
import GaloisForLFunctions.RHTower.ZetaTruncatedExtension
import GaloisForLFunctions.RHTower.ZetaCriticalLineNotSquareIntegrable

/-!
# Centered prime-tail sampling-anomaly weld

The entire correction left by exact `Λ-1` centering is not an arbitrary zero-free gauge.  On the
punctured right half-plane it is exactly

`-s ∫_1^∞ {x} x^(-s-1) dx`.

After `x=exp h`, this is the positive-log fractional-part carrier
`{exp h} exp(-h/2)` on the critical line.  The same carrier already occurs, with opposite sign, as
Route T's floor-sawtooth density.  Its mass pairing is uniformly bounded.  Thus discrete centering
splits canonically into the finite-order divisor current of `(s-1)ζ(s)` plus a source-defined,
mass-controlled sampling anomaly; exponentiating that anomaly, as in the entire carrier, is not
needed for the Route T estimate.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- Positive-log fractional-part Mellin anomaly. -/
def criticalCenteredSamplingAnomaly (s : ℂ) : ℂ :=
  -s * zetaSawtoothTail 1 s

/-- Sampling anomaly is analytic throughout the open right half-plane, including the former pole. -/
theorem analyticAt_criticalCenteredSamplingAnomaly
    {s : ℂ} (hs0 : 0 < s.re) :
    AnalyticAt ℂ criticalCenteredSamplingAnomaly s := by
  change AnalyticAt ℂ (fun z : ℂ => -z * zetaSawtoothTail 1 z) s
  exact analyticAt_id.neg.mul
    (analyticOnNhd_zetaSawtoothTail (N := 1) (by norm_num) s hs0)

/-- Away from the removed pole, the entire gauge derivative is the usual zeta sampling error. -/
theorem centeredPrimeTailGaugeDerivative_eq_zeta_sampling_error
    {s : ℂ} (hs1 : s ≠ 1) :
    centeredPrimeTailGaugeDerivative s =
      riemannZeta s - 1 - 1 / (s - 1) := by
  rw [centeredPrimeTailGaugeDerivative, dslope_of_ne _ hs1, slope_def_field,
    zetaResidueUnit_one]
  have hunit : zetaResidueUnit s = (s - 1) * riemannZeta s := by
    simp [zetaResidueUnit, Function.update_of_ne hs1]
  rw [hunit]
  field_simp [sub_ne_zero.mpr hs1]
  ring

/-- **C49 analytic weld.**  Exact centered gauge equals the fractional-part sampling anomaly on
the whole punctured right half-plane. -/
theorem centeredPrimeTailGaugeDerivative_eq_samplingAnomaly
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    centeredPrimeTailGaugeDerivative s = criticalCenteredSamplingAnomaly s := by
  rw [centeredPrimeTailGaugeDerivative_eq_zeta_sampling_error hs1,
    criticalCenteredSamplingAnomaly]
  have hz := zeta_eq_truncated_of_re_pos (N := 1) (by norm_num) hs0 hs1
  rw [zetaTruncated] at hz
  norm_num at hz ⊢
  linear_combination hz

/-- **C49 closed analytic weld.**  The puncture is removable on both sides, so the equality holds
everywhere in the open right half-plane. -/
theorem centeredPrimeTailGaugeDerivative_eq_samplingAnomaly_of_re_pos
    {s : ℂ} (hs0 : 0 < s.re) :
    centeredPrimeTailGaugeDerivative s = criticalCenteredSamplingAnomaly s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hgauge : AnalyticOnNhd ℂ centeredPrimeTailGaugeDerivative U :=
    fun z _ => analyticAt_centeredPrimeTailGaugeDerivative z
  have hanomaly : AnalyticOnNhd ℂ criticalCenteredSamplingAnomaly U :=
    fun _ hz => analyticAt_criticalCenteredSamplingAnomaly hz
  have htwo : (2 : ℂ) ∈ U := by norm_num [U]
  have heq : centeredPrimeTailGaugeDerivative =ᶠ[nhds (2 : ℂ)]
      criticalCenteredSamplingAnomaly := by
    have hsafe : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hsafe] with z hz
    exact centeredPrimeTailGaugeDerivative_eq_samplingAnomaly (by linarith)
      (fun h => by rw [h] at hz; norm_num at hz)
  exact hgauge.eqOn_of_preconnected_of_eventuallyEq hanomaly hUpre htwo heq hs0

/-- Exact fractional-part integral at the removed pole. -/
theorem zetaSawtoothTail_one_one :
    zetaSawtoothTail 1 1 = 1 - (Real.eulerMascheroniConstant : ℂ) := by
  have h := centeredPrimeTailGaugeDerivative_eq_samplingAnomaly_of_re_pos
    (s := (1 : ℂ)) (by norm_num)
  rw [centeredPrimeTailGaugeDerivative, dslope_same,
    deriv_zetaResidueUnit_one, criticalCenteredSamplingAnomaly] at h
  norm_num at h
  have hneg := congrArg Neg.neg h
  rw [neg_neg] at hneg
  calc
    zetaSawtoothTail 1 1 = -((Real.eulerMascheroniConstant : ℂ) - 1) := hneg.symm
    _ = 1 - (Real.eulerMascheroniConstant : ℂ) := by ring

/-- On the open right half-plane the centered current is canonically the finite-order divisor
log-current plus the fractional-part sampling anomaly. -/
theorem centeredPrimeTailCurrentContinuation_eq_logDeriv_add_samplingAnomaly
    {s : ℂ} (hs0 : 0 < s.re) :
    centeredPrimeTailCurrentContinuation s =
      logDeriv zetaResidueUnit s + criticalCenteredSamplingAnomaly s := by
  have hg := centeredPrimeTailGaugeDerivative_eq_samplingAnomaly_of_re_pos hs0
  rw [centeredPrimeTailGaugeDerivative] at hg
  rw [centeredPrimeTailCurrentContinuation, ← hg]
  ring

/-- Quantitative right-half-plane control inherited from bounded fractional part. -/
theorem norm_centeredPrimeTailGaugeDerivative_le
    {s : ℂ} (hs0 : 0 < s.re) :
    ‖centeredPrimeTailGaugeDerivative s‖ ≤ ‖s‖ / s.re := by
  rw [centeredPrimeTailGaugeDerivative_eq_samplingAnomaly_of_re_pos hs0,
    criticalCenteredSamplingAnomaly, norm_mul, norm_neg]
  have htail := norm_zetaSawtoothTail_le (N := 1) hs0 (by norm_num)
  norm_num at htail
  calc
    ‖s‖ * ‖zetaSawtoothTail 1 s‖ ≤ ‖s‖ * (s.re)⁻¹ :=
      mul_le_mul_of_nonneg_left htail (norm_nonneg s)
    _ = ‖s‖ / s.re := by rw [div_eq_mul_inv]

/-- Natural-floor error on logarithmic time is exactly negative fractional part. -/
theorem natFloor_exp_sub_exp_eq_neg_fract (h : ℝ) :
    (⌊Real.exp h⌋₊ : ℝ) - Real.exp h = -Int.fract (Real.exp h) := by
  have hcast : ((⌊Real.exp h⌋₊ : ℕ) : ℝ) = ((⌊Real.exp h⌋ : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℤ => (n : ℝ))
      (Int.natCast_floor_eq_floor (Real.exp_pos h).le)
  rw [hcast, ← Int.self_sub_fract]
  ring

/-- Pointwise weld: Route T's floor density is the negative positive-log fractional-part carrier
paired with the actual Xi mass outgoing derivative. -/
theorem xiMassCriticalFloorSawtoothDensity_eq_neg_fractLogCarrier
    (a sigma u h : ℝ) :
    xiMassCriticalFloorSawtoothDensity a sigma u h =
      -fractLogCarrier h * xiMassCriticalOutgoingDerivative a sigma u h := by
  rw [xiMassCriticalFloorSawtoothDensity, fractLogCarrier,
    natFloor_exp_sub_exp_eq_neg_fract]
  push_cast
  ring

/-- Mass pairing of the centered sampling anomaly, kept before exponentiation. -/
def xiMassCriticalSamplingAnomalyFlux (a sigma u : ℝ) : ℂ :=
  ∫ h in Ioi (0 : ℝ),
    -fractLogCarrier h * xiMassCriticalOutgoingDerivative a sigma u h

/-- The analytic sampling-anomaly carrier and Route T floor current are literally the same flux. -/
theorem xiMassCriticalSamplingAnomalyFlux_eq_floorSawtoothFlux
    (a sigma u : ℝ) :
    xiMassCriticalSamplingAnomalyFlux a sigma u =
      xiMassCriticalFloorSawtoothFlux a sigma u := by
  rw [xiMassCriticalSamplingAnomalyFlux, xiMassCriticalFloorSawtoothFlux]
  apply integral_congr_ae
  filter_upwards with h
  exact (xiMassCriticalFloorSawtoothDensity_eq_neg_fractLogCarrier a sigma u h).symm

/-- **C49 mass weld.**  Sampling anomaly has one height-independent Route T bound. -/
theorem norm_xiMassCriticalSamplingAnomalyFlux_le
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u : ℝ) :
    ‖xiMassCriticalSamplingAnomalyFlux a sigma u‖ ≤
      2 * xiMassCriticalOutgoingZeroShiftBound sigma := by
  rw [xiMassCriticalSamplingAnomalyFlux_eq_floorSawtoothFlux]
  exact norm_xiMassCriticalFloorSawtoothFlux_le ha hsigma u

end

end RHTower
