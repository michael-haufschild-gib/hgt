import GaloisForLFunctions.OrderSixMetaplecticTheory.TheShiftedHeckeTraceAtAPrimaryPrimeIsASumOverShiftedHeckePoints
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheTwistedCosetsOfTheHeckeTraceReadTheDilateCorrelation
import GaloisForLFunctions.OrderSixMetaplecticTheory.ThePhasedConjugateTwistCarriesAQuarterOfTheDoublePole

/-!
# The constant term of the shifted Hecke trace carries the shift phase

`θ_s(T_b·)` has the amplitudes `b(v, h)e(ξ_hb)` (`phAmp`). In the shifted Hecke trace at a primary prime `p` every
pair of frequencies that survives the average over `O/p` carries a phase that only depends on `b` modulo `3`:

* the dilate pairs `(h, −p²h)` carry `e(ξ_hb)e(ξ_{p²h}b) = φ_b(h) = e(2ξ_hb)`, since `3 ∣ p² − 1` (`dilatePhase`);
  the two dilate families agree after `h ↦ −h` (`b(v, −h) = b(v, h)`);
* the low–low pairs `(k, −k)` carry `e(ξ_kb)e(−ξ_{−k}b) = φ_b(k)` (`pairPhase`).

So the constant term is the unshifted one (`integral_sourceHeckeTrace_bessel`) with `φ_b` on every coefficient
(`integral_sourceHeckeShiftTrace_bessel`):

`∫_P Tr_pF^b = N(p)|P| (2c²v^{4/3} + 2|p|^{−2}R[φ_bT(h)T(−p²h)](|p|v) + |p| R[φ_bT(k)T(kp)](v/|p|))`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- The amplitudes of `θ_s` are even: `b(v, −h) = b(v, h)`. -/
theorem sourceAmplitude_neg (v : ℝ) (hv : 0 < v) (h : O) :
    rationalSourceModeAmplitude v (-h) = rationalSourceModeAmplitude v h := by
  by_cases hh : h = 0
  · rw [hh, neg_zero]
  · rw [rationalSourceModeAmplitude_bessel v hv _ (neg_ne_zero.mpr hh), rationalSourceModeAmplitude_bessel v hv h hh,
      rationalSourceResidualFourierCoefficient_neg, cuspFrequency_neg, norm_neg]

/-- The amplitudes `b(v, h)e(ξ_hb)` of `θ_s(T_b·)`. -/
def phAmp (v : ℝ) (b h : O) : ℂ := rationalSourceModeAmplitude v h * tracePhase (cuspFrequency h * ringComplex b)

theorem summable_phAmp (v : ℝ) (hv : 0 < v) (b : O) : Summable (fun h => ‖phAmp v b h‖) := by
  simpa only [phAmp, norm_mul, tracePhase_norm, mul_one] using rationalSourceModeAmplitude_summable v hv

theorem shiftPhase_neg_neg (b h : O) : shiftPhase (-b) (-h) = shiftPhase b h := by
  simp only [shiftPhase, cuspFrequency_neg, map_neg]
  congr 1
  ring

/-- Opposite frequencies at opposite shifts: `e(ξ_kb)e(ξ_{−k}(−b)) = φ_b(k)`. -/
theorem pairPhase (b k : O) :
    tracePhase (cuspFrequency k * ringComplex b) * tracePhase (cuspFrequency (-k) * ringComplex (-b)) =
      shiftPhase b k := by
  rw [← AddChar.map_add_eq_mul, shiftPhase, cuspFrequency_neg, map_neg]
  congr 1
  ring

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem three_dvd_sq_sub_one : (3 : O) ∣ P.p ^ 2 - 1 := by
  obtain ⟨t, ht⟩ := P.three_dvd_sub_one
  exact ⟨t * (P.p + 1), by linear_combination (P.p + 1) * ht⟩

/-- **The dilate pairs carry `φ_b`.** `e(ξ_hb)e(ξ_{−p²h}(−b)) = e(2ξ_hb)`, since `3 ∣ p² − 1`. -/
theorem dilatePhase (b h : O) :
    tracePhase (cuspFrequency h * ringComplex b) *
        tracePhase (cuspFrequency (-(h * P.p) * P.p) * ringComplex (-b)) = shiftPhase b h := by
  have e1 : cuspFrequency h * ringComplex b + cuspFrequency (-(h * P.p) * P.p) * ringComplex (-b) =
      cuspFrequency h * ringComplex (b + P.p ^ 2 * b) := by
    rw [cuspFrequency_mul_right, cuspFrequency_neg, cuspFrequency_mul_right]
    simp only [map_add, map_mul, map_neg, map_pow]
    ring
  have e2 : (2 : ℂ) * ringComplex b = ringComplex (2 * b) := by rw [map_mul, map_ofNat]
  obtain ⟨t, ht⟩ := P.three_dvd_sq_sub_one
  rw [← AddChar.map_add_eq_mul, e1, shiftPhase, e2]
  exact tracePhase_congr_three h _ _ ⟨t * b, by linear_combination b * ht⟩

theorem heckeHigh_shift_source (b : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    P.heckeHigh (fun w => sourceTheta (integralComplexMatrix (integralTranslation b) • w)) (upperPoint z v hv) =
      cuspCharacterSeries (phAmp (‖ringComplex P.p‖ * v) b) (ringComplex P.p * z) := by
  simp only [heckeHigh]
  rw [P.dilation_upperPoint, sourceTheta_shift, cuspCharacterSeries_translate]
  rfl

theorem heckeLow_shift_phAmp (b r : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    P.heckeLow (fun w => sourceTheta (integralComplexMatrix (integralTranslation b) • w)) r (upperPoint z v hv) =
      cuspCharacterSeries (phAmp (v / ‖ringComplex P.p‖) b) ((z + 3 * ringComplex r) / ringComplex P.p) := by
  rw [P.heckeLow_shift_source, cuspCharacterSeries_translate]
  rfl

/-- The coefficients `b(v/|p|, k)e(−ξ_k·3β/p)e(ξ_kb)` of the shifted low point `Θ_b^{(x−β)}`. -/
def lowShift (v : ℝ) (β b : O) (k : O) : ℂ := P.shiftedLow v β k * tracePhase (cuspFrequency k * ringComplex b)

theorem summable_lowShift (v : ℝ) (hv : 0 < v) (β b : O) : Summable (fun k => ‖P.lowShift v β b k‖) := by
  simpa only [lowShift, norm_mul, tracePhase_norm, mul_one] using P.summable_shiftedLow v hv β

/-- The shifted trace at `(z, v)` as cusp series: two dilate terms and the phased low–low terms. -/
theorem sourceHeckeShiftTrace_upperPoint (b : O) (v : ℝ) (hv : 0 < v) (z : ℂ) :
    P.heckeShiftTrace sourceTheta b (upperPoint z v hv) =
      cuspCharacterSeries (phAmp (‖ringComplex P.p‖ * v) b) (ringComplex P.p * z) *
          ((Fintype.card P.Res : ℂ) *
            cuspCharacterSeries (fun m => phAmp (v / ‖ringComplex P.p‖) (-b) (m * P.p)) z) +
        ((Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => phAmp (v / ‖ringComplex P.p‖) b (m * P.p)) z) *
          cuspCharacterSeries (phAmp (‖ringComplex P.p‖ * v) (-b)) (ringComplex P.p * z) +
        ∑ y : {y : P.Res // y ≠ 0}, ringComplex (symbol (3 * P.lift y.1) P.p) *
          ((Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => cuspConv (P.lowShift v (P.lowBeta (P.lift y.1)) b)
            (phAmp (v / ‖ringComplex P.p‖) (-b)) (m * P.p)) z) := by
  rw [P.heckeShiftTrace_eq_hecke sourceTheta sourceTheta_automorphy]
  simp only [P.heckeHigh_shift_source, P.heckeLow_shift_phAmp]
  have hv1 : 0 < v / ‖ringComplex P.p‖ := div_pos hv P.norm_pos
  have hcP := summable_phAmp _ hv1 b
  have hcM := summable_phAmp _ hv1 (-b)
  have hii : ∑ x : P.Res, cuspCharacterSeries (phAmp (v / ‖ringComplex P.p‖) b)
      ((z + 3 * ringComplex (P.wShift + P.lift x)) / ringComplex P.p) =
      (Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => phAmp (v / ‖ringComplex P.p‖) b (m * P.p)) z := by
    have e : ∀ x : P.Res, z + 3 * ringComplex (P.wShift + P.lift x) =
        (z + 3 * ringComplex P.wShift) + 3 * ringComplex (P.lift x) := by
      intro x
      rw [map_add]
      ring
    simp_rw [e]
    rw [P.sum_cuspCharacterSeries_low _ hcP, cuspCharacterSeries_period]
  have hiii : ∀ y : {y : P.Res // y ≠ 0}, ∑ x : P.Res, ringComplex (symbol (3 * P.lift y.1) P.p) *
      cuspCharacterSeries (phAmp (v / ‖ringComplex P.p‖) b)
        ((z + 3 * ringComplex (P.lift x - P.lowBeta (P.lift y.1))) / ringComplex P.p) *
      cuspCharacterSeries (phAmp (v / ‖ringComplex P.p‖) (-b)) ((z + 3 * ringComplex (P.lift x)) / ringComplex P.p) =
      ringComplex (symbol (3 * P.lift y.1) P.p) * ((Fintype.card P.Res : ℂ) *
        cuspCharacterSeries (fun m => cuspConv (P.lowShift v (P.lowBeta (P.lift y.1)) b)
          (phAmp (v / ‖ringComplex P.p‖) (-b)) (m * P.p)) z) := by
    intro y
    set β := P.lowBeta (P.lift y.1)
    have hf : (fun h => phAmp (v / ‖ringComplex P.p‖) b h *
        tracePhase (cuspFrequency h * (-(3 * ringComplex β) / ringComplex P.p))) = P.lowShift v β b := by
      funext h
      simp only [phAmp, lowShift, shiftedLow]
      ring
    have e : ∀ x : P.Res, cuspCharacterSeries (phAmp (v / ‖ringComplex P.p‖) b)
          ((z + 3 * ringComplex (P.lift x - β)) / ringComplex P.p) *
        cuspCharacterSeries (phAmp (v / ‖ringComplex P.p‖) (-b)) ((z + 3 * ringComplex (P.lift x)) / ringComplex P.p) =
        cuspCharacterSeries (cuspConv (P.lowShift v β b) (phAmp (v / ‖ringComplex P.p‖) (-b)))
          ((z + 3 * ringComplex (P.lift x)) / ringComplex P.p) := by
      intro x
      rw [show (z + 3 * ringComplex (P.lift x - β)) / ringComplex P.p =
          (z + 3 * ringComplex (P.lift x)) / ringComplex P.p + (-(3 * ringComplex β) / ringComplex P.p) by
        rw [map_sub]; ring, cuspCharacterSeries_translate, hf, cuspCharacterSeries_mul (P.summable_lowShift v hv β b) hcM]
    simp_rw [mul_assoc, e]
    rw [← Finset.mul_sum, P.sum_cuspCharacterSeries_low _ (summable_cuspConv (P.summable_lowShift v hv β b) hcM)]
  rw [← Finset.mul_sum, P.sum_cuspCharacterSeries_low _ hcM z, ← Finset.sum_mul, hii, Finset.sum_comm]
  simp_rw [hiii]
  ring

/-- **The constant term of the shifted Hecke trace at `p`.** -/
theorem integral_sourceHeckeShiftTrace (b : O) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, P.heckeShiftTrace sourceTheta b (upperPoint z v hv) =
      (Fintype.card P.Res : ℂ) * periodArea *
        (2 * ∑' h : O, rationalSourceModeAmplitude (‖ringComplex P.p‖ * v) h *
            rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) (-(h * P.p) * P.p) * shiftPhase b h +
          ∑ y : {y : P.Res // y ≠ 0}, ringComplex (symbol (3 * P.lift y.1) P.p) *
            ∑' k : O, P.shiftedLow v (P.lowBeta (P.lift y.1)) k * shiftPhase b k *
              rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) (-k)) := by
  have hp := P.norm_pos
  have hv0 : 0 < ‖ringComplex P.p‖ * v := mul_pos hp hv
  have hv1 : 0 < v / ‖ringComplex P.p‖ := div_pos hv hp
  have haP := summable_phAmp _ hv0 b
  have haM := summable_phAmp _ hv0 (-b)
  have hinj : Function.Injective (fun m : O => m * P.p) := fun x y h => mul_right_cancel₀ P.ne_zero h
  have hcPp : Summable (fun m => ‖phAmp (v / ‖ringComplex P.p‖) b (m * P.p)‖) :=
    (summable_phAmp _ hv1 b).comp_injective hinj
  have hcMp : Summable (fun m => ‖phAmp (v / ‖ringComplex P.p‖) (-b) (m * P.p)‖) :=
    (summable_phAmp _ hv1 (-b)).comp_injective hinj
  have hg : ∀ β : O, Summable (fun m => ‖cuspConv (P.lowShift v β b) (phAmp (v / ‖ringComplex P.p‖) (-b)) (m * P.p)‖) :=
    fun β => (summable_cuspConv (P.summable_lowShift v hv β b) (summable_phAmp _ hv1 (-b))).comp_injective hinj
  simp_rw [P.sourceHeckeShiftTrace_upperPoint b v hv]
  have hc1 : Continuous (fun z : ℂ => cuspCharacterSeries (phAmp (‖ringComplex P.p‖ * v) b) (ringComplex P.p * z) *
      ((Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => phAmp (v / ‖ringComplex P.p‖) (-b) (m * P.p)) z)) :=
    ((cuspCharacterSeries_continuous _ haP).comp (continuous_const.mul continuous_id)).mul
      (continuous_const.mul (cuspCharacterSeries_continuous _ hcMp))
  have hc2 : Continuous (fun z : ℂ =>
      ((Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => phAmp (v / ‖ringComplex P.p‖) b (m * P.p)) z) *
        cuspCharacterSeries (phAmp (‖ringComplex P.p‖ * v) (-b)) (ringComplex P.p * z)) :=
    (continuous_const.mul (cuspCharacterSeries_continuous _ hcPp)).mul
      ((cuspCharacterSeries_continuous _ haM).comp (continuous_const.mul continuous_id))
  have hc3 : ∀ y : {y : P.Res // y ≠ 0}, Continuous (fun z : ℂ => ringComplex (symbol (3 * P.lift y.1) P.p) *
      ((Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => cuspConv (P.lowShift v (P.lowBeta (P.lift y.1)) b)
        (phAmp (v / ‖ringComplex P.p‖) (-b)) (m * P.p)) z)) := fun y =>
    continuous_const.mul (continuous_const.mul (cuspCharacterSeries_continuous _ (hg _)))
  have I1 : ∫ z in periodDomain, cuspCharacterSeries (phAmp (‖ringComplex P.p‖ * v) b) (ringComplex P.p * z) *
      ((Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => phAmp (v / ‖ringComplex P.p‖) (-b) (m * P.p)) z) =
      (Fintype.card P.Res : ℂ) * (periodArea * ∑' h : O, phAmp (‖ringComplex P.p‖ * v) b h *
        phAmp (v / ‖ringComplex P.p‖) (-b) (-(h * P.p) * P.p)) := by
    rw [show (fun z : ℂ => cuspCharacterSeries (phAmp (‖ringComplex P.p‖ * v) b) (ringComplex P.p * z) *
        ((Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => phAmp (v / ‖ringComplex P.p‖) (-b) (m * P.p)) z)) =
        fun z => (Fintype.card P.Res : ℂ) * (cuspCharacterSeries (phAmp (‖ringComplex P.p‖ * v) b) (ringComplex P.p * z) *
          cuspCharacterSeries (fun m => phAmp (v / ‖ringComplex P.p‖) (-b) (m * P.p)) z) by funext z; ring,
      integral_const_mul, integral_cuspCharacterSeries_mul_dilate P.p _ _ haP hcMp]
  have I2 : ∫ z in periodDomain,
      ((Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => phAmp (v / ‖ringComplex P.p‖) b (m * P.p)) z) *
        cuspCharacterSeries (phAmp (‖ringComplex P.p‖ * v) (-b)) (ringComplex P.p * z) =
      (Fintype.card P.Res : ℂ) * (periodArea * ∑' h : O, phAmp (‖ringComplex P.p‖ * v) (-b) h *
        phAmp (v / ‖ringComplex P.p‖) b (-(h * P.p) * P.p)) := by
    rw [show (fun z : ℂ => ((Fintype.card P.Res : ℂ) *
        cuspCharacterSeries (fun m => phAmp (v / ‖ringComplex P.p‖) b (m * P.p)) z) *
          cuspCharacterSeries (phAmp (‖ringComplex P.p‖ * v) (-b)) (ringComplex P.p * z)) =
        fun z => (Fintype.card P.Res : ℂ) * (cuspCharacterSeries (phAmp (‖ringComplex P.p‖ * v) (-b)) (ringComplex P.p * z) *
          cuspCharacterSeries (fun m => phAmp (v / ‖ringComplex P.p‖) b (m * P.p)) z) by funext z; ring,
      integral_const_mul, integral_cuspCharacterSeries_mul_dilate P.p _ _ haM hcPp]
  have I3 : ∀ y : {y : P.Res // y ≠ 0}, ∫ z in periodDomain, ringComplex (symbol (3 * P.lift y.1) P.p) *
      ((Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => cuspConv (P.lowShift v (P.lowBeta (P.lift y.1)) b)
        (phAmp (v / ‖ringComplex P.p‖) (-b)) (m * P.p)) z) =
      ringComplex (symbol (3 * P.lift y.1) P.p) * ((Fintype.card P.Res : ℂ) *
        (periodArea * cuspConv (P.lowShift v (P.lowBeta (P.lift y.1)) b) (phAmp (v / ‖ringComplex P.p‖) (-b)) 0)) := by
    intro y
    rw [integral_const_mul, integral_const_mul, integral_cuspCharacterSeries _ (hg _), zero_mul]
  have hS1 : ∑' h : O, phAmp (‖ringComplex P.p‖ * v) b h * phAmp (v / ‖ringComplex P.p‖) (-b) (-(h * P.p) * P.p) =
      ∑' h : O, rationalSourceModeAmplitude (‖ringComplex P.p‖ * v) h *
        rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) (-(h * P.p) * P.p) * shiftPhase b h := by
    refine tsum_congr fun h => ?_
    rw [← P.dilatePhase b h]
    simp only [phAmp]
    ring
  have hS2 : ∑' h : O, phAmp (‖ringComplex P.p‖ * v) (-b) h * phAmp (v / ‖ringComplex P.p‖) b (-(h * P.p) * P.p) =
      ∑' h : O, rationalSourceModeAmplitude (‖ringComplex P.p‖ * v) h *
        rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) (-(h * P.p) * P.p) * shiftPhase b h := by
    rw [← (Equiv.neg O).tsum_eq]
    refine tsum_congr fun h => ?_
    have hph := P.dilatePhase (-b) (-h)
    rw [neg_neg] at hph
    simp only [Equiv.neg_apply, phAmp]
    rw [← shiftPhase_neg_neg b h, ← hph, sourceAmplitude_neg _ hv0 h,
      show -(-h * P.p) * P.p = -(-(h * P.p) * P.p) by ring, sourceAmplitude_neg _ hv1 (-(h * P.p) * P.p)]
    ring
  have hS3 : ∀ β : O, cuspConv (P.lowShift v β b) (phAmp (v / ‖ringComplex P.p‖) (-b)) 0 =
      ∑' k : O, P.shiftedLow v β k * shiftPhase b k * rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) (-k) := by
    intro β
    unfold cuspConv
    refine tsum_congr fun k => ?_
    rw [← pairPhase b k]
    simp only [lowShift, phAmp, zero_sub]
    ring
  rw [integral_add ((integrableOn_periodDomain_of_continuous _ hc1).add (integrableOn_periodDomain_of_continuous _ hc2))
      (integrable_finsetSum _ fun y _ => integrableOn_periodDomain_of_continuous _ (hc3 y)),
    integral_add (integrableOn_periodDomain_of_continuous _ hc1) (integrableOn_periodDomain_of_continuous _ hc2),
    I1, I2, integral_finsetSum _ fun y _ => integrableOn_periodDomain_of_continuous _ (hc3 y),
    Finset.sum_congr rfl fun y _ => I3 y, hS1, hS2]
  simp only [hS3]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun y _ => by ring

/-- `φ_b(h)T(h)T(−p²h)`. -/
def phShiftSq (b : O) (h : O) : ℂ := shiftPhase b h * P.shiftSqCoeff h

/-- `φ_b(k)T(k)T(kp)` on `p ∤ k`. -/
def phDilate (b : O) (k : O) : ℂ := shiftPhase b k * P.dilateCoeff k

/-- **The phased dilate terms are the phased shifted square at `p²`.** -/
theorem shift_series_eq_phased (b : O) (v : ℝ) (hv : 0 < v) :
    ∑' h : O, rationalSourceModeAmplitude (‖ringComplex P.p‖ * v) h *
        rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) (-(h * P.p) * P.p) * shiftPhase b h =
      thetaConstant ^ 2 * (v : ℂ) ^ (4 / 3 : ℂ) +
        ((‖ringComplex P.p‖ : ℂ) ^ 2)⁻¹ * besselRemainder (P.phShiftSq b) (‖ringComplex P.p‖ * v) := by
  have hp := P.norm_pos
  have hpc : (‖ringComplex P.p‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hs := (summable_amplitude_mul
    (a := fun h => rationalSourceModeAmplitude (‖ringComplex P.p‖ * v) h * shiftPhase b h)
    (by simpa only [norm_mul, norm_shiftPhase, mul_one] using
      rationalSourceModeAmplitude_summable (‖ringComplex P.p‖ * v) (mul_pos hp hv))
    (rationalSourceModeAmplitude_summable (v / ‖ringComplex P.p‖) (div_pos hv hp))
    (fun h => -(h * P.p) * P.p)).congr (fun h => by ring)
  rw [hs.tsum_eq_add_tsum_ite 0, besselRemainder, ← tsum_mul_left]
  congr 1
  · rw [zero_mul, neg_zero, zero_mul, rationalSourceModeAmplitude_zero, rationalSourceModeAmplitude_zero,
      shiftPhase_zero, mul_one, ← cpow_mul_mul_cpow_div _ v hp hv]
    push_cast
    ring
  · refine tsum_congr fun h => ?_
    by_cases hh : h = 0
    · simp [hh]
    · have hh' : -(h * P.p) * P.p ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero hh P.ne_zero)) P.ne_zero
      rw [if_neg hh, if_neg hh, rationalSourceModeAmplitude_bessel _ (mul_pos hp hv) h hh,
        rationalSourceModeAmplitude_bessel _ (div_pos hv hp) _ hh', P.norm_cuspFrequency_dilate, phShiftSq,
        shiftSqCoeff, besselSq]
      have e : 4 * Real.pi * (‖cuspFrequency h‖ * ‖ringComplex P.p‖ ^ 2) * (v / ‖ringComplex P.p‖) =
          4 * Real.pi * ‖cuspFrequency h‖ * (‖ringComplex P.p‖ * v) := by
        field_simp
      rw [e]
      push_cast
      field_simp

/-- The phased twisted cosets, collected by frequency. -/
theorem sum_twisted_conv_phased (b : O) (v : ℝ) (hv : 0 < v) :
    ∑ y : {y : P.Res // y ≠ 0}, ringComplex (symbol (3 * P.lift y.1) P.p) *
        ∑' k : O, P.shiftedLow v (P.lowBeta (P.lift y.1)) k * shiftPhase b k *
          rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) (-k) =
      ∑' k : O, shiftPhase b k * (P.twistedCoeff k * (rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) k *
        rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) (-k))) := by
  have hb : Summable (fun h => ‖rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) h‖) :=
    rationalSourceModeAmplitude_summable _ (div_pos hv P.norm_pos)
  have hs : ∀ y : {y : P.Res // y ≠ 0}, Summable (fun k => ringComplex (symbol (3 * P.lift y.1) P.p) *
      (P.shiftedLow v (P.lowBeta (P.lift y.1)) k * shiftPhase b k *
        rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) (-k))) := by
    intro y
    refine Summable.mul_left _ (Summable.of_norm_bounded
      (hb.mul_right (∑' j, ‖rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) j‖)) fun k => ?_)
    rw [norm_mul, norm_mul, norm_shiftPhase, mul_one, shiftedLow, norm_mul, tracePhase_norm, mul_one]
    exact mul_le_mul_of_nonneg_left (hb.le_tsum _ fun j _ => norm_nonneg _) (norm_nonneg _)
  simp only [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun y _ => hs y)]
  refine tsum_congr fun k => ?_
  simp only [twistedCoeff, Finset.sum_mul, Finset.mul_sum, shiftedLow]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **The phased twisted cosets are the phased dilate correlation.** -/
theorem twisted_series_eq_phased (b : O) (v : ℝ) (hv : 0 < v) :
    ∑' k : O, shiftPhase b k * (P.twistedCoeff k * (rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) k *
        rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) (-k))) =
      (‖ringComplex P.p‖ : ℂ) * besselRemainder (P.phDilate b) (v / ‖ringComplex P.p‖) := by
  rw [besselRemainder, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · rw [if_pos hk, hk, P.twistedCoeff_of_dvd 0 (dvd_zero _)]
    ring
  · rw [if_neg hk, sourceAmplitude_mul_neg _ (div_pos hv P.norm_pos) k hk, besselSq, phDilate]
    have h := P.twistedCoeff_mul_sq k
    linear_combination (shiftPhase b k * (((v / ‖ringComplex P.p‖ : ℝ) : ℂ) ^ 2 *
      schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency k‖ * (v / ‖ringComplex P.p‖)) ^ 2)) * h

/-- **The constant term of the shifted Hecke trace in Bessel form.** -/
theorem integral_sourceHeckeShiftTrace_bessel (b : O) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, P.heckeShiftTrace sourceTheta b (upperPoint z v hv) =
      (Fintype.card P.Res : ℂ) * periodArea *
        (2 * (thetaConstant ^ 2 * (v : ℂ) ^ (4 / 3 : ℂ) +
            ((‖ringComplex P.p‖ : ℂ) ^ 2)⁻¹ * besselRemainder (P.phShiftSq b) (‖ringComplex P.p‖ * v)) +
          (‖ringComplex P.p‖ : ℂ) * besselRemainder (P.phDilate b) (v / ‖ringComplex P.p‖)) := by
  rw [P.integral_sourceHeckeShiftTrace b v hv, P.shift_series_eq_phased b v hv, P.sum_twisted_conv_phased b v hv,
    P.twisted_series_eq_phased b v hv]

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
