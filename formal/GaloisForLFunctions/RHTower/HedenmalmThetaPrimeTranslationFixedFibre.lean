import GaloisForLFunctions.RHTower.FrankensteinThetaPrimeTranslationCommonForcing
import GaloisForLFunctions.RHTower.HedenmalmThetaTranslationWeightNoGo
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedThreePoint

/-!
# Prime anomalies cannot inhabit one fixed theta source fibre

The exact integer-translation anomaly is a bounded theta interval pointwise, but the reciprocal
theta weight changes its meaning completely.  At the negative cusp the interval reaches one fixed
prime step toward the center.  Squaring that larger density and dividing by the original density
produces an exponentially divergent lower bound.

Consequently every nontrivial integer anomaly fails to belong to Hedenmalm's fixed source Hilbert
space `L²(ℝ, k⁻¹ dx)`.  Thus the flat rank-one prime connection is a valid pointwise/moving-fibre
identity, not a bounded or even vector-valued perturbation of the compact fixed-fibre theta
operator.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmPrimeTranslation HedenmalmIntervalAnomaly

namespace HedenmalmThetaSource

theorem antitoneOn_thetaCuspFullSource :
    AntitoneOn thetaCuspFullSource (Ici (0 : ℝ)) := by
  intro s hs t ht hst
  rcases hst.eq_or_lt with rfl | hst
  · exact le_rfl
  · have hprod := strictAntiOn_thetaCuspFullSource_mul_reflect 0 hs ht hst
    simp only [zero_add, zero_sub, thetaCuspFullSource_neg] at hprod
    nlinarith [thetaCuspFullSource_pos_all s, thetaCuspFullSource_pos_all t]

theorem thetaIntervalMass_neg_shift_ge
    {a y : ℝ} (ha : 0 < a) (hy : a ≤ y) :
    (a / 4) * thetaCuspFullSource (y - 3 * a / 4) ≤
      intervalMass thetaSource (-y) (-y + a) := by
  have hleft : 0 ≤ y - a := by linarith
  have hright : y - 3 * a / 4 ≤ y := by linarith
  have hsmall : y - a ≤ y - 3 * a / 4 := by linarith
  have hreflect : intervalMass thetaSource (-y) (-y + a) =
      intervalMass thetaSource (y - a) y := by
    rw [show -y = -y from rfl,
      show -y + a = -(y - a) by ring,
      intervalMass_neg thetaSource thetaSource_even (by linarith)]
  rw [hreflect, intervalMass]
  have hkint : IntegrableOn thetaCuspFullSource (Ioc (y - a) (y - 3 * a / 4)) volume :=
    thetaSource.integrable_k.integrableOn
  have hconst : IntegrableOn (fun _ : ℝ => thetaCuspFullSource (y - 3 * a / 4))
      (Ioc (y - a) (y - 3 * a / 4)) volume := by
    exact integrableOn_const (measure_Ioc_lt_top.ne)
  have hmono :
      (∫ _ in Ioc (y - a) (y - 3 * a / 4), thetaCuspFullSource (y - 3 * a / 4)) ≤
        ∫ u in Ioc (y - a) (y - 3 * a / 4), thetaCuspFullSource u := by
    refine setIntegral_mono_on hconst hkint measurableSet_Ioc ?_
    intro u hu
    exact antitoneOn_thetaCuspFullSource
      (by simpa only [mem_Ici] using (lt_of_le_of_lt hleft hu.1).le)
      (by simp only [mem_Ici]; linarith) hu.2
  have hsubset : Ioc (y - a) (y - 3 * a / 4) ⊆ Ioc (y - a) y := by
    intro u hu
    exact ⟨hu.1, hu.2.trans hright⟩
  have hbig :
      (∫ u in Ioc (y - a) (y - 3 * a / 4), thetaCuspFullSource u) ≤
        ∫ u in Ioc (y - a) y, thetaCuspFullSource u := by
    refine setIntegral_mono_set thetaSource.integrable_k.integrableOn ?_
      (Filter.Eventually.of_forall fun u hu => hsubset hu)
    filter_upwards with u
    exact (thetaCuspFullSource_pos_all u).le
  calc
    (a / 4) * thetaCuspFullSource (y - 3 * a / 4) =
        ∫ _ in Ioc (y - a) (y - 3 * a / 4),
          thetaCuspFullSource (y - 3 * a / 4) := by
      rw [← intervalIntegral.integral_of_le hsmall,
        intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ ∫ u in Ioc (y - a) (y - 3 * a / 4), thetaCuspFullSource u := hmono
    _ ≤ ∫ u in Ioc (y - a) y, thetaCuspFullSource u := hbig

theorem thetaEnvelope_sq_ge_linear
    {b y : ℝ} (hb : 2 * Real.exp (-2 * b) ≤ 1) :
    thetaEnvelope y * Real.exp (9 * y / 2 - 9 * b) ≤
      thetaEnvelope (y - b) ^ 2 := by
  have hcorr : 0 ≤ Real.pi * Real.exp (2 * y) *
      (1 - 2 * Real.exp (-2 * b)) := by
    positivity
  have hextra : 1 ≤ Real.exp (Real.pi * Real.exp (2 * y) *
      (1 - 2 * Real.exp (-2 * b))) := by
    simpa using Real.one_le_exp_iff.mpr hcorr
  have hid : thetaEnvelope (y - b) ^ 2 =
      thetaEnvelope y * Real.exp (9 * y / 2 - 9 * b) *
        Real.exp (Real.pi * Real.exp (2 * y) *
          (1 - 2 * Real.exp (-2 * b))) := by
    unfold thetaEnvelope
    rw [show Real.exp (2 * (y - b)) =
        Real.exp (2 * y) * Real.exp (-2 * b) by
      rw [show 2 * (y - b) = 2 * y + (-2 * b) by ring, Real.exp_add]]
    rw [pow_two, ← Real.exp_add]
    repeat' rw [← Real.exp_add]
    congr 1
    rw [Real.exp_add]
    ring
  rw [hid]
  have hbase : 0 ≤ thetaEnvelope y * Real.exp (9 * y / 2 - 9 * b) := by
    exact mul_nonneg (thetaEnvelope_pos y).le (Real.exp_pos _).le
  calc
    thetaEnvelope y * Real.exp (9 * y / 2 - 9 * b) =
        (thetaEnvelope y * Real.exp (9 * y / 2 - 9 * b)) * 1 := by ring
    _ ≤ (thetaEnvelope y * Real.exp (9 * y / 2 - 9 * b)) *
        Real.exp (Real.pi * Real.exp (2 * y) *
          (1 - 2 * Real.exp (-2 * b))) :=
      mul_le_mul_of_nonneg_left hextra hbase

theorem two_exp_neg_three_quarter_log_le_one
    {n : ℕ} (hn : 2 ≤ n) :
    2 * Real.exp (-2 * (3 * Real.log n / 4)) ≤ 1 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hlog : 0 < Real.log n := Real.log_pos (lt_of_lt_of_le (by norm_num) hnR)
  have hlt : Real.exp (-2 * (3 * Real.log n / 4)) < Real.exp (-Real.log n) := by
    apply Real.exp_lt_exp.mpr
    linarith
  have hexp : Real.exp (-Real.log n) = ((n : ℝ))⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hnpos]
  have hdiv : 2 * ((n : ℝ))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hnpos).2 hnR
  rw [hexp] at hlt
  linarith

/-- Squaring one theta source a fixed distance closer to the center overwhelms the original
source at the negative cusp.  This is the fixed-fibre wall behind the prime anomaly. -/
theorem thetaSource_shift_sq_div_ge_linear
    {b y : ℝ} (hy : 0 ≤ y) (hyb : 0 < y - b)
    (hb : 2 * Real.exp (-2 * b) ≤ 1) :
    (thetaEnvelopeLower ^ 2 / thetaEnvelopeUpper) *
        Real.exp (9 * y / 2 - 9 * b) ≤
      thetaCuspFullSource (y - b) ^ 2 / thetaCuspFullSource y := by
  have hU : 0 < thetaEnvelopeUpper := thetaEnvelopeUpper_pos
  have hL : 0 < thetaEnvelopeLower := thetaEnvelopeLower_pos
  have hE : 0 < thetaEnvelope y := thetaEnvelope_pos y
  have hshiftE : 0 < thetaEnvelope (y - b) := thetaEnvelope_pos _
  have hky : 0 < thetaCuspFullSource y := thetaCuspFullSource_pos_all y
  have hupper := thetaCuspFullSource_le_envelope hy
  have hlower := thetaCuspFullSource_ge_envelope hyb
  have hsq : (thetaEnvelopeLower * thetaEnvelope (y - b)) ^ 2 ≤
      thetaCuspFullSource (y - b) ^ 2 := by
    exact (sq_le_sq₀ (mul_nonneg hL.le hshiftE.le)
      (thetaCuspFullSource_pos_all _).le).2 hlower
  apply (le_div_iff₀ hky).2
  calc
    (thetaEnvelopeLower ^ 2 / thetaEnvelopeUpper) *
          Real.exp (9 * y / 2 - 9 * b) * thetaCuspFullSource y
        ≤ (thetaEnvelopeLower ^ 2 / thetaEnvelopeUpper) *
          Real.exp (9 * y / 2 - 9 * b) *
            (thetaEnvelopeUpper * thetaEnvelope y) := by
      gcongr
    _ = thetaEnvelopeLower ^ 2 *
          (thetaEnvelope y * Real.exp (9 * y / 2 - 9 * b)) := by
      field_simp [hU.ne']
    _ ≤ thetaEnvelopeLower ^ 2 * thetaEnvelope (y - b) ^ 2 := by
      gcongr
      exact thetaEnvelope_sq_ge_linear hb
    _ = (thetaEnvelopeLower * thetaEnvelope (y - b)) ^ 2 := by ring
    _ ≤ thetaCuspFullSource (y - b) ^ 2 := hsq

/-- Pointwise weighted energy density of the integer anomaly in the fixed Hedenmalm source
fibre `L²(k⁻¹ dx)`. -/
def thetaIntegerAnomalyFixedFibreEnergy (n : ℕ) (x : ℝ) : ℝ :=
  ‖integerAnomaly thetaSource n x‖ ^ 2 / thetaCuspFullSource x

/-- The negative cusp forces at least an exponentially growing fixed-fibre anomaly energy.
The doubly exponential terms have the stronger sign; this theorem keeps only the surviving
linear exponential needed for non-admission. -/
theorem thetaIntegerAnomalyFixedFibreEnergy_neg_ge
    {n : ℕ} (hn : 2 ≤ n) {y : ℝ} (hy : Real.log n ≤ y) :
    (((n : ℝ) ^ (-(1 / 2 : ℝ))) * (Real.log n / 4)) ^ 2 *
        (thetaEnvelopeLower ^ 2 / thetaEnvelopeUpper) *
          Real.exp (9 * y / 2 - 9 * (3 * Real.log n / 4)) ≤
      thetaIntegerAnomalyFixedFibreEnergy n (-y) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have ha : 0 < Real.log n := Real.log_pos (lt_of_lt_of_le (by norm_num) hnR)
  have hc : 0 < (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hnpos _
  have hk : 0 < thetaCuspFullSource y := thetaCuspFullSource_pos_all y
  have hy0 : 0 ≤ y := le_trans ha.le hy
  have hyb : 0 < y - 3 * Real.log n / 4 := by linarith
  have hmass := thetaIntervalMass_neg_shift_ge ha hy
  have hmass0 : 0 ≤ intervalMass thetaSource (-y) (-y + Real.log n) := by
    exact (intervalMass_pos thetaSource (by linarith)).le
  have hshift0 : 0 ≤ thetaCuspFullSource (y - 3 * Real.log n / 4) :=
    (thetaCuspFullSource_pos_all _).le
  have hscaled :
      (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((Real.log n / 4) * thetaCuspFullSource (y - 3 * Real.log n / 4)) ≤
        (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          intervalMass thetaSource (-y) (-y + Real.log n) :=
    mul_le_mul_of_nonneg_left hmass hc.le
  have hscaled0 : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) *
      ((Real.log n / 4) * thetaCuspFullSource (y - 3 * Real.log n / 4)) := by
    positivity
  have hmassScaled0 : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) *
      intervalMass thetaSource (-y) (-y + Real.log n) :=
    mul_nonneg hc.le hmass0
  have hscaledSq := (sq_le_sq₀ hscaled0 hmassScaled0).2 hscaled
  have hratio := thetaSource_shift_sq_div_ge_linear hy0 hyb
    (two_exp_neg_three_quarter_log_le_one hn)
  have hanorm :
      ‖integerAnomaly thetaSource n (-y)‖ ^ 2 =
        ((n : ℝ) ^ (-(1 / 2 : ℝ)) *
          intervalMass thetaSource (-y) (-y + Real.log n)) ^ 2 := by
    rw [integerAnomaly_eq_intervalMass thetaSource hn1]
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hc.le hmass0)]
  rw [thetaIntegerAnomalyFixedFibreEnergy, hanorm, thetaCuspFullSource_neg]
  calc
    (((n : ℝ) ^ (-(1 / 2 : ℝ))) * (Real.log n / 4)) ^ 2 *
          (thetaEnvelopeLower ^ 2 / thetaEnvelopeUpper) *
            Real.exp (9 * y / 2 - 9 * (3 * Real.log n / 4)) =
        (((n : ℝ) ^ (-(1 / 2 : ℝ))) * (Real.log n / 4)) ^ 2 *
          ((thetaEnvelopeLower ^ 2 / thetaEnvelopeUpper) *
            Real.exp (9 * y / 2 - 9 * (3 * Real.log n / 4))) := by ring
    _ ≤ (((n : ℝ) ^ (-(1 / 2 : ℝ))) * (Real.log n / 4)) ^ 2 *
          (thetaCuspFullSource (y - 3 * Real.log n / 4) ^ 2 /
            thetaCuspFullSource y) := by
      gcongr
    _ = (((n : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((Real.log n / 4) * thetaCuspFullSource
            (y - 3 * Real.log n / 4))) ^ 2) / thetaCuspFullSource y := by ring
    _ ≤ (((n : ℝ) ^ (-(1 / 2 : ℝ)) *
          intervalMass thetaSource (-y) (-y + Real.log n)) ^ 2) /
            thetaCuspFullSource y := by
      exact div_le_div_of_nonneg_right hscaledSq hk.le

theorem continuous_thetaIntegerAnomalyFixedFibreEnergy (n : ℕ) :
    Continuous (thetaIntegerAnomalyFixedFibreEnergy n) := by
  have hanomaly : Continuous (fun x : ℝ => integerAnomaly thetaSource n x) := by
    rw [show (fun x : ℝ => integerAnomaly thetaSource n x) = fun x =>
        Complex.I * ((((n : ℝ) ^ (-(1 / 2 : ℝ))) * thetaSource.mass *
          (thetaSource.cdfFun (x + Real.log n) - thetaSource.cdfFun x) : ℝ) : ℂ) by
      funext x
      exact integerAnomaly_eq thetaSource n x]
    have hcdf : Continuous thetaSource.cdfFun := thetaSource.continuous_cdfFun
    fun_prop
  exact (hanomaly.norm.pow 2).div contDiff_thetaCuspFullSource.continuous
    (fun x => (thetaCuspFullSource_pos_all x).ne')

theorem not_integrableOn_exp_Ioi_any (A : ℝ) :
    ¬ IntegrableOn (fun x : ℝ => Real.exp x) (Ioi A) volume := by
  intro h
  set C : ℝ := ∫ x in Ioi A, Real.exp x with hC
  have hbound : ∀ T : ℝ, A ≤ T → Real.exp T - Real.exp A ≤ C := by
    intro T hT
    have hsub : Ioc A T ⊆ Ioi A := Ioc_subset_Ioi_self
    have hle : (∫ x in Ioc A T, Real.exp x) ≤ C := by
      refine setIntegral_mono_set h ?_ (Filter.Eventually.of_forall fun x hx => hsub hx)
      filter_upwards with x
      exact (Real.exp_pos x).le
    have hval : (∫ x in Ioc A T, Real.exp x) = Real.exp T - Real.exp A := by
      rw [← intervalIntegral.integral_of_le hT, integral_exp]
    rwa [hval] at hle
  have hlim : Tendsto (fun T : ℝ => Real.exp T - Real.exp A) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ (-Real.exp A) Real.tendsto_exp_atTop
  obtain ⟨T, hT⟩ := (hlim.eventually_gt_atTop C).and (eventually_ge_atTop A) |>.exists
  exact absurd (hbound T hT.2) (not_le.mpr hT.1)

/-- **P-G104 fixed-fibre anomaly exclusion.**  Every genuine integer-translation anomaly has
infinite norm in the one fixed Hedenmalm source fibre.  The flat rank-one prime connection from
P-G103 therefore lives only pointwise/on a moving pre-Hilbert carrier; it cannot be a bounded or
even vector-valued perturbation of the compact theta operator on `L²(k⁻¹ dx)`. -/
theorem not_integrable_thetaIntegerAnomalyFixedFibreEnergy
    {n : ℕ} (hn : 2 ≤ n) :
    ¬ Integrable (thetaIntegerAnomalyFixedFibreEnergy n) (volume : Measure ℝ) := by
  intro henergy
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hlog : 0 < Real.log n := Real.log_pos (lt_of_lt_of_le (by norm_num) hnR)
  let b : ℝ := 3 * Real.log n / 4
  let C : ℝ :=
    (((n : ℝ) ^ (-(1 / 2 : ℝ))) * (Real.log n / 4)) ^ 2 *
      (thetaEnvelopeLower ^ 2 / thetaEnvelopeUpper)
  have hC : 0 < C := by
    dsimp [C]
    have hpow : 0 < (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hnpos _
    have hU := thetaEnvelopeUpper_pos
    have hL := thetaEnvelopeLower_pos
    positivity
  let Y : ℝ := max (Real.log n)
    ((9 * b - Real.log C) / (7 / 2 : ℝ))
  have hdom : ∀ y ∈ Ioi Y,
      Real.exp y ≤ C * Real.exp (9 * y / 2 - 9 * b) := by
    intro y hy
    have hycrit : (9 * b - Real.log C) / (7 / 2 : ℝ) < y :=
      lt_of_le_of_lt (le_max_right _ _) hy
    rw [← Real.exp_log hC]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp only [b] at hycrit ⊢
    linarith
  have hlower : ∀ y ∈ Ioi Y,
      C * Real.exp (9 * y / 2 - 9 * b) ≤
        thetaIntegerAnomalyFixedFibreEnergy n (-y) := by
    intro y hy
    have hylog : Real.log n ≤ y :=
      le_trans (le_max_left _ _) hy.le
    simpa only [C, b, mul_assoc] using
      thetaIntegerAnomalyFixedFibreEnergy_neg_ge hn hylog
  have hreflect : Integrable (fun y : ℝ => thetaIntegerAnomalyFixedFibreEnergy n (-y)) :=
    henergy.comp_neg
  have htail : IntegrableOn
      (fun y : ℝ => thetaIntegerAnomalyFixedFibreEnergy n (-y)) (Ioi Y) volume :=
    hreflect.integrableOn
  have hexp : IntegrableOn (fun y : ℝ => Real.exp y) (Ioi Y) volume := by
    refine htail.mono' (Real.continuous_exp.aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]
    exact (hdom y hy).trans (hlower y hy)
  exact not_integrableOn_exp_Ioi_any Y hexp

/-- Equivalent Hilbert-space statement: the prime anomaly is not admitted by the source-space
measure itself. -/
theorem integerAnomaly_not_memLp_fixedSource
    {n : ℕ} (hn : 2 ≤ n) :
    ¬ MemLp (integerAnomaly thetaSource n) 2
      (volume.withDensity (realDensity (sourceWeight thetaSource))) := by
  intro hmem
  have hweighted := (memLp_two_withDensity_iff
    (measurable_sourceWeight thetaSource) (sourceWeight_pos thetaSource)).mp hmem
  have hsquare := (memLp_two_iff_integrable_sq_norm hweighted.1).mp hweighted
  apply not_integrable_thetaIntegerAnomalyFixedFibreEnergy hn
  refine hsquare.congr ?_
  filter_upwards with x
  rw [thetaIntegerAnomalyFixedFibreEnergy, norm_mul, sqrtWeight,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (sourceWeight_pos thetaSource x).le, sourceWeight, thetaSource_k]
  ring

end HedenmalmThetaSource

end

end RHTower
