import GaloisForLFunctions.RHTower.RadialPSWFLocalWeakLimit
import GaloisForLFunctions.RHTower.DunsterSigmaComparison
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Filter MeasureTheory Set

namespace RHTower

noncomputable section

/-- Dunster's nonsingular exterior speed after the arclength change
`t = sqrt (x^2 - 1)`. -/
def radialPSWFArclengthSpeed (sigma t : ℝ) : ℝ :=
  Real.sqrt (1 - sigma ^ 2 / (1 + t ^ 2))

/-- Dunster's turning-point-anchored phase in the nonsingular arclength coordinate. -/
def radialPSWFArclengthPhase (sigma t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, radialPSWFArclengthSpeed sigma u

/-- Exact leading squared-Bessel density in arclength coordinates.  Its pushforward by
`x = sqrt (1 + t^2)` is
`(2/pi) cos^2(c xi_sigma(x)+theta) / sqrt((x^2-1)(x^2-sigma^2)) dx`. -/
def radialPSWFLeadingArclengthDensity (c sigma theta t : ℝ) : ℝ :=
  (2 / Real.pi) * (1 + t ^ 2)⁻¹ * (radialPSWFArclengthSpeed sigma t)⁻¹ *
    Real.cos (c * radialPSWFArclengthPhase sigma t + theta) ^ 2

theorem radialPSWFArclengthSpeed_eq (sigma t : ℝ) :
    radialPSWFArclengthSpeed sigma t =
      Real.sqrt (1 - sigma ^ 2 / (1 + t ^ 2)) := rfl

theorem continuous_radialPSWFArclengthSpeed (sigma : ℝ) :
    Continuous (radialPSWFArclengthSpeed sigma) := by
  exact continuous_radialPSWFTurningDensity sigma

theorem radialPSWFArclengthSpeed_mem_Icc (sigma t : ℝ) :
    Real.sqrt (1 - sigma ^ 2) ≤ radialPSWFArclengthSpeed sigma t ∧
      radialPSWFArclengthSpeed sigma t ≤ 1 :=
  radialPSWFTurningDensity_mem_Icc sigma t

theorem radialPSWFArclengthSpeed_pos {sigma t : ℝ} (hsigma : sigma ^ 2 < 1) :
    0 < radialPSWFArclengthSpeed sigma t := by
  have hroot : 0 < Real.sqrt (1 - sigma ^ 2) := Real.sqrt_pos.2 (sub_pos.2 hsigma)
  exact hroot.trans_le (radialPSWFArclengthSpeed_mem_Icc sigma t).1

theorem hasDerivAt_radialPSWFArclengthSpeed {sigma t : ℝ} (hsigma : sigma ^ 2 < 1) :
    HasDerivAt (radialPSWFArclengthSpeed sigma)
      (sigma ^ 2 * t /
        ((1 + t ^ 2) ^ 2 * radialPSWFArclengthSpeed sigma t)) t := by
  have hden : (1 + t ^ 2) ≠ 0 := by positivity
  have harg : 1 - sigma ^ 2 / (1 + t ^ 2) ≠ 0 := by
    have hdenpos : 0 < 1 + t ^ 2 := by positivity
    apply ne_of_gt
    rw [sub_pos, div_lt_one hdenpos]
    nlinarith [sq_nonneg t]
  have hdenDeriv : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * t) t := by
    have hraw := (hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_pow 2 t)
    change HasDerivAt (fun u : ℝ => 1 + u ^ 2)
      (0 + (2 : ℝ) * t ^ (2 - 1)) t at hraw
    norm_num at hraw ⊢
    exact hraw
  have hdiv : HasDerivAt (fun u : ℝ => sigma ^ 2 / (1 + u ^ 2))
      (-2 * sigma ^ 2 * t / (1 + t ^ 2) ^ 2) t := by
    have hraw := (hasDerivAt_const t (sigma ^ 2)).div hdenDeriv hden
    change HasDerivAt (fun u : ℝ => sigma ^ 2 / (1 + u ^ 2))
      ((0 * (1 + t ^ 2) - sigma ^ 2 * (2 * t)) / (1 + t ^ 2) ^ 2) t at hraw
    have hcoef :
        (0 * (1 + t ^ 2) - sigma ^ 2 * (2 * t)) / (1 + t ^ 2) ^ 2 =
          -2 * sigma ^ 2 * t / (1 + t ^ 2) ^ 2 := by ring
    rwa [hcoef] at hraw
  have hbase : HasDerivAt (fun u : ℝ => 1 - sigma ^ 2 / (1 + u ^ 2))
      (2 * sigma ^ 2 * t / (1 + t ^ 2) ^ 2) t := by
    have hraw := (hasDerivAt_const t (1 : ℝ)).sub hdiv
    change HasDerivAt (fun u : ℝ => 1 - sigma ^ 2 / (1 + u ^ 2))
      (0 - (-2 * sigma ^ 2 * t / (1 + t ^ 2) ^ 2)) t at hraw
    have hcoef :
        0 - (-2 * sigma ^ 2 * t / (1 + t ^ 2) ^ 2) =
          2 * sigma ^ 2 * t / (1 + t ^ 2) ^ 2 := by ring
    rwa [hcoef] at hraw
  have hsqrt := hbase.sqrt harg
  convert hsqrt using 1
  · rfl
  · rw [radialPSWFArclengthSpeed]
    field_simp

def radialPSWFArclengthSpeedDeriv (sigma t : ℝ) : ℝ :=
  sigma ^ 2 * t /
    ((1 + t ^ 2) ^ 2 * radialPSWFArclengthSpeed sigma t)

theorem continuous_radialPSWFArclengthSpeedDeriv {sigma : ℝ} (hsigma : sigma ^ 2 < 1) :
    Continuous (radialPSWFArclengthSpeedDeriv sigma) := by
  unfold radialPSWFArclengthSpeedDeriv
  exact (continuous_const.mul continuous_id).div
    (((continuous_const.add (continuous_id.pow 2)).pow 2).mul
      (continuous_radialPSWFArclengthSpeed sigma))
    (fun t => mul_ne_zero (pow_ne_zero _ (by positivity))
      (radialPSWFArclengthSpeed_pos hsigma).ne')

theorem radialPSWFArclengthSpeedDeriv_nonneg {sigma t : ℝ}
    (hsigma : sigma ^ 2 < 1) (ht : 0 ≤ t) :
    0 ≤ radialPSWFArclengthSpeedDeriv sigma t := by
  unfold radialPSWFArclengthSpeedDeriv
  exact div_nonneg (mul_nonneg (sq_nonneg sigma) ht)
    (mul_nonneg (sq_nonneg (1 + t ^ 2))
      (radialPSWFArclengthSpeed_pos hsigma).le)

theorem hasDerivAt_radialPSWFArclengthPhase (sigma t : ℝ) :
    HasDerivAt (radialPSWFArclengthPhase sigma)
      (radialPSWFArclengthSpeed sigma t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((continuous_radialPSWFArclengthSpeed sigma).intervalIntegrable 0 t)
    (continuous_radialPSWFArclengthSpeed sigma).stronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_radialPSWFArclengthSpeed sigma).continuousAt

theorem radialPSWFArclengthPhase_eq_turningPhase {sigma t : ℝ} (ht : 0 ≤ t) :
    radialPSWFArclengthPhase sigma t =
      radialPSWFTurningPhase sigma (Real.sqrt (1 + t ^ 2)) := by
  rw [radialPSWFArclengthPhase, radialPSWFTurningPhase]
  have hnonneg : 0 ≤ 1 + t ^ 2 := by positivity
  rw [Real.sq_sqrt hnonneg, show 1 + t ^ 2 - 1 = t ^ 2 by ring,
    Real.sqrt_sq ht]
  rfl

theorem radialPSWFLeadingArclengthDensity_nonneg
    {c sigma theta t : ℝ} (hsigma : sigma ^ 2 < 1) :
    0 ≤ radialPSWFLeadingArclengthDensity c sigma theta t := by
  unfold radialPSWFLeadingArclengthDensity
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (inv_nonneg.2 (radialPSWFArclengthSpeed_pos hsigma).le)) (sq_nonneg _)

theorem radialPSWFArclengthSpeed_inv_le_two
    {sigma t : ℝ} (hsigma : sigma ^ 2 ≤ 3 / 4) :
    (radialPSWFArclengthSpeed sigma t)⁻¹ ≤ 2 := by
  have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - sigma ^ 2) := by
    have h := Real.sqrt_le_sqrt (show (1 / 2 : ℝ) ^ 2 ≤ 1 - sigma ^ 2 by nlinarith)
    simpa using h
  have hspeed : (1 / 2 : ℝ) ≤ radialPSWFArclengthSpeed sigma t :=
    hroot.trans (radialPSWFArclengthSpeed_mem_Icc sigma t).1
  have hpos : 0 < radialPSWFArclengthSpeed sigma t := lt_of_lt_of_le (by norm_num) hspeed
  simpa only [one_div] using
    (one_div_le hpos (by norm_num : (0 : ℝ) < 2)).2 hspeed

theorem abs_radialPSWFArclengthSpeed_inv_sub_one_le
    {sigma t : ℝ} (hsigma : sigma ^ 2 ≤ 3 / 4) :
    |(radialPSWFArclengthSpeed sigma t)⁻¹ - 1| ≤ 2 * sigma ^ 2 := by
  have hsigma1 : sigma ^ 2 < 1 := lt_of_le_of_lt hsigma (by norm_num)
  have hqpos : 0 < radialPSWFArclengthSpeed sigma t :=
    radialPSWFArclengthSpeed_pos hsigma1
  have hq0 : 0 ≤ radialPSWFArclengthSpeed sigma t := hqpos.le
  have hq1 : radialPSWFArclengthSpeed sigma t ≤ 1 :=
    (radialPSWFArclengthSpeed_mem_Icc sigma t).2
  have hqhalf : (1 / 2 : ℝ) ≤ radialPSWFArclengthSpeed sigma t := by
    have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - sigma ^ 2) := by
      have h := Real.sqrt_le_sqrt (show (1 / 2 : ℝ) ^ 2 ≤ 1 - sigma ^ 2 by nlinarith)
      simpa using h
    exact hroot.trans (radialPSWFArclengthSpeed_mem_Icc sigma t).1
  have hdenpos : 0 < 1 + t ^ 2 := by positivity
  have hratio : sigma ^ 2 / (1 + t ^ 2) ≤ sigma ^ 2 := by
    rw [div_le_iff₀ hdenpos]
    nlinarith [sq_nonneg sigma, sq_nonneg t]
  have harg : 0 ≤ 1 - sigma ^ 2 / (1 + t ^ 2) := by
    nlinarith [sq_nonneg sigma]
  have hqSq : radialPSWFArclengthSpeed sigma t ^ 2 =
      1 - sigma ^ 2 / (1 + t ^ 2) := by
    rw [radialPSWFArclengthSpeed, Real.sq_sqrt harg]
  have honeSub : 1 - radialPSWFArclengthSpeed sigma t ≤ sigma ^ 2 := by
    nlinarith [sq_nonneg (radialPSWFArclengthSpeed sigma t)]
  have hid : (radialPSWFArclengthSpeed sigma t)⁻¹ - 1 =
      (1 - radialPSWFArclengthSpeed sigma t) /
        radialPSWFArclengthSpeed sigma t := by
    field_simp
  have hnonneg : 0 ≤ (radialPSWFArclengthSpeed sigma t)⁻¹ - 1 := by
    rw [hid]
    exact div_nonneg (sub_nonneg.mpr hq1) hq0
  rw [abs_of_nonneg hnonneg, hid, div_le_iff₀ hqpos]
  nlinarith [sq_nonneg sigma]

/-- Uniform endpoint-and-tail envelope for the exact leading squared-Bessel density. -/
theorem radialPSWFLeadingArclengthDensity_le_integrableEnvelope
    {c sigma theta t : ℝ} (hsigma : sigma ^ 2 ≤ 3 / 4) :
    radialPSWFLeadingArclengthDensity c sigma theta t
      ≤ (4 / Real.pi) * (1 + t ^ 2)⁻¹ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hinv := radialPSWFArclengthSpeed_inv_le_two (t := t) hsigma
  have hcos : Real.cos (c * radialPSWFArclengthPhase sigma t + theta) ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_cos (c * radialPSWFArclengthPhase sigma t + theta),
      Real.cos_le_one (c * radialPSWFArclengthPhase sigma t + theta)]
  have hbase : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
  unfold radialPSWFLeadingArclengthDensity
  calc
    (2 / Real.pi) * (1 + t ^ 2)⁻¹ * (radialPSWFArclengthSpeed sigma t)⁻¹ *
          Real.cos (c * radialPSWFArclengthPhase sigma t + theta) ^ 2
        ≤ (2 / Real.pi) * (1 + t ^ 2)⁻¹ * 2 * 1 := by
          gcongr
    _ = (4 / Real.pi) * (1 + t ^ 2)⁻¹ := by ring

theorem continuous_radialPSWFArclengthPhase (sigma : ℝ) :
    Continuous (radialPSWFArclengthPhase sigma) := by
  rw [continuous_iff_continuousAt]
  exact fun t => (hasDerivAt_radialPSWFArclengthPhase sigma t).continuousAt

theorem continuous_radialPSWFLeadingArclengthDensity
    {c sigma theta : ℝ} (hsigma : sigma ^ 2 < 1) :
    Continuous (radialPSWFLeadingArclengthDensity c sigma theta) := by
  unfold radialPSWFLeadingArclengthDensity
  have hden : Continuous (fun t : ℝ => (1 + t ^ 2)⁻¹) :=
    (continuous_const.add (continuous_id.pow 2)).inv₀
      (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 + t ^ 2))
  have hspeed : Continuous (fun t : ℝ => (radialPSWFArclengthSpeed sigma t)⁻¹) :=
    (continuous_radialPSWFArclengthSpeed sigma).inv₀
      (fun t => (radialPSWFArclengthSpeed_pos hsigma).ne')
  exact (((continuous_const.mul hden).mul hspeed).mul
    ((Real.continuous_cos.comp
      (continuous_const.mul (continuous_radialPSWFArclengthPhase sigma) |>.add
        continuous_const)).pow 2))

/-- On a compact arclength interval, replacing the exact Liouville amplitude by its free value
costs at most a uniform `O(sigma^2)` error. -/
theorem abs_integral_weight_mul_leadingArclengthDensity_sub_free_le
    {a b c sigma theta M : ℝ} (hab : a ≤ b) (hsigma : sigma ^ 2 ≤ 3 / 4)
    {w : ℝ → ℝ} (hwc : ContinuousOn w (Icc a b))
    (hM : 0 ≤ M) (hwM : ∀ x ∈ Icc a b, |w x| ≤ M) :
    |(∫ t in a..b, w t * radialPSWFLeadingArclengthDensity c sigma theta t) -
      ∫ t in a..b,
        (2 / Real.pi) * w t * (1 + t ^ 2)⁻¹ *
          Real.cos (c * radialPSWFArclengthPhase sigma t + theta) ^ 2|
      ≤ ((4 / Real.pi) * M * sigma ^ 2) * |b - a| := by
  have hsigma1 : sigma ^ 2 < 1 := lt_of_le_of_lt hsigma (by norm_num)
  have hleadCont : ContinuousOn
      (fun t => w t * radialPSWFLeadingArclengthDensity c sigma theta t) (Icc a b) :=
    hwc.mul (continuous_radialPSWFLeadingArclengthDensity hsigma1).continuousOn
  have hfreeCont : ContinuousOn
      (fun t => (2 / Real.pi) * w t * (1 + t ^ 2)⁻¹ *
        Real.cos (c * radialPSWFArclengthPhase sigma t + theta) ^ 2) (Icc a b) := by
    have hinv : Continuous (fun t : ℝ => (1 + t ^ 2)⁻¹) :=
      (continuous_const.add (continuous_id.pow 2)).inv₀
        (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 + t ^ 2))
    exact (((continuousOn_const.mul hwc).mul hinv.continuousOn).mul
      ((Real.continuous_cos.comp
        ((continuous_const.mul (continuous_radialPSWFArclengthPhase sigma)).add
          continuous_const)).pow 2).continuousOn)
  have hleadInt : IntervalIntegrable
      (fun t => w t * radialPSWFLeadingArclengthDensity c sigma theta t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le hab]
  have hfreeInt : IntervalIntegrable
      (fun t => (2 / Real.pi) * w t * (1 + t ^ 2)⁻¹ *
        Real.cos (c * radialPSWFArclengthPhase sigma t + theta) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le hab]
  rw [← intervalIntegral.integral_sub hleadInt hfreeInt, ← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  rw [uIoc_of_le hab] at ht
  have htI : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
  have heq :
      w t * radialPSWFLeadingArclengthDensity c sigma theta t -
          (2 / Real.pi) * w t * (1 + t ^ 2)⁻¹ *
            Real.cos (c * radialPSWFArclengthPhase sigma t + theta) ^ 2 =
        (2 / Real.pi) * w t * (1 + t ^ 2)⁻¹ *
          ((radialPSWFArclengthSpeed sigma t)⁻¹ - 1) *
            Real.cos (c * radialPSWFArclengthPhase sigma t + theta) ^ 2 := by
    unfold radialPSWFLeadingArclengthDensity
    ring
  rw [heq, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul]
  have hpi : 0 ≤ 2 / Real.pi := by positivity
  have hinv0 : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
  have hinv1 : (1 + t ^ 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    nlinarith [sq_nonneg t]
  have hcos0 : 0 ≤ Real.cos (c * radialPSWFArclengthPhase sigma t + theta) ^ 2 := sq_nonneg _
  have hcos1 : Real.cos (c * radialPSWFArclengthPhase sigma t + theta) ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_cos (c * radialPSWFArclengthPhase sigma t + theta),
      Real.cos_le_one (c * radialPSWFArclengthPhase sigma t + theta)]
  rw [abs_of_nonneg hpi, abs_of_nonneg hinv0, abs_of_nonneg hcos0]
  calc
    2 / Real.pi * |w t| * (1 + t ^ 2)⁻¹ *
          |(radialPSWFArclengthSpeed sigma t)⁻¹ - 1| *
            Real.cos (c * radialPSWFArclengthPhase sigma t + theta) ^ 2
        ≤ 2 / Real.pi * M * 1 * (2 * sigma ^ 2) * 1 := by
          gcongr
          · exact hwM t htI
          · exact abs_radialPSWFArclengthSpeed_inv_sub_one_le hsigma
    _ = (4 / Real.pi) * M * sigma ^ 2 := by ring

theorem integrable_radialPSWFLeadingArclengthDensity
    {c sigma theta : ℝ} (hsigma : sigma ^ 2 ≤ 3 / 4) :
    Integrable (radialPSWFLeadingArclengthDensity c sigma theta) := by
  have hsigma' : sigma ^ 2 < 1 := lt_of_le_of_lt hsigma (by norm_num)
  have hmajor : Integrable (fun t : ℝ => (4 / Real.pi) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (4 / Real.pi)
  exact hmajor.mono'
    (continuous_radialPSWFLeadingArclengthDensity hsigma').aestronglyMeasurable
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (radialPSWFLeadingArclengthDensity_nonneg hsigma')]
      exact radialPSWFLeadingArclengthDensity_le_integrableEnvelope hsigma)

theorem integral_Ioc_radialPSWFLeadingArclengthDensity_le
    {c sigma theta eta : ℝ} (hsigma : sigma ^ 2 ≤ 3 / 4) (heta : 0 ≤ eta) :
    ∫ t in Ioc (0 : ℝ) eta, radialPSWFLeadingArclengthDensity c sigma theta t
      ≤ (4 / Real.pi) * eta := by
  have hlead := integrable_radialPSWFLeadingArclengthDensity
    (c := c) (theta := theta) hsigma
  have hconst : IntegrableOn (fun _ : ℝ => 4 / Real.pi) (Ioc (0 : ℝ) eta) :=
    integrableOn_const measure_Ioc_lt_top.ne
  calc
    ∫ t in Ioc (0 : ℝ) eta, radialPSWFLeadingArclengthDensity c sigma theta t
        ≤ ∫ _t in Ioc (0 : ℝ) eta, (4 / Real.pi) := by
          apply setIntegral_mono_on hlead.integrableOn hconst measurableSet_Ioc
          intro t _
          calc
            radialPSWFLeadingArclengthDensity c sigma theta t
                ≤ (4 / Real.pi) * (1 + t ^ 2)⁻¹ :=
              radialPSWFLeadingArclengthDensity_le_integrableEnvelope hsigma
            _ ≤ 4 / Real.pi := by
              have hpi : 0 ≤ 4 / Real.pi := by positivity
              have hinv : (1 + t ^ 2)⁻¹ ≤ 1 := by
                rw [inv_le_one₀ (by positivity)]
                nlinarith [sq_nonneg t]
              simpa using mul_le_of_le_one_right hpi hinv
    _ = (4 / Real.pi) * eta := by
          rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le heta]
          ring

theorem integral_Ioi_radialPSWFLeadingArclengthDensity_le
    {c sigma theta R : ℝ} (hsigma : sigma ^ 2 ≤ 3 / 4) :
    ∫ t in Ioi R, radialPSWFLeadingArclengthDensity c sigma theta t
      ≤ (4 / Real.pi) * (Real.pi / 2 - Real.arctan R) := by
  have hlead := integrable_radialPSWFLeadingArclengthDensity
    (c := c) (theta := theta) hsigma
  have hmajor : Integrable (fun t : ℝ => (4 / Real.pi) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (4 / Real.pi)
  calc
    ∫ t in Ioi R, radialPSWFLeadingArclengthDensity c sigma theta t
        ≤ ∫ t in Ioi R, (4 / Real.pi) * (1 + t ^ 2)⁻¹ := by
          apply setIntegral_mono_on hlead.integrableOn hmajor.integrableOn measurableSet_Ioi
          intro t _
          exact radialPSWFLeadingArclengthDensity_le_integrableEnvelope hsigma
    _ = (4 / Real.pi) * (Real.pi / 2 - Real.arctan R) := by
          rw [integral_const_mul, integral_Ioi_inv_one_add_sq]

/-- Compact-interval oscillatory averaging in Dunster's nonsingular arclength coordinate. -/
theorem tendsto_integral_weight_mul_cos_sq_radialArclengthPhase_add
    {ι : Type*} {l : Filter ι} {c sigma : ι → ℝ} {theta a b : ℝ}
    (hc : Tendsto c l atTop) (hsigma : Tendsto sigma l (nhds 0))
    (hab : a ≤ b) (ha : 0 ≤ a) {w w' : ℝ → ℝ}
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x)
    (hw'c : ContinuousOn w' (Icc a b)) :
    Tendsto (fun i =>
      ∫ t in a..b,
        w t * Real.cos
          (c i * radialPSWFArclengthPhase (sigma i) t + theta) ^ 2)
      l (nhds ((1 / 2) * ∫ t in a..b, w t)) := by
  let B := |w b| + |w a| + ∫ t in a..b, |w' t|
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have hint : 0 ≤ ∫ t in a..b, |w' t| :=
      intervalIntegral.integral_nonneg hab (fun x _ => abs_nonneg _)
    positivity
  have hsigma2 : Tendsto (fun i => sigma i ^ 2) l (nhds 0) := by
    simpa using hsigma.pow 2
  have hsigmaSmall : ∀ᶠ i in l, sigma i ^ 2 < 3 / 4 :=
    hsigma2.eventually (eventually_lt_nhds (by norm_num))
  have hmajor : Tendsto (fun i => 2 * B / c i) l (nhds 0) := by
    have hinv : Tendsto (fun i => (c i)⁻¹) l (nhds 0) := hc.inv_tendsto_atTop
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (2 * B)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using squeeze_zero'
    (Eventually.of_forall fun i => abs_nonneg _)
    (by
      filter_upwards [hsigmaSmall, hc.eventually (eventually_gt_atTop (0 : ℝ))]
        with i hsig hci
      have hsig1 : sigma i ^ 2 < 1 := lt_trans hsig (by norm_num)
      have hmain := abs_integral_weight_mul_cos_sq_sub_half_le
        (φ := fun t => c i * radialPSWFArclengthPhase (sigma i) t + theta)
        (φ' := fun t => c i * radialPSWFArclengthSpeed (sigma i) t)
        (φ'' := fun t => c i * radialPSWFArclengthSpeedDeriv (sigma i) t)
        hab (show 0 < c i / 2 by positivity) hw hw'c
        (fun x _ =>
          ((hasDerivAt_radialPSWFArclengthPhase (sigma i) x).const_mul (c i)).add_const theta)
        (fun x _ =>
          ((hasDerivAt_radialPSWFArclengthSpeed hsig1).const_mul (c i)))
        ((continuous_const.mul
          (continuous_radialPSWFArclengthSpeedDeriv hsig1)).continuousOn)
        (fun x hx => mul_nonneg hci.le
          (radialPSWFArclengthSpeedDeriv_nonneg hsig1 (ha.trans hx.1)))
        (fun x _ => by
          have hfloor : (1 / 2 : ℝ) ≤ radialPSWFArclengthSpeed (sigma i) x := by
            have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - sigma i ^ 2) := by
              have h := Real.sqrt_le_sqrt
                (show (1 / 2 : ℝ) ^ 2 ≤ 1 - sigma i ^ 2 by nlinarith)
              simpa using h
            exact hroot.trans (radialPSWFArclengthSpeed_mem_Icc (sigma i) x).1
          rw [abs_of_nonneg (mul_nonneg hci.le
            (radialPSWFArclengthSpeed_pos hsig1).le)]
          nlinarith)
      calc
        |(∫ t in a..b,
              w t * Real.cos
                (c i * radialPSWFArclengthPhase (sigma i) t + theta) ^ 2) -
            (1 / 2) * ∫ t in a..b, w t|
            ≤ B / (c i / 2) := hmain
        _ = 2 * B / c i := by field_simp)
    hmajor

/-- Compact-interval weak limit for the literal leading Dunster squared-Bessel density, including
the varying Liouville amplitude. -/
theorem tendsto_integral_weight_mul_radialPSWFLeadingArclengthDensity
    {ι : Type*} {l : Filter ι} {c sigma : ι → ℝ} {theta a b : ℝ}
    (hc : Tendsto c l atTop) (hsigma : Tendsto sigma l (nhds 0))
    (hab : a ≤ b) (ha : 0 ≤ a) {w w' : ℝ → ℝ}
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x)
    (hw'c : ContinuousOn w' (Icc a b)) :
    Tendsto (fun i =>
      ∫ t in a..b, w t *
        radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t)
      l (nhds (∫ t in a..b, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹)) := by
  let p : ℝ → ℝ := fun t => w t * (1 + t ^ 2)⁻¹
  let p' : ℝ → ℝ := fun t =>
    w' t * (1 + t ^ 2)⁻¹ + w t * (-2 * t / (1 + t ^ 2) ^ 2)
  have hwc : ContinuousOn w (Icc a b) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x := by
    intro x hx
    have hden : 1 + x ^ 2 ≠ 0 := by positivity
    have hdenDeriv : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x := by
      have hraw := (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_pow 2 x)
      change HasDerivAt (fun t : ℝ => 1 + t ^ 2)
        (0 + (2 : ℝ) * x ^ (2 - 1)) x at hraw
      norm_num at hraw ⊢
      exact hraw
    have hinv : HasDerivAt (fun t : ℝ => (1 + t ^ 2)⁻¹)
        (-2 * x / (1 + x ^ 2) ^ 2) x := by
      have hraw := hdenDeriv.inv hden
      change HasDerivAt (fun t : ℝ => (1 + t ^ 2)⁻¹)
        (-(2 * x) / (1 + x ^ 2) ^ 2) x at hraw
      simpa only [neg_mul] using hraw
    exact (hw x hx).mul hinv
  have hp'c : ContinuousOn p' (Icc a b) := by
    have hinv : Continuous (fun t : ℝ => (1 + t ^ 2)⁻¹) :=
      (continuous_const.add (continuous_id.pow 2)).inv₀
        (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 + t ^ 2))
    have hden2 : Continuous (fun t : ℝ => (1 + t ^ 2) ^ 2) :=
      (continuous_const.add (continuous_id.pow 2)).pow 2
    have hfrac : Continuous (fun t : ℝ => -2 * t / (1 + t ^ 2) ^ 2) :=
      (continuous_const.mul continuous_id).div hden2
        (fun t => pow_ne_zero _ (ne_of_gt (by positivity : (0 : ℝ) < 1 + t ^ 2)))
    exact (hw'c.mul hinv.continuousOn).add (hwc.mul hfrac.continuousOn)
  have hfreeRaw := tendsto_integral_weight_mul_cos_sq_radialArclengthPhase_add
    (theta := theta) hc hsigma hab ha hp hp'c
  have hfree := hfreeRaw.const_mul (2 / Real.pi)
  have hfree' : Tendsto (fun i =>
      ∫ t in a..b,
        (2 / Real.pi) * w t * (1 + t ^ 2)⁻¹ *
          Real.cos (c i * radialPSWFArclengthPhase (sigma i) t + theta) ^ 2)
      l (nhds (∫ t in a..b, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹)) := by
    convert hfree using 1
    · funext i
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp [p]
      ring
    · congr 1
      calc
        ∫ t in a..b, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹
            = (1 / Real.pi) * ∫ t in a..b, p t := by
              rw [← intervalIntegral.integral_const_mul]
              apply intervalIntegral.integral_congr
              intro t _
              dsimp [p]
              ring
        _ = 2 / Real.pi * (1 / 2 * ∫ t in a..b, p t) := by ring
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hwc
  have hM0 : 0 ≤ M :=
    (norm_nonneg (w a)).trans (hM a ⟨le_rfl, hab⟩)
  have hsigma2 : Tendsto (fun i => sigma i ^ 2) l (nhds 0) := by
    simpa using hsigma.pow 2
  have hsigmaSmall : ∀ᶠ i in l, sigma i ^ 2 ≤ 3 / 4 :=
    (hsigma2.eventually (eventually_lt_nhds (by norm_num))).mono fun _ hi => hi.le
  have hboundTend : Tendsto
      (fun i => ((4 / Real.pi) * M * sigma i ^ 2) * |b - a|) l (nhds 0) := by
    simpa only [mul_zero, zero_mul] using
      ((hsigma2.const_mul ((4 / Real.pi) * M)).mul_const |b - a|)
  have hdiff : Tendsto (fun i =>
      (∫ t in a..b, w t *
          radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t) -
        ∫ t in a..b,
          (2 / Real.pi) * w t * (1 + t ^ 2)⁻¹ *
            Real.cos (c i * radialPSWFArclengthPhase (sigma i) t + theta) ^ 2)
      l (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero, Real.norm_eq_abs] using squeeze_zero'
      (Eventually.of_forall fun i => abs_nonneg _)
      (by
        filter_upwards [hsigmaSmall] with i hi
        exact abs_integral_weight_mul_leadingArclengthDensity_sub_free_le
          hab hi hwc hM0 (fun x hx => by simpa [Real.norm_eq_abs] using hM x hx))
      hboundTend
  have hadd := hdiff.add hfree'
  simpa only [sub_add_cancel, zero_add] using hadd

/-- Tail weak limit of the literal leading Dunster density against bounded `C¹` tests.  Compact
oscillatory convergence is glued to the explicit uniform endpoint/tail envelope. -/
theorem tendsto_integral_Ioi_weight_mul_radialPSWFLeadingArclengthDensity_of_nonneg
    {ι : Type*} {l : Filter ι} {c sigma : ι → ℝ} {theta a : ℝ}
    (hc : Tendsto c l atTop) (hsigma : Tendsto sigma l (nhds 0))
    (ha : 0 ≤ a) {w w' : ℝ → ℝ} (hw : ∀ x, HasDerivAt w (w' x) x) (hw'c : Continuous w')
    {M : ℝ} (hM0 : 0 ≤ M) (hwM : ∀ x, |w x| ≤ M) :
    Tendsto (fun i =>
      ∫ t in Ioi a, w t *
        radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t)
      l (nhds (∫ t in Ioi a,
        (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹)) := by
  have hwc : Continuous w := by
    rw [continuous_iff_continuousAt]
    exact fun x => (hw x).continuousAt
  have htargetInt : Integrable (fun t : ℝ => (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹) := by
    apply integrable_inv_one_add_sq.bdd_mul
    · exact (continuous_const.mul hwc).aestronglyMeasurable
    · exact Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.pi)]
        exact mul_le_mul_of_nonneg_left (hwM t) (by positivity)
  have hsigma2 : Tendsto (fun i => sigma i ^ 2) l (nhds 0) := by
    simpa using hsigma.pow 2
  have hsigmaSmall : ∀ᶠ i in l, sigma i ^ 2 ≤ 3 / 4 :=
    (hsigma2.eventually (eventually_lt_nhds (by norm_num))).mono fun _ hi => hi.le
  rw [Metric.tendsto_nhds]
  intro eps heps
  have htailTend : Tendsto
      (fun R : ℝ => (5 * M / Real.pi) * (Real.pi / 2 - Real.arctan R))
      atTop (nhds 0) := by
    have harctan : Tendsto Real.arctan atTop (nhds (Real.pi / 2)) :=
      tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop
    have hsub : Tendsto (fun R : ℝ => Real.pi / 2 - Real.arctan R)
        atTop (nhds (Real.pi / 2 - Real.pi / 2)) :=
      tendsto_const_nhds.sub harctan
    simpa only [sub_self, mul_zero] using hsub.const_mul (5 * M / Real.pi)
  have htailSmall : ∀ᶠ R : ℝ in atTop,
      (5 * M / Real.pi) * (Real.pi / 2 - Real.arctan R) < eps / 2 :=
    htailTend.eventually (eventually_lt_nhds (half_pos heps))
  obtain ⟨R, hRtail, hRa⟩ :=
    (htailSmall.and (eventually_ge_atTop a)).exists
  have hlocal := tendsto_integral_weight_mul_radialPSWFLeadingArclengthDensity
    (theta := theta) hc hsigma hRa ha
    (fun x _ => hw x) hw'c.continuousOn
  have hlocalEv : ∀ᶠ i in l,
      dist (∫ t in a..R,
          w t * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t)
        (∫ t in a..R, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹) < eps / 2 :=
    (Metric.tendsto_nhds.mp hlocal) (eps / 2) (half_pos heps)
  filter_upwards [hsigmaSmall, hlocalEv] with i hi hloc
  have hlead := integrable_radialPSWFLeadingArclengthDensity
    (c := c i) (theta := theta) hi
  have hfiniteInt : Integrable (fun t : ℝ =>
      w t * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t) := by
    apply hlead.bdd_mul hwc.aestronglyMeasurable
    exact Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hwM t
  have hdisj : Disjoint (Ioc a R) (Ioi R) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy
  have hunion : Ioc a R ∪ Ioi R = Ioi a := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact lt_of_le_of_lt hRa hx
    · intro hx
      exact le_or_gt x R |>.elim (fun hxR => Or.inl ⟨hx, hxR⟩) Or.inr
  have hsplitFinite :
      ∫ t in Ioi a,
          w t * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t =
        (∫ t in a..R,
          w t * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t) +
        ∫ t in Ioi R,
          w t * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t := by
    rw [intervalIntegral.integral_of_le hRa]
    rw [← hunion]
    exact setIntegral_union₀ hdisj.aedisjoint measurableSet_Ioi.nullMeasurableSet
      hfiniteInt.integrableOn hfiniteInt.integrableOn
  have hsplitTarget :
      ∫ t in Ioi a, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹ =
        (∫ t in a..R, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹) +
        ∫ t in Ioi R, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹ := by
    rw [intervalIntegral.integral_of_le hRa]
    rw [← hunion]
    exact setIntegral_union₀ hdisj.aedisjoint measurableSet_Ioi.nullMeasurableSet
      htargetInt.integrableOn htargetInt.integrableOn
  have htailFinite :
      |∫ t in Ioi R,
          w t * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t|
        ≤ M * (4 / Real.pi) * (Real.pi / 2 - Real.arctan R) := by
    have hmajorInt : IntegrableOn (fun t : ℝ =>
        M * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t) (Ioi R) := by
      exact (hlead.const_mul M).integrableOn
    have hnorm := norm_integral_le_of_norm_le
      (f := fun t : ℝ =>
        w t * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t)
      hmajorInt
      (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (radialPSWFLeadingArclengthDensity_nonneg
            (lt_of_le_of_lt hi (by norm_num)))]
        exact mul_le_mul_of_nonneg_right (hwM t)
          (radialPSWFLeadingArclengthDensity_nonneg
            (lt_of_le_of_lt hi (by norm_num))))
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ t in Ioi R,
          w t * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t‖
          ≤ ∫ t in Ioi R,
              M * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t := hnorm
      _ = M * ∫ t in Ioi R,
          radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t := by
            rw [integral_const_mul]
      _ ≤ M * ((4 / Real.pi) * (Real.pi / 2 - Real.arctan R)) :=
            mul_le_mul_of_nonneg_left
              (integral_Ioi_radialPSWFLeadingArclengthDensity_le hi) hM0
      _ = M * (4 / Real.pi) * (Real.pi / 2 - Real.arctan R) := by ring
  have htailTarget :
      |∫ t in Ioi R, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹|
        ≤ (M / Real.pi) * (Real.pi / 2 - Real.arctan R) := by
    have hmajorInt : IntegrableOn (fun t : ℝ => (M / Real.pi) * (1 + t ^ 2)⁻¹)
        (Ioi R) := (integrable_inv_one_add_sq.const_mul (M / Real.pi)).integrableOn
    have hnorm := norm_integral_le_of_norm_le
      (f := fun t : ℝ => (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹)
      hmajorInt
      (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.pi),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + t ^ 2)⁻¹)]
        calc
          1 / Real.pi * |w t| * (1 + t ^ 2)⁻¹
              ≤ 1 / Real.pi * M * (1 + t ^ 2)⁻¹ := by gcongr; exact hwM t
          _ = M / Real.pi * (1 + t ^ 2)⁻¹ := by ring)
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ t in Ioi R, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹‖
          ≤ ∫ t in Ioi R, (M / Real.pi) * (1 + t ^ 2)⁻¹ := hnorm
      _ = (M / Real.pi) * (Real.pi / 2 - Real.arctan R) := by
            rw [integral_const_mul, integral_Ioi_inv_one_add_sq]
  rw [Real.dist_eq, hsplitFinite, hsplitTarget]
  calc
    |((∫ t in a..R,
          w t * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t) +
        ∫ t in Ioi R,
          w t * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t) -
      ((∫ t in a..R, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹) +
        ∫ t in Ioi R, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹)|
        ≤ |(∫ t in a..R,
              w t * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t) -
            ∫ t in a..R, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹| +
          |∫ t in Ioi R,
              w t * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t| +
          |∫ t in Ioi R, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹| := by
            calc
              |_ - _| = |((∫ t in a..R,
                    w t * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t) -
                  ∫ t in a..R, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹) +
                ((∫ t in Ioi R,
                    w t * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t) -
                  ∫ t in Ioi R, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹)| := by ring_nf
              _ ≤ |(∫ t in a..R,
                    w t * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t) -
                  ∫ t in a..R, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹| +
                |(∫ t in Ioi R,
                    w t * radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t) -
                  ∫ t in Ioi R, (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹| := abs_add_le _ _
              _ ≤ _ := by
                have htailTriangle :
                    |(∫ t in Ioi R,
                        w t * radialPSWFLeadingArclengthDensity
                          (c i) (sigma i) theta t) -
                      ∫ t in Ioi R,
                        (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹| ≤
                    |∫ t in Ioi R,
                        w t * radialPSWFLeadingArclengthDensity
                          (c i) (sigma i) theta t| +
                      |∫ t in Ioi R,
                        (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹| := abs_sub _ _
                linarith
    _ < eps / 2 +
        M * (4 / Real.pi) * (Real.pi / 2 - Real.arctan R) +
        (M / Real.pi) * (Real.pi / 2 - Real.arctan R) := by
          rw [Real.dist_eq] at hloc
          linarith
    _ = eps / 2 + (5 * M / Real.pi) * (Real.pi / 2 - Real.arctan R) := by ring
    _ < eps / 2 + eps / 2 := by linarith
    _ = eps := by ring

/-- Global weak limit of the literal leading Dunster density against bounded `C¹` tests. -/
theorem tendsto_integral_Ioi_weight_mul_radialPSWFLeadingArclengthDensity
    {ι : Type*} {l : Filter ι} {c sigma : ι → ℝ} {theta : ℝ}
    (hc : Tendsto c l atTop) (hsigma : Tendsto sigma l (nhds 0))
    {w w' : ℝ → ℝ} (hw : ∀ x, HasDerivAt w (w' x) x) (hw'c : Continuous w')
    {M : ℝ} (hM0 : 0 ≤ M) (hwM : ∀ x, |w x| ≤ M) :
    Tendsto (fun i =>
      ∫ t in Ioi (0 : ℝ), w t *
        radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t)
      l (nhds (∫ t in Ioi (0 : ℝ),
        (1 / Real.pi) * w t * (1 + t ^ 2)⁻¹)) :=
  tendsto_integral_Ioi_weight_mul_radialPSWFLeadingArclengthDensity_of_nonneg
    (a := 0) hc hsigma le_rfl hw hw'c hM0 hwM

/-- Every nonnegative arclength tail of the literal leading Dunster density converges to its exact
arctangent mass. -/
theorem tendsto_integral_Ioi_radialPSWFLeadingArclengthDensity
    {ι : Type*} {l : Filter ι} {c sigma : ι → ℝ} {theta a : ℝ}
    (hc : Tendsto c l atTop) (hsigma : Tendsto sigma l (nhds 0)) (ha : 0 ≤ a) :
    Tendsto (fun i => ∫ t in Ioi a,
        radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t)
      l (nhds ((1 / Real.pi) * (Real.pi / 2 - Real.arctan a))) := by
  have h :=
    tendsto_integral_Ioi_weight_mul_radialPSWFLeadingArclengthDensity_of_nonneg
      (theta := theta) hc hsigma ha (w := fun _ => 1) (w' := fun _ => 0)
      (fun x => hasDerivAt_const x 1) continuous_const (M := 1) zero_le_one
      (fun _ => by norm_num)
  simpa only [one_mul, mul_one, integral_const_mul, integral_Ioi_inv_one_add_sq] using h

/-- The arclength threshold corresponding to the radial dilation threshold `k` converts the
limiting Cauchy tail exactly into the paper's arcsine tail. -/
theorem pi_div_two_sub_arctan_sqrt_sq_sub_one
    {k : ℝ} (hk : 1 ≤ k) :
    Real.pi / 2 - Real.arctan (Real.sqrt (k ^ 2 - 1)) =
      Real.arcsin (1 / k) := by
  rcases eq_or_lt_of_le hk with rfl | hk1
  · norm_num [Real.arcsin_one]
  have hk0 : 0 < k := one_pos.trans hk1
  have harg : 0 < k ^ 2 - 1 := by nlinarith
  have hsqrt : Real.sqrt (1 - (1 / k) ^ 2) = Real.sqrt (k ^ 2 - 1) / k := by
    rw [show 1 - (1 / k) ^ 2 = (k ^ 2 - 1) / k ^ 2 by field_simp]
    rw [Real.sqrt_div harg.le, Real.sqrt_sq_eq_abs, abs_of_pos hk0]
  have hmem : (1 / k : ℝ) ∈ Ioo (-(1 : ℝ)) 1 := by
    constructor
    · have : 0 < (1 / k : ℝ) := by positivity
      linarith
    · exact (div_lt_one hk0).2 hk1
  rw [Real.arcsin_eq_arctan hmem, hsqrt]
  have hquot : (1 / k) / (Real.sqrt (k ^ 2 - 1) / k) =
      (Real.sqrt (k ^ 2 - 1))⁻¹ := by
    field_simp
  rw [hquot, Real.arctan_inv_of_pos (Real.sqrt_pos.2 harg)]

/-- At every radial dilation threshold `k ≥ 1`, the literal leading Dunster density has the exact
arcsine tail predicted for the diagonal radial Gram entry. -/
theorem tendsto_integral_Ioi_sqrt_sq_sub_one_radialPSWFLeadingArclengthDensity
    {ι : Type*} {l : Filter ι} {c sigma : ι → ℝ} {theta k : ℝ}
    (hc : Tendsto c l atTop) (hsigma : Tendsto sigma l (nhds 0)) (hk : 1 ≤ k) :
    Tendsto (fun i => ∫ t in Ioi (Real.sqrt (k ^ 2 - 1)),
        radialPSWFLeadingArclengthDensity (c i) (sigma i) theta t)
      l (nhds ((1 / Real.pi) * Real.arcsin (1 / k))) := by
  have h := tendsto_integral_Ioi_radialPSWFLeadingArclengthDensity
    (theta := theta) hc hsigma (Real.sqrt_nonneg (k ^ 2 - 1))
  rw [pi_div_two_sub_arctan_sqrt_sq_sub_one hk] at h
  exact h

end

end RHTower
