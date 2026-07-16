import GaloisForLFunctions.RHTower.MobiusCriticalFisherSteinContact
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Set Filter
open scoped Topology Interval

noncomputable section

namespace RHTower

/-- The folded universal critical gap density predicted by two independent unit-rate
exponential incidence coordinates. -/
def mobiusIncidenceUniversalGapDensity (x : ℝ) : ℝ :=
  2 * |x| * Real.exp (-|x|)

theorem mobiusIncidenceUniversalGapDensity_nonneg (x : ℝ) :
    0 ≤ mobiusIncidenceUniversalGapDensity x := by
  unfold mobiusIncidenceUniversalGapDensity
  positivity

/-- The universal gap density has the exact four-unit mass dictated by the completed
incidence normalization. -/
theorem integral_mobiusIncidenceUniversalGapDensity :
    (∫ x : ℝ, mobiusIncidenceUniversalGapDensity x) = 4 := by
  simp only [mobiusIncidenceUniversalGapDensity]
  rw [show (fun x : ℝ => 2 * |x| * Real.exp (-|x|)) =
      fun x => 2 * (|x| * Real.exp (-|x|)) by
    funext x
    ring]
  rw [integral_const_mul,
    integral_comp_abs (f := fun x : ℝ => x * Real.exp (-x))]
  have h := integral_Ioi_pow_mul_exp_neg_rate 1 (show (0 : ℝ) < 1 by norm_num)
  simp only [pow_one, one_mul] at h
  rw [h]
  norm_num

/-- Positive-axis quotient controlling the imaginary-axis slope of the folded universal
gap response. -/
def mobiusIncidenceUniversalGapSlope (eta : ℝ) : ℝ :=
  ∫ x in Ioi 0, x * Real.exp (-x) / (x ^ 2 + eta ^ 2)

theorem integrableOn_mobiusIncidenceUniversalGapSlope
    {eta : ℝ} (heta : 0 < eta) :
    IntegrableOn
      (fun x : ℝ => x * Real.exp (-x) / (x ^ 2 + eta ^ 2)) (Ioi 0) := by
  have hbase : IntegrableOn (fun x : ℝ => x * Real.exp (-x)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (1 : ℝ)) (b := 1)
      (by norm_num) (by norm_num) (by norm_num)
    convert h using 1
    funext x
    simp only [Real.rpow_one, one_mul]
    congr 1
    ring
  have hmajor : IntegrableOn
      (fun x : ℝ => (eta ^ 2)⁻¹ * (x * Real.exp (-x))) (Ioi 0) :=
    hbase.const_mul (eta ^ 2)⁻¹
  refine hmajor.mono' ?_ ?_
  · exact ((continuous_id.mul (Real.continuous_exp.comp continuous_neg)).div
      (continuous_id.pow 2 |>.add (continuous_const.pow 2))
      (fun x hx => by
        have : 0 < x ^ 2 + eta ^ 2 := by positivity
        exact this.ne' hx)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    have hnum : 0 ≤ x * Real.exp (-x) := by positivity
    have hden : eta ^ 2 ≤ x ^ 2 + eta ^ 2 := by nlinarith [sq_nonneg x]
    have hden0 : 0 < eta ^ 2 := sq_pos_of_pos heta
    have hleft : 0 ≤ x * Real.exp (-x) / (x ^ 2 + eta ^ 2) := by positivity
    have hright : 0 ≤ (eta ^ 2)⁻¹ * (x * Real.exp (-x)) := by positivity
    simp only [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright]
    calc
      x * Real.exp (-x) / (x ^ 2 + eta ^ 2)
          ≤ x * Real.exp (-x) / eta ^ 2 :=
        div_le_div_of_nonneg_left hnum hden0 hden
      _ = (eta ^ 2)⁻¹ * (x * Real.exp (-x)) := by ring

theorem intervalIntegral_one_div_eq_neg_log
    {eta : ℝ} (heta : 0 < eta) :
    (∫ x : ℝ in eta..1, 1 / x) = -Real.log eta := by
  rw [integral_one_div_of_pos heta (by norm_num)]
  rw [one_div, inv_eq_one_div, Real.log_div (by norm_num : (1 : ℝ) ≠ 0) heta.ne']
  simp

/-- The positive-axis quotient has an explicit logarithmically divergent lower bound. -/
theorem mobiusIncidenceUniversalGapSlope_lower_bound
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    Real.exp (-1) / 2 * (-Real.log eta) ≤
      mobiusIncidenceUniversalGapSlope eta := by
  let F : ℝ → ℝ := fun x => x * Real.exp (-x) / (x ^ 2 + eta ^ 2)
  let G : ℝ → ℝ := fun x => Real.exp (-1) / (2 * x)
  have hFint : IntegrableOn F (Ioi 0) := by
    simpa only [F] using integrableOn_mobiusIncidenceUniversalGapSlope heta
  have hFnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp only [F]
    exact div_nonneg (mul_nonneg (le_of_lt hx) (Real.exp_nonneg _)) (by positivity)
  have hsubset : Ioc eta 1 ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact heta.trans hx.1
  have hinterval_le : (∫ x in eta..1, F x) ≤ ∫ x in Ioi 0, F x := by
    rw [intervalIntegral.integral_of_le heta1]
    exact setIntegral_mono_set hFint hFnonneg
      (Filter.Eventually.of_forall (fun x hx => hsubset hx))
  have hFcont : ContinuousOn F (Icc eta 1) := by
    intro x hx
    dsimp only [F]
    fun_prop (disch := positivity)
  have hGcont : ContinuousOn G (Icc eta 1) := by
    intro x hx
    dsimp only [G]
    fun_prop (disch := linarith [hx.1])
  have hpoint : ∀ x ∈ Icc eta 1, G x ≤ F x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le heta hx.1
    have hexp : Real.exp (-1) ≤ Real.exp (-x) := by
      exact Real.exp_le_exp.mpr (neg_le_neg hx.2)
    have heta_sq : eta ^ 2 ≤ x ^ 2 :=
      (sq_le_sq₀ heta.le hx0.le).2 hx.1
    have hden : x ^ 2 + eta ^ 2 ≤ 2 * x ^ 2 := by linarith
    have hratio : 1 / (2 * x) ≤ x / (x ^ 2 + eta ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    dsimp only [F, G]
    calc
      Real.exp (-1) / (2 * x)
          ≤ Real.exp (-x) / (2 * x) :=
        div_le_div_of_nonneg_right hexp (by positivity)
      _ ≤ Real.exp (-x) * (x / (x ^ 2 + eta ^ 2)) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hratio (Real.exp_nonneg (-x))
      _ = x * Real.exp (-x) / (x ^ 2 + eta ^ 2) := by ring
  have hmono : (∫ x in eta..1, G x) ≤ ∫ x in eta..1, F x :=
    intervalIntegral.integral_mono_on heta1
      (hGcont.intervalIntegrable_of_Icc heta1)
      (hFcont.intervalIntegrable_of_Icc heta1) hpoint
  have hG : (∫ x in eta..1, G x) =
      Real.exp (-1) / 2 * (-Real.log eta) := by
    dsimp only [G]
    rw [show (fun x : ℝ => Real.exp (-1) / (2 * x)) =
        fun x => (Real.exp (-1) / 2) * (1 / x) by
      funext x
      ring]
    rw [intervalIntegral.integral_const_mul, intervalIntegral_one_div_eq_neg_log heta]
  rw [← hG]
  exact hmono.trans hinterval_le

/-- The universal positive-axis quotient diverges to positive infinity at the centered
boundary point. -/
theorem tendsto_mobiusIncidenceUniversalGapSlope_nhdsGT_zero_atTop :
    Tendsto mobiusIncidenceUniversalGapSlope (nhdsWithin 0 (Ioi 0)) atTop := by
  have hneglog : Tendsto (fun eta : ℝ => -Real.log eta)
      (nhdsWithin 0 (Ioi 0)) atTop :=
    tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero
  have hcoefficient : 0 < Real.exp (-1) / 2 := by positivity
  have hscaled := hneglog.const_mul_atTop hcoefficient
  refine tendsto_atTop_mono' (nhdsWithin 0 (Ioi 0)) ?_ hscaled
  have hlt : ∀ᶠ eta : ℝ in nhdsWithin 0 (Ioi 0), eta < 1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with eta heta heta1
  exact mobiusIncidenceUniversalGapSlope_lower_bound heta heta1.le

/-- The folded Cauchy response of the universal four-unit gap density. -/
def mobiusIncidenceUniversalGapResponse (z : ℂ) : ℂ :=
  4 * z * ∫ x in Ioi (0 : ℝ),
    ((x * Real.exp (-x) : ℝ) : ℂ) / (z ^ 2 - (x : ℂ) ^ 2)

@[simp]
theorem mobiusIncidenceUniversalGapResponse_zero :
    mobiusIncidenceUniversalGapResponse 0 = 0 := by
  simp [mobiusIncidenceUniversalGapResponse]

/-- Exact imaginary-axis form of the universal response quotient. -/
theorem mobiusIncidenceUniversalGapResponse_I_mul_div
    {eta : ℝ} (heta : 0 < eta) :
    mobiusIncidenceUniversalGapResponse (Complex.I * eta) /
        (Complex.I * eta) =
      ((-4 * mobiusIncidenceUniversalGapSlope eta : ℝ) : ℂ) := by
  have heta0 : (eta : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
  have hIeta : Complex.I * (eta : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero heta0
  have hintegrand :
      (fun x : ℝ =>
          ((x * Real.exp (-x) : ℝ) : ℂ) /
            ((Complex.I * eta) ^ 2 - (x : ℂ) ^ 2)) =
        fun x =>
          ((-(x * Real.exp (-x) / (x ^ 2 + eta ^ 2)) : ℝ) : ℂ) := by
    funext x
    have hden : x ^ 2 + eta ^ 2 ≠ 0 := by positivity
    have hdenC : (((x ^ 2 + eta ^ 2 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast hden
    push_cast
    rw [mul_pow, Complex.I_sq]
    rw [show (-1 : ℂ) * (eta : ℂ) ^ 2 - (x : ℂ) ^ 2 =
        -(((x ^ 2 + eta ^ 2 : ℝ) : ℂ)) by
      push_cast
      ring]
    rw [div_neg]
    push_cast
  have hintegral :
      (∫ x in Ioi (0 : ℝ),
          ((x * Real.exp (-x) : ℝ) : ℂ) /
            ((Complex.I * eta) ^ 2 - (x : ℂ) ^ 2)) =
        ((-mobiusIncidenceUniversalGapSlope eta : ℝ) : ℂ) := by
    rw [hintegrand]
    have hcast :
        (∫ x in Ioi (0 : ℝ),
          ((-(x * Real.exp (-x) / (x ^ 2 + eta ^ 2)) : ℝ) : ℂ)) =
          (((∫ x in Ioi (0 : ℝ),
            -(x * Real.exp (-x) / (x ^ 2 + eta ^ 2))) : ℝ) : ℂ) := by
      exact integral_ofReal
        (X := ℝ) (μ := volume.restrict (Ioi 0)) (𝕜 := ℂ)
    rw [hcast, integral_neg]
    rfl
  rw [mobiusIncidenceUniversalGapResponse, hintegral]
  apply (div_eq_iff hIeta).2
  push_cast
  ring

theorem mobiusIncidenceUniversalGapResponse_I_mul_div_re
    {eta : ℝ} (heta : 0 < eta) :
    (mobiusIncidenceUniversalGapResponse (Complex.I * eta) /
        (Complex.I * eta)).re =
      -4 * mobiusIncidenceUniversalGapSlope eta := by
  rw [mobiusIncidenceUniversalGapResponse_I_mul_div heta]
  simp

/-- The real part of the imaginary-axis response quotient tends to negative infinity. -/
theorem tendsto_mobiusIncidenceUniversalGapResponse_I_mul_div_re_nhdsGT_zero_atBot :
    Tendsto
      (fun eta : ℝ =>
        (mobiusIncidenceUniversalGapResponse (Complex.I * eta) /
          (Complex.I * eta)).re)
      (nhdsWithin 0 (Ioi 0)) atBot := by
  have hscaled : Tendsto
      (fun eta : ℝ => -4 * mobiusIncidenceUniversalGapSlope eta)
      (nhdsWithin 0 (Ioi 0)) atBot :=
    (tendsto_const_mul_atBot_of_neg
      (f := mobiusIncidenceUniversalGapSlope)
      (l := nhdsWithin 0 (Ioi 0)) (r := (-4 : ℝ)) (by norm_num)).2
        tendsto_mobiusIncidenceUniversalGapSlope_nhdsGT_zero_atTop
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with eta heta
  exact (mobiusIncidenceUniversalGapResponse_I_mul_div_re heta).symm

/-- The imaginary-axis quotient has no finite complex limit at the centered origin. -/
theorem not_tendsto_mobiusIncidenceUniversalGapResponse_I_mul_div_nhds
    (c : ℂ) :
    ¬ Tendsto
      (fun eta : ℝ =>
        mobiusIncidenceUniversalGapResponse (Complex.I * eta) /
          (Complex.I * eta))
      (nhdsWithin 0 (Ioi 0)) (nhds c) := by
  intro h
  have hre : Tendsto
      (fun eta : ℝ =>
        (mobiusIncidenceUniversalGapResponse (Complex.I * eta) /
          (Complex.I * eta)).re)
      (nhdsWithin 0 (Ioi 0)) (nhds c.re) :=
    Complex.continuous_re.continuousAt.tendsto.comp h
  exact (not_tendsto_nhds_of_tendsto_atBot
    tendsto_mobiusIncidenceUniversalGapResponse_I_mul_div_re_nhdsGT_zero_atBot
    c.re) hre

end RHTower
