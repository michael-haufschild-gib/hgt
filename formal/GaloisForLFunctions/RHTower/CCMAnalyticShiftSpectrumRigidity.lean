import GaloisForLFunctions.RHTower.CCMEvenShiftExponentialTypeRigidity
import Mathlib.Analysis.Analytic.Order

/-!
# Holomorphic fixed-shift calculus has a quantized aperture spectrum

A finite polynomial in the fixed shift coordinate `z = exp (-q h)` changes an aperture exponent
by its valuation at `z = 0`.  This file proves the complete holomorphic extension.  Every analytic
germ at the augmentation point has exactly two possible effects:

* a locally zero germ annihilates every aperture carrier eventually;
* a nonzero germ translates every exponential upper-rate budget by exactly `q` times its finite
  vanishing order.

Thus no coefficient beyond the first nonzero Taylor coefficient affects the aperture exponent.
In particular, a holomorphic unit is completely rate-invisible, while any nontrivial improvement
is quantized and loses exactly the corresponding finite exponent slab.  A fixed-shift transform
outside this dichotomy must be singular at the augmentation boundary.
-/

open Filter
open scoped Topology

noncomputable section

namespace RHTower

/-- Absolute multiplier obtained by evaluating a complex filter on the physical fixed-shift arc
`z = exp (-q h)`. -/
def analyticShiftMultiplier (q : ℝ) (F : ℂ → ℂ) (h : ℝ) : ℝ :=
  ‖F (Real.exp (-q * h) : ℂ)‖

/-- Exponential upper-rate budgets depend only on an eventual germ at aperture infinity. -/
theorem apertureExponentialUpperBound_congr
    {eta theta : ℝ → ℝ} {epsilon : ℝ} (h : eta =ᶠ[atTop] theta) :
    ApertureExponentialUpperBound eta epsilon ↔
      ApertureExponentialUpperBound theta epsilon := by
  constructor <;> rintro ⟨C, hC, hb⟩ <;> refine ⟨C, hC, ?_⟩
  · filter_upwards [hb, h] with x hx heq
    rwa [← heq]
  · filter_upwards [hb, h] with x hx heq
    rwa [heq]

/-- Evaluation on the fixed-shift arc converges to evaluation at the augmentation point. -/
theorem tendsto_analyticShiftMultiplier
    {q : ℝ} (hq : 0 < q) {F : ℂ → ℂ} (hF : ContinuousAt F 0) :
    Tendsto (analyticShiftMultiplier q F) atTop (nhds ‖F 0‖) := by
  have hexpR : Tendsto (fun h : ℝ => Real.exp (-q * h)) atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_id.const_mul_atTop_of_neg (by linarith : -q < 0)
  have hexpC : Tendsto (fun h : ℝ => (Real.exp (-q * h) : ℂ)) atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hexpR
  exact hF.norm.tendsto.comp hexpC

/-- The analytic vanishing-order factorization becomes an exact eventual exponential attenuation
times a multiplier converging to a positive constant on the physical fixed-shift arc. -/
theorem analyticShiftMultiplier_eventually_factor
    {q : ℝ} (hq : 0 < q) {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hFfinite : analyticOrderAt F 0 ≠ ⊤) :
    ∃ G : ℂ → ℂ,
      AnalyticAt ℂ G 0 ∧ G 0 ≠ 0 ∧
      Tendsto (analyticShiftMultiplier q G) atTop (nhds ‖G 0‖) ∧
      analyticShiftMultiplier q F =ᶠ[atTop]
        fun h => Real.exp (-(q * (analyticOrderNatAt F 0 : ℝ)) * h) *
          analyticShiftMultiplier q G h := by
  have horder : (analyticOrderNatAt F 0 : ℕ∞) = analyticOrderAt F 0 :=
    ENat.coe_toNat hFfinite
  obtain ⟨G, hGan, hG0, hfactor⟩ :=
    (hF.analyticOrderAt_eq_natCast).mp horder.symm
  have hexpR : Tendsto (fun h : ℝ => Real.exp (-q * h)) atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_id.const_mul_atTop_of_neg (by linarith : -q < 0)
  have hexpC : Tendsto (fun h : ℝ => (Real.exp (-q * h) : ℂ)) atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hexpR
  refine ⟨G, hGan, hG0,
    tendsto_analyticShiftMultiplier hq hGan.continuousAt, ?_⟩
  filter_upwards [hexpC.eventually hfactor] with h hh
  rw [analyticShiftMultiplier, analyticShiftMultiplier, hh, norm_smul, norm_pow]
  simp only [sub_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (-q * h))]
  rw [show -(q * (analyticOrderNatAt F 0 : ℝ)) * h =
      (analyticOrderNatAt F 0 : ℝ) * (-q * h) by ring,
    Real.exp_nat_mul]

/-- **Complete holomorphic fixed-shift spectrum law.**  A nonzero analytic germ translates every
aperture exponential upper-rate budget by exactly its vanishing order times the shift length.
No higher Taylor coefficient affects any rate. -/
theorem apertureExponentialUpperBound_analyticShift_complete_iff
    {q : ℝ} (hq : 0 < q) {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hFfinite : analyticOrderAt F 0 ≠ ⊤)
    {eta : ℝ → ℝ} (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) (epsilon : ℝ) :
    ApertureExponentialUpperBound
        (fun h => analyticShiftMultiplier q F h * eta h) epsilon ↔
      ApertureExponentialUpperBound eta
        (epsilon + q * (analyticOrderNatAt F 0 : ℝ)) := by
  obtain ⟨G, hGan, hG0, hGlim, hfactor⟩ :=
    analyticShiftMultiplier_eventually_factor hq hF hFfinite
  have hcongr :
      (fun h => analyticShiftMultiplier q F h * eta h) =ᶠ[atTop]
        fun h => Real.exp (-(q * (analyticOrderNatAt F 0 : ℝ)) * h) *
          (analyticShiftMultiplier q G h * eta h) := by
    filter_upwards [hfactor] with h hh
    rw [hh]
    ring
  rw [apertureExponentialUpperBound_congr hcongr,
    apertureExponentialUpperBound_exp_neg_mul_iff]
  exact apertureExponentialUpperBound_mul_iff_of_tendsto_pos
    (norm_pos_iff.mpr hG0) hGlim heta _

/-- Zero exponential type above a prescribed base rate. -/
def SubexponentialAboveApertureRate (eta : ℝ → ℝ) (baseRate : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ApertureExponentialUpperBound eta (baseRate + epsilon)

/-- A nonzero holomorphic fixed-shift filter makes the output zero-type exactly when the input is
subexponential above the quantized rate discarded by the filter. -/
theorem subexponentialAtApertureInfinity_analyticShift_complete_iff
    {q : ℝ} (hq : 0 < q) {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hFfinite : analyticOrderAt F 0 ≠ ⊤)
    {eta : ℝ → ℝ} (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) :
    SubexponentialAtApertureInfinity
        (fun h => analyticShiftMultiplier q F h * eta h) ↔
      SubexponentialAboveApertureRate eta
        (q * (analyticOrderNatAt F 0 : ℝ)) := by
  constructor <;> intro hsub epsilon hepsilon
  · have h := (apertureExponentialUpperBound_analyticShift_complete_iff
      hq hF hFfinite heta epsilon).1 (hsub epsilon hepsilon)
    simpa [add_comm] using h
  · apply (apertureExponentialUpperBound_analyticShift_complete_iff
      hq hF hFfinite heta epsilon).2
    simpa [add_comm] using hsub epsilon hepsilon

/-- A holomorphic unit at the augmentation point is completely invisible to zero exponential
type. -/
theorem subexponentialAtApertureInfinity_analyticShift_unit_iff
    {q : ℝ} (hq : 0 < q) {F : ℂ → ℂ} (hF : ContinuousAt F 0) (hF0 : F 0 ≠ 0)
    {eta : ℝ → ℝ} (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) :
    SubexponentialAtApertureInfinity
        (fun h => analyticShiftMultiplier q F h * eta h) ↔
      SubexponentialAtApertureInfinity eta := by
  exact subexponentialAtApertureInfinity_mul_iff_of_tendsto_pos
    (norm_pos_iff.mpr hF0) (tendsto_analyticShiftMultiplier hq hF) heta

/-- A locally zero analytic germ annihilates every physical fixed-shift multiplier eventually. -/
theorem analyticShiftMultiplier_eventually_eq_zero_of_order_eq_top
    {q : ℝ} (hq : 0 < q) {F : ℂ → ℂ}
    (hFtop : analyticOrderAt F 0 = ⊤) :
    analyticShiftMultiplier q F =ᶠ[atTop] 0 := by
  have hzero : ∀ᶠ z : ℂ in 𝓝 0, F z = 0 := analyticOrderAt_eq_top.mp hFtop
  have hexpR : Tendsto (fun h : ℝ => Real.exp (-q * h)) atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_id.const_mul_atTop_of_neg (by linarith : -q < 0)
  have hexpC : Tendsto (fun h : ℝ => (Real.exp (-q * h) : ℂ)) atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hexpR
  filter_upwards [hexpC.eventually hzero] with h hh
  unfold analyticShiftMultiplier
  rw [hh, norm_zero]
  simp

/-- The locally zero branch of the analytic dichotomy has every exponential upper-rate budget,
independently of the input carrier. -/
theorem apertureExponentialUpperBound_analyticShift_of_order_eq_top
    {q : ℝ} (hq : 0 < q) {F : ℂ → ℂ}
    (hFtop : analyticOrderAt F 0 = ⊤) (eta : ℝ → ℝ) (epsilon : ℝ) :
    ApertureExponentialUpperBound
      (fun h => analyticShiftMultiplier q F h * eta h) epsilon := by
  refine ⟨0, le_rfl, ?_⟩
  filter_upwards [analyticShiftMultiplier_eventually_eq_zero_of_order_eq_top hq hFtop]
    with h hh
  rw [hh]
  simp

/-- Direct CCM connector: every nonzero holomorphic fixed-shift filter sees the published
completed critical-Mellin error only after the exact finite rate translation determined by its
vanishing order. -/
theorem criticalMellinCompletedError_analyticShift_upperBound_iff
    {q : ℝ} (hq : 0 < q) {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hFfinite : analyticOrderAt F 0 ≠ ⊤) (epsilon : ℝ) :
    ApertureExponentialUpperBound
        (fun h => analyticShiftMultiplier q F h * |criticalMellinCompletedError h|)
        epsilon ↔
      ApertureExponentialUpperBound
        (fun h => |criticalMellinCompletedError h|)
        (epsilon + q * (analyticOrderNatAt F 0 : ℝ)) := by
  exact apertureExponentialUpperBound_analyticShift_complete_iff
    hq hF hFfinite
      (Eventually.of_forall fun h => abs_nonneg (criticalMellinCompletedError h)) epsilon

section NormedOperatorValued

variable {E : Type*} [NormedAddCommGroup E]

/-- Norm of a vector-, operator-, or Schatten-valued holomorphic filter evaluated on the physical
fixed-shift arc. -/
def normedAnalyticShiftMultiplier (q : ℝ) (F : ℂ → E) (h : ℝ) : ℝ :=
  ‖F (Real.exp (-q * h) : ℂ)‖

/-- Normed-valued evaluation on the physical fixed-shift arc converges to the augmentation
value. -/
theorem tendsto_normedAnalyticShiftMultiplier
    {q : ℝ} (hq : 0 < q) {F : ℂ → E} (hF : ContinuousAt F 0) :
    Tendsto (normedAnalyticShiftMultiplier q F) atTop (nhds ‖F 0‖) := by
  have hexpR : Tendsto (fun h : ℝ => Real.exp (-q * h)) atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_id.const_mul_atTop_of_neg (by linarith : -q < 0)
  have hexpC : Tendsto (fun h : ℝ => (Real.exp (-q * h) : ℂ)) atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hexpR
  exact hF.norm.tendsto.comp hexpC

variable [NormedSpace ℂ E]

/-- A nonzero normed-valued analytic germ has exact exponential attenuation given by its finite
vanishing order, times a norm multiplier converging to a positive constant. -/
theorem normedAnalyticShiftMultiplier_eventually_factor
    {q : ℝ} (hq : 0 < q) {F : ℂ → E} (hF : AnalyticAt ℂ F 0)
    (hFfinite : analyticOrderAt F 0 ≠ ⊤) :
    ∃ G : ℂ → E,
      AnalyticAt ℂ G 0 ∧ G 0 ≠ 0 ∧
      Tendsto (normedAnalyticShiftMultiplier q G) atTop (nhds ‖G 0‖) ∧
      normedAnalyticShiftMultiplier q F =ᶠ[atTop]
        fun h => Real.exp (-(q * (analyticOrderNatAt F 0 : ℝ)) * h) *
          normedAnalyticShiftMultiplier q G h := by
  have horder : (analyticOrderNatAt F 0 : ℕ∞) = analyticOrderAt F 0 :=
    ENat.coe_toNat hFfinite
  obtain ⟨G, hGan, hG0, hfactor⟩ :=
    (hF.analyticOrderAt_eq_natCast).mp horder.symm
  have hexpR : Tendsto (fun h : ℝ => Real.exp (-q * h)) atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_id.const_mul_atTop_of_neg (by linarith : -q < 0)
  have hexpC : Tendsto (fun h : ℝ => (Real.exp (-q * h) : ℂ)) atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hexpR
  refine ⟨G, hGan, hG0,
    tendsto_normedAnalyticShiftMultiplier hq hGan.continuousAt, ?_⟩
  filter_upwards [hexpC.eventually hfactor] with h hh
  rw [normedAnalyticShiftMultiplier, normedAnalyticShiftMultiplier, hh, norm_smul, norm_pow]
  simp only [sub_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (-q * h))]
  rw [show -(q * (analyticOrderNatAt F 0 : ℝ)) * h =
      (analyticOrderNatAt F 0 : ℝ) * (-q * h) by ring,
    Real.exp_nat_mul]

/-- **Operator-valued holomorphic aperture-spectrum law.**  In every complex normed target,
including bounded-operator and Schatten targets, a nonzero norm-holomorphic fixed-shift germ
translates every aperture exponential upper-rate budget by exactly shift length times its
vanishing order. -/
theorem apertureExponentialUpperBound_normedAnalyticShift_complete_iff
    {q : ℝ} (hq : 0 < q) {F : ℂ → E} (hF : AnalyticAt ℂ F 0)
    (hFfinite : analyticOrderAt F 0 ≠ ⊤)
    {eta : ℝ → ℝ} (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) (epsilon : ℝ) :
    ApertureExponentialUpperBound
        (fun h => normedAnalyticShiftMultiplier q F h * eta h) epsilon ↔
      ApertureExponentialUpperBound eta
        (epsilon + q * (analyticOrderNatAt F 0 : ℝ)) := by
  obtain ⟨G, hGan, hG0, hGlim, hfactor⟩ :=
    normedAnalyticShiftMultiplier_eventually_factor hq hF hFfinite
  have hcongr :
      (fun h => normedAnalyticShiftMultiplier q F h * eta h) =ᶠ[atTop]
        fun h => Real.exp (-(q * (analyticOrderNatAt F 0 : ℝ)) * h) *
          (normedAnalyticShiftMultiplier q G h * eta h) := by
    filter_upwards [hfactor] with h hh
    rw [hh]
    ring
  rw [apertureExponentialUpperBound_congr hcongr,
    apertureExponentialUpperBound_exp_neg_mul_iff]
  exact apertureExponentialUpperBound_mul_iff_of_tendsto_pos
    (norm_pos_iff.mpr hG0) hGlim heta _

/-- Normed-valued zero-type form of the complete holomorphic spectrum law. -/
theorem subexponentialAtApertureInfinity_normedAnalyticShift_complete_iff
    {q : ℝ} (hq : 0 < q) {F : ℂ → E} (hF : AnalyticAt ℂ F 0)
    (hFfinite : analyticOrderAt F 0 ≠ ⊤)
    {eta : ℝ → ℝ} (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) :
    SubexponentialAtApertureInfinity
        (fun h => normedAnalyticShiftMultiplier q F h * eta h) ↔
      SubexponentialAboveApertureRate eta
        (q * (analyticOrderNatAt F 0 : ℝ)) := by
  constructor <;> intro hsub epsilon hepsilon
  · have h := (apertureExponentialUpperBound_normedAnalyticShift_complete_iff
      hq hF hFfinite heta epsilon).1 (hsub epsilon hepsilon)
    simpa [add_comm] using h
  · apply (apertureExponentialUpperBound_normedAnalyticShift_complete_iff
      hq hF hFfinite heta epsilon).2
    simpa [add_comm] using hsub epsilon hepsilon

omit [NormedSpace ℂ E] in
/-- A norm-holomorphic operator-valued unit is completely invisible to zero exponential type. -/
theorem subexponentialAtApertureInfinity_normedAnalyticShift_unit_iff
    {q : ℝ} (hq : 0 < q) {F : ℂ → E} (hF : ContinuousAt F 0) (hF0 : F 0 ≠ 0)
    {eta : ℝ → ℝ} (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) :
    SubexponentialAtApertureInfinity
        (fun h => normedAnalyticShiftMultiplier q F h * eta h) ↔
      SubexponentialAtApertureInfinity eta := by
  exact subexponentialAtApertureInfinity_mul_iff_of_tendsto_pos
    (norm_pos_iff.mpr hF0) (tendsto_normedAnalyticShiftMultiplier hq hF) heta

/-- Locally zero normed-valued germs annihilate the physical fixed-shift arc eventually. -/
theorem normedAnalyticShiftMultiplier_eventually_eq_zero_of_order_eq_top
    {q : ℝ} (hq : 0 < q) {F : ℂ → E}
    (hFtop : analyticOrderAt F 0 = ⊤) :
    normedAnalyticShiftMultiplier q F =ᶠ[atTop] 0 := by
  have hzero : ∀ᶠ z : ℂ in 𝓝 0, F z = 0 := analyticOrderAt_eq_top.mp hFtop
  have hexpR : Tendsto (fun h : ℝ => Real.exp (-q * h)) atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_id.const_mul_atTop_of_neg (by linarith : -q < 0)
  have hexpC : Tendsto (fun h : ℝ => (Real.exp (-q * h) : ℂ)) atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hexpR
  filter_upwards [hexpC.eventually hzero] with h hh
  unfold normedAnalyticShiftMultiplier
  rw [hh, norm_zero]
  simp

end NormedOperatorValued

end RHTower
