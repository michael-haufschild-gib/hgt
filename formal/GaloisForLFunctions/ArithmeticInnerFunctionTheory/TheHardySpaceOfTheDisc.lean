import GaloisForLFunctions.ArithmeticInnerFunctionTheory.ThePoissonJensenIdentity
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheSzegoInfimum
import GaloisForLFunctions.Bottcher.ZeroSet
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Hardy space of a disc datum

A function holomorphic off the boundary point `1`, of polynomial growth there, bounded on a radius, and square-integrable on the circle
(`IsHardyDisc`) behaves like an `H²` function. All of this follows from the Poisson–Jensen identity, with no boundary-limit theory.

* **Sub-mean value** (`IsDiscDatum.norm_sq_le_circleAverage`). `|Ψ(0)|² ≤ avg |Ψ|²`: Jensen on the disc, then Jensen's inequality for the exponential.
* **Mean value** (`IsHardyDisc.circleAverage_eq`). `avg Φ = Φ(0)`. It comes from the sub-mean value for `Φ + λ`, by letting `λ` be large: the quadratic terms cancel, and a linear
  functional bounded on all large `λ` vanishes.
* **Parseval** (`IsHardyDisc.circleAverage_norm_sq_eq`). With `a_k` the Taylor coefficients at `0`, `avg |Φ|² = Σ_{k<n} |a_k|² + avg |Φ_n|²`, where `Φ_n` is `Φ` with the first `n` terms peeled off.
* **The reproducing bound** (`IsHardyDisc.norm_sub_sq_le`). `|Φ(u) − Φ(0)|² ≤ (avg |Φ|² − |Φ(0)|²) |u|²/(1 − |u|²)`.
-/

open Complex Metric Filter Topology MeasureTheory Set
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

noncomputable section

local notation "𝕋" => AddCircle (2 * π)

/-! ### The sub-mean value -/

theorem norm_circleMap_zero_one (θ : ℝ) : ‖circleMap 0 1 θ‖ = 1 := by
  simp [circleMap]

/-- `|Ψ(0)|² ≤ avg |Ψ|²` for a disc datum. -/
theorem IsDiscDatum.norm_sq_le_circleAverage {Ψ : ℂ → ℂ} (hD : IsDiscDatum Ψ)
    (hl2 : CircleIntegrable (fun z => ‖Ψ z‖ ^ 2) 0 1) :
    ‖Ψ 0‖ ^ 2 ≤ Real.circleAverage (fun z => ‖Ψ z‖ ^ 2) 0 1 := by
  have hJ : Real.log ‖Ψ 0‖ ≤ Real.circleAverage (fun w => Real.log ‖Ψ w‖) 0 1 := by
    have h := hD.hasSum_discWeight.nonneg hD.discWeight_nonneg
    linarith
  have hmeasW : Measurable fun z => ‖Ψ z‖ ^ 2 := hD.meas.norm.pow_const 2
  have hcnt : {z : ℂ | Ψ z = 0 ∧ z ≠ 1}.Countable := by
    have hc := Bottcher.analyticOnNhd_zeros_countable (f := Ψ) (U := {1}ᶜ)
      (fun z hz => hD.analyticAt hz)
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
      (show (0 : ℂ) ∈ ({1}ᶜ : Set ℂ) by simp) hD.ne0
    exact hc.mono fun z hz => by
      have hz' : Ψ z = 0 ∧ z ≠ 1 := hz
      exact ⟨hz'.2, hz'.1⟩
  have hpos : ∀ᵐ x : 𝕋 ∂AddCircle.haarAddCircle, 0 < ‖Ψ (circleZ x)‖ ^ 2 := by
    have hA : ({z : ℂ | Ψ z = 0 ∧ z ≠ 1} ∪ {1}).Countable := hcnt.union (countable_singleton _)
    filter_upwards [ae_circleZ_notMem_of_countable hA] with x hx
    have hx1 : circleZ x ≠ 1 := fun h => hx (Or.inr h)
    have hne : Ψ (circleZ x) ≠ 0 := fun h => hx (Or.inl ⟨h, hx1⟩)
    exact pow_pos (norm_pos_iff.mpr hne) 2
  have hint := (integrable_haar_circleZ_iff hmeasW).mpr hl2
  have hlogc : CircleIntegrable (fun z => Real.log (‖Ψ z‖ ^ 2)) 0 1 := by
    have h := hD.circleIntegrable.const_smul (a := (2 : ℝ))
    have e : (fun z => Real.log (‖Ψ z‖ ^ 2)) = (2 : ℝ) • fun w => Real.log ‖Ψ w‖ := by
      funext z
      simp [Real.log_pow]
    rw [e]
    exact h
  have hlog := (integrable_haar_circleZ_iff (Real.measurable_log.comp hmeasW)).mpr hlogc
  have hE := exp_integral_log_le (μ := AddCircle.haarAddCircle) hpos hint hlog (g := fun _ => 0)
    measurable_const ⟨0, fun _ => by simp⟩ (by simp)
  simp only [Real.exp_zero, mul_one] at hE
  have e1 := integral_haar_circleZ fun z => ‖Ψ z‖ ^ 2
  have e2 := integral_haar_circleZ fun z => Real.log (‖Ψ z‖ ^ 2)
  rw [e1] at hE
  have e3 : ∫ x : 𝕋, Real.log (‖Ψ (circleZ x)‖ ^ 2) ∂AddCircle.haarAddCircle =
      2 * Real.circleAverage (fun w => Real.log ‖Ψ w‖) 0 1 := by
    have h4 : Real.circleAverage (fun z => Real.log (‖Ψ z‖ ^ 2)) 0 1 =
        Real.circleAverage (fun z => (2 : ℝ) • Real.log ‖Ψ z‖) 0 1 :=
      Real.circleAverage_congr_sphere fun z _ => by simp [Real.log_pow]
    rw [e2, h4, Real.circleAverage_fun_smul]
    simp
  rw [e3] at hE
  refine le_trans ?_ hE
  have hne : 0 < ‖Ψ 0‖ := norm_pos_iff.mpr hD.ne0
  rw [← Real.exp_log (pow_pos hne 2), Real.log_pow]
  refine Real.exp_le_exp.mpr ?_
  push_cast
  linarith

/-! ### Squares -/

/-- The linear part of a square. -/
theorem norm_add_sq (a b : ℂ) : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * (conj b * a).re + ‖b‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_add]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The linear functional `z ↦ Re(b̄ z)`. -/
def reMul (b : ℂ) : ℂ →L[ℝ] ℝ := Complex.reCLM.comp ((ContinuousLinearMap.mul ℝ ℂ) (conj b))

theorem reMul_apply (b z : ℂ) : reMul b z = (conj b * z).re := rfl

/-! ### The class -/

/-- A disc function of Hardy type: holomorphic off `1`, of polynomial growth at `1`, bounded on a radius, and
square-integrable on the circle. -/
structure IsHardyDisc (Φ : ℂ → ℂ) : Prop where
  diff : DifferentiableOn ℂ Φ {1}ᶜ
  meas : Measurable Φ
  up : ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 1 → ‖Φ w‖ ≤ A / ‖1 - w‖ ^ 2
  radial : ∃ B : ℝ, ∀ x : ℝ, 1 / 2 ≤ x → x < 1 → ‖Φ (x : ℂ)‖ ≤ B
  l2 : CircleIntegrable (fun z => ‖Φ z‖ ^ 2) 0 1

namespace IsHardyDisc

variable {Φ : ℂ → ℂ} (h : IsHardyDisc Φ)

include h

theorem circleIntegrable : CircleIntegrable Φ 0 1 := by
  have hm : Measurable fun θ : ℝ => Φ (circleMap 0 1 θ) :=
    h.meas.comp (continuous_circleMap 0 1).measurable
  have hb : IntervalIntegrable (fun θ : ℝ => (1 + ‖Φ (circleMap 0 1 θ)‖ ^ 2) / 2) volume 0 (2 * π) :=
    (intervalIntegrable_const.add h.l2).div_const 2
  refine hb.mono_fun hm.aestronglyMeasurable (Eventually.of_forall fun θ => ?_)
  have h0 : 0 ≤ (1 + ‖Φ (circleMap 0 1 θ)‖ ^ 2) / 2 := by positivity
  change ‖Φ (circleMap 0 1 θ)‖ ≤ ‖(1 + ‖Φ (circleMap 0 1 θ)‖ ^ 2) / 2‖
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  nlinarith [sq_nonneg (‖Φ (circleMap 0 1 θ)‖ - 1), norm_nonneg (Φ (circleMap 0 1 θ))]

/-- Averages of `|Φ + b|²`. -/
theorem circleIntegrable_add_sq (b : ℂ) :
    CircleIntegrable (fun z => ‖Φ z + b‖ ^ 2) 0 1 ∧
      Real.circleAverage (fun z => ‖Φ z + b‖ ^ 2) 0 1 =
        Real.circleAverage (fun z => ‖Φ z‖ ^ 2) 0 1 +
          2 * (conj b * Real.circleAverage Φ 0 1).re + ‖b‖ ^ 2 := by
  have hL : CircleIntegrable (fun z => reMul b (Φ z)) 0 1 :=
    ⟨(reMul b).integrable_comp h.circleIntegrable.1, (reMul b).integrable_comp h.circleIntegrable.2⟩
  have hL2 : CircleIntegrable (fun z => (2 : ℝ) * reMul b (Φ z)) 0 1 :=
    IntervalIntegrable.const_mul hL 2
  have hC : CircleIntegrable (fun _ : ℂ => ‖b‖ ^ 2) 0 1 := intervalIntegrable_const
  have hS : CircleIntegrable (fun z => ‖Φ z‖ ^ 2 + (2 : ℝ) * reMul b (Φ z)) 0 1 :=
    IntervalIntegrable.add h.l2 hL2
  have hfun : (fun z => ‖Φ z + b‖ ^ 2) =
      fun z => ‖Φ z‖ ^ 2 + (2 : ℝ) * reMul b (Φ z) + ‖b‖ ^ 2 := by
    funext z
    rw [norm_add_sq, reMul_apply]
  rw [hfun]
  refine ⟨IntervalIntegrable.add hS hC, ?_⟩
  rw [Real.circleAverage_fun_add hS hC, Real.circleAverage_fun_add h.l2 hL2, Real.circleAverage_const]
  have e : Real.circleAverage (fun z => (2 : ℝ) * reMul b (Φ z)) 0 1 =
      2 * (conj b * Real.circleAverage Φ 0 1).re := by
    have e1 : (fun z => (2 : ℝ) * reMul b (Φ z)) = fun z => (2 : ℝ) • (reMul b ∘ Φ) z := by
      funext z
      simp
    rw [e1, Real.circleAverage_fun_smul, (reMul b).circleAverage_comp_comm h.circleIntegrable,
      reMul_apply]
    simp
  rw [e]

/-- A large shift of a Hardy function is a disc datum. -/
theorem exists_isDiscDatum_add :
    ∃ B : ℝ, ∀ b : ℂ, B < ‖b‖ → Φ 0 + b ≠ 0 → IsDiscDatum fun u => Φ u + b := by
  obtain ⟨B, hB⟩ := h.radial
  obtain ⟨A, hA0, hA⟩ := h.up
  refine ⟨B, fun b hb hne => ⟨h.diff.add_const b, h.meas.add_const b, hne, ?_, ?_⟩⟩
  · refine ⟨Real.log (A + 4 * ‖b‖ + 4), fun w hw hw1 => ?_⟩
    set d := ‖1 - w‖ with hd
    have hdpos : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hw1))
    have hd2 : d ≤ 2 := by
      calc d ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    have hdsq : d ^ 2 ≤ 4 := by nlinarith
    have hK : 0 < A + 4 * ‖b‖ + 4 := by positivity
    have hle : ‖Φ w + b‖ ≤ (A + 4 * ‖b‖ + 4) / d ^ 2 := by
      have h1 := hA w hw hw1
      have h2 : ‖b‖ ≤ 4 * ‖b‖ / d ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [norm_nonneg b]
      calc ‖Φ w + b‖ ≤ ‖Φ w‖ + ‖b‖ := norm_add_le _ _
        _ ≤ A / d ^ 2 + 4 * ‖b‖ / d ^ 2 := add_le_add h1 h2
        _ = (A + 4 * ‖b‖) / d ^ 2 := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)
    have e : Real.log (A + 4 * ‖b‖ + 4) - 2 * Real.log d =
        Real.log ((A + 4 * ‖b‖ + 4) / d ^ 2) := by
      rw [Real.log_div hK.ne' (by positivity), Real.log_pow]
      norm_num
    rw [e]
    rcases eq_or_ne ‖Φ w + b‖ 0 with h0 | h0
    · rw [h0, Real.log_zero]
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ (by positivity)]
      nlinarith [norm_nonneg b]
    · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)) hle
  · refine ⟨‖b‖ - B, 1 / 2, by linarith, le_rfl, by norm_num, fun x hx hx1 => ?_⟩
    have h1 := hB x hx hx1
    have h2 : ‖b‖ - ‖Φ (x : ℂ)‖ ≤ ‖Φ (x : ℂ) + b‖ := by
      have := norm_sub_norm_le b (-Φ (x : ℂ))
      rw [norm_neg, sub_neg_eq_add, add_comm] at this
      exact this
    linarith

/-- **The mean value property.** -/
theorem circleAverage_eq : Real.circleAverage Φ 0 1 = Φ 0 := by
  by_contra hne
  set D : ℂ := Φ 0 - Real.circleAverage Φ 0 1 with hD
  have hD0 : D ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hDn : 0 < ‖D‖ := norm_pos_iff.mpr hD0
  obtain ⟨B, hB⟩ := h.exists_isDiscDatum_add
  set C : ℝ := Real.circleAverage (fun z => ‖Φ z‖ ^ 2) 0 1 with hC
  obtain ⟨t, ht1, ht2, ht3⟩ : ∃ t : ℝ, B < t * ‖D‖ ∧ ‖Φ 0‖ < t * ‖D‖ ∧ C < 2 * t * ‖D‖ ^ 2 := by
    have hT : Tendsto (fun t : ℝ => t * ‖D‖) atTop atTop := tendsto_id.atTop_mul_const hDn
    have hT2 : Tendsto (fun t : ℝ => 2 * t * ‖D‖ ^ 2) atTop atTop := by
      have := (tendsto_id.atTop_mul_const (show (0 : ℝ) < 2 * ‖D‖ ^ 2 by positivity))
      refine this.congr fun t => ?_
      simp only [id]
      ring
    obtain ⟨t, h1, h2, h3⟩ := ((hT.eventually_gt_atTop B).and
      ((hT.eventually_gt_atTop ‖Φ 0‖).and (hT2.eventually_gt_atTop C))).exists
    exact ⟨t, h1, h2, h3⟩
  have htpos : 0 < t := by
    by_contra hneg
    push Not at hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg hDn.le
    linarith [norm_nonneg (Φ 0)]
  set b : ℂ := (t : ℂ) * D with hb
  have hbn : ‖b‖ = t * ‖D‖ := by
    rw [hb, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
  have hne0 : Φ 0 + b ≠ 0 := by
    intro h0
    have h1 : b = -Φ 0 := by linear_combination h0
    rw [h1, norm_neg] at hbn
    linarith
  have hDatum := hB b (by rw [hbn]; exact ht1) hne0
  obtain ⟨hl2, hav⟩ := h.circleIntegrable_add_sq b
  have hJ := hDatum.norm_sq_le_circleAverage hl2
  rw [hav, norm_add_sq] at hJ
  have e1 : (conj b * D).re = t * ‖D‖ ^ 2 := by
    rw [hb, map_mul, Complex.conj_ofReal, mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have e2 : (conj b * Φ 0).re - (conj b * Real.circleAverage Φ 0 1).re = (conj b * D).re := by
    rw [hD, mul_sub, Complex.sub_re]
  have hnn : 0 ≤ ‖Φ 0‖ ^ 2 := sq_nonneg _
  nlinarith

/-- `avg |Φ − Φ(0)|² = avg |Φ|² − |Φ(0)|²`. -/
theorem circleAverage_norm_sub_sq :
    CircleIntegrable (fun z => ‖Φ z - Φ 0‖ ^ 2) 0 1 ∧
      Real.circleAverage (fun z => ‖Φ z - Φ 0‖ ^ 2) 0 1 =
        Real.circleAverage (fun z => ‖Φ z‖ ^ 2) 0 1 - ‖Φ 0‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := h.circleIntegrable_add_sq (-Φ 0)
  simp only [← sub_eq_add_neg] at h1 h2
  refine ⟨h1, ?_⟩
  rw [h2, h.circleAverage_eq, norm_neg]
  have e : (conj (-Φ 0) * Φ 0).re = -‖Φ 0‖ ^ 2 := by
    rw [map_neg, neg_mul, Complex.conj_mul', Complex.neg_re, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [e]
  ring

/-- **Peeling a Taylor coefficient** keeps the class. -/
theorem dslope : IsHardyDisc (dslope Φ 0) := by
  have hmem : ({1}ᶜ : Set ℂ) ∈ 𝓝 (0 : ℂ) :=
    isOpen_compl_singleton.mem_nhds (by simp)
  have hd : DifferentiableOn ℂ (_root_.dslope Φ 0) {1}ᶜ := (Complex.differentiableOn_dslope hmem).mpr h.diff
  have hval : ∀ w : ℂ, w ≠ 0 → _root_.dslope Φ 0 w = w⁻¹ * (Φ w - Φ 0) := fun w hw => by
    rw [dslope_of_ne _ hw, slope_def_module, sub_zero, smul_eq_mul]
  refine ⟨hd, ?_, ?_, ?_, ?_⟩
  · have hs : Measurable (slope Φ 0) := by
      have : slope Φ 0 = fun b => (b - 0)⁻¹ • (Φ b - Φ 0) := by
        funext b
        rw [slope_def_module]
      rw [this]
      exact (measurable_id.sub_const 0).inv.smul (h.meas.sub_const _)
    have e : _root_.dslope Φ 0 = fun b => if b = 0 then deriv Φ 0 else slope Φ 0 b := by
      funext b
      by_cases hb : b = 0
      · subst hb
        simp
      · rw [dslope_of_ne _ hb, if_neg hb]
    rw [e]
    exact Measurable.ite (measurableSet_singleton 0) measurable_const hs
  · obtain ⟨A, hA0, hA⟩ := h.up
    have hsub : closedBall (0 : ℂ) (1 / 2) ⊆ {1}ᶜ := fun z hz hz1 => by
      have : z = 1 := hz1
      rw [this] at hz
      simp at hz
      norm_num at hz
    obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn
      (hd.continuousOn.mono hsub)
    have hK0 : 0 ≤ max K 0 := le_max_right _ _
    refine ⟨2 * A + 8 * ‖Φ 0‖ + 4 * max K 0, by positivity, fun w hw hw1 => ?_⟩
    set d := ‖1 - w‖ with hd'
    have hdpos : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hw1))
    have hd2 : d ≤ 2 := by
      calc d ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    have hdsq : d ^ 2 ≤ 4 := by nlinarith
    rw [le_div_iff₀ (by positivity)]
    by_cases hsmall : ‖w‖ ≤ 1 / 2
    · have h1 := (hK w (by simpa using hsmall)).trans (le_max_left K 0)
      have h2 := norm_nonneg (Φ 0)
      nlinarith [mul_le_mul h1 hdsq (sq_nonneg d) hK0, sq_nonneg d]
    · push Not at hsmall
      have hw0 : w ≠ 0 := fun h0 => by
        rw [h0, norm_zero] at hsmall
        linarith
      rw [hval w hw0, norm_mul, norm_inv]
      have h1 : ‖w‖⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      have h2 : ‖Φ w - Φ 0‖ ≤ A / d ^ 2 + ‖Φ 0‖ := (norm_sub_le _ _).trans (by linarith [hA w hw hw1])
      have h3 : (A / d ^ 2) * d ^ 2 = A := by field_simp
      have hdp : 0 < d ^ 2 := by positivity
      calc ‖w‖⁻¹ * ‖Φ w - Φ 0‖ * d ^ 2 ≤ 2 * (A / d ^ 2 + ‖Φ 0‖) * d ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)) hdp.le
        _ = 2 * A + 2 * ‖Φ 0‖ * d ^ 2 := by rw [mul_add 2, add_mul, mul_assoc 2 (A / d ^ 2), h3]
        _ ≤ _ := by nlinarith [norm_nonneg (Φ 0)]
  · obtain ⟨B, hB⟩ := h.radial
    refine ⟨2 * (B + ‖Φ 0‖), fun x hx hx1 => ?_⟩
    have hx0 : (x : ℂ) ≠ 0 := by
      intro h0
      have : x = 0 := by exact_mod_cast h0
      linarith
    rw [hval _ hx0, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have h1 : x⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have h2 : ‖Φ (x : ℂ) - Φ 0‖ ≤ B + ‖Φ 0‖ := (norm_sub_le _ _).trans (by linarith [hB x hx hx1])
    exact mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
  · have h1 := h.circleAverage_norm_sub_sq.1
    have e : (fun θ : ℝ => ‖_root_.dslope Φ 0 (circleMap 0 1 θ)‖ ^ 2) =
        fun θ => ‖Φ (circleMap 0 1 θ) - Φ 0‖ ^ 2 := by
      funext θ
      have hn := norm_circleMap_zero_one θ
      have h0 : circleMap 0 1 θ ≠ 0 := fun h0 => by
        rw [h0, norm_zero] at hn
        exact zero_ne_one hn
      rw [hval _ h0, norm_mul, norm_inv, hn, inv_one, one_mul]
    unfold CircleIntegrable at h1 ⊢
    rw [e]
    exact h1

/-- One step of Parseval. -/
theorem circleAverage_dslope :
    Real.circleAverage (fun z => ‖_root_.dslope Φ 0 z‖ ^ 2) 0 1 =
      Real.circleAverage (fun z => ‖Φ z‖ ^ 2) 0 1 - ‖Φ 0‖ ^ 2 := by
  rw [← h.circleAverage_norm_sub_sq.2]
  refine Real.circleAverage_congr_sphere fun z hz => ?_
  have hn : ‖z‖ = 1 := by simpa using hz
  have h0 : z ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  rw [dslope_of_ne _ h0, slope_def_module, sub_zero, smul_eq_mul, norm_mul, norm_inv, hn, inv_one, one_mul]

end IsHardyDisc

/-! ### Parseval and the reproducing bound -/

/-- `Φ` with its first `n` Taylor terms peeled off. -/
def peel (Φ : ℂ → ℂ) (n : ℕ) : ℂ → ℂ := (Function.swap dslope (0 : ℂ))^[n] Φ

theorem peel_zero (Φ : ℂ → ℂ) : peel Φ 0 = Φ := rfl

theorem peel_succ (Φ : ℂ → ℂ) (n : ℕ) : peel Φ (n + 1) = dslope (peel Φ n) 0 := by
  rw [peel, Function.iterate_succ_apply']
  rfl

/-- The Taylor coefficient of `Φ` at `0`. -/
def taylorCoeff (Φ : ℂ → ℂ) (n : ℕ) : ℂ := peel Φ n 0

namespace IsHardyDisc

variable {Φ : ℂ → ℂ} (h : IsHardyDisc Φ)

include h

theorem peel (n : ℕ) : IsHardyDisc (GaloisForLFunctions.ArithmeticInnerFunctionTheory.peel Φ n) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [peel_succ]
    exact ih.dslope

/-- **Parseval.** `avg |Φ|² = Σ_{k<n} |a_k|² + avg |Φ_n|²`. -/
theorem circleAverage_norm_sq_eq (n : ℕ) :
    Real.circleAverage (fun z => ‖Φ z‖ ^ 2) 0 1 =
      ∑ k ∈ Finset.range n, ‖taylorCoeff Φ k‖ ^ 2 +
        Real.circleAverage (fun z => ‖GaloisForLFunctions.ArithmeticInnerFunctionTheory.peel Φ n z‖ ^ 2) 0 1 := by
  induction n with
  | zero => simp [peel_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, peel_succ, (h.peel n).circleAverage_dslope, ih, taylorCoeff]
    ring

/-- **Bessel.** -/
theorem sum_norm_sq_le (n : ℕ) :
    ∑ k ∈ Finset.range n, ‖taylorCoeff Φ k‖ ^ 2 ≤ Real.circleAverage (fun z => ‖Φ z‖ ^ 2) 0 1 := by
  rw [h.circleAverage_norm_sq_eq n]
  have : 0 ≤ Real.circleAverage
      (fun z => ‖GaloisForLFunctions.ArithmeticInnerFunctionTheory.peel Φ n z‖ ^ 2) 0 1 :=
    Real.circleAverage_nonneg_of_nonneg fun z _ => sq_nonneg _
  linarith

/-- **The Taylor series converges on the disc.** -/
theorem hasSum_taylor {u : ℂ} (hu : ‖u‖ < 1) : HasSum (fun k => u ^ k * taylorCoeff Φ k) (Φ u) := by
  obtain ⟨R, hR1, hR2⟩ := exists_between hu
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg u) hR1
  lift R to NNReal using hR0.le
  have hsub : closedBall (0 : ℂ) R ⊆ {1}ᶜ := fun z hz hz1 => by
    have : z = 1 := hz1
    rw [this] at hz
    simp at hz
    have h3 : (R : ℝ) < 1 := hR2
    linarith
  have hp := (h.diff.mono hsub).hasFPowerSeriesOnBall (by exact_mod_cast hR0)
  set p := cauchyPowerSeries Φ 0 R with hpd
  have hcoeff : ∀ k, taylorCoeff Φ k = p.coeff k := fun k => by
    have h1 := hp.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope k
    have h2 := h1.coeff_zero (1 : Fin 0 → ℂ)
    have h3 := p.coeff_iterate_fslope k 0
    rw [zero_add] at h3
    calc taylorCoeff Φ k = (FormalMultilinearSeries.fslope^[k] p) 0 1 := h2.symm
      _ = (FormalMultilinearSeries.fslope^[k] p).coeff 0 := rfl
      _ = p.coeff k := h3
  have hmem : u ∈ Metric.eball (0 : ℂ) R := by
    rw [Metric.mem_eball, edist_zero_right, ← ENNReal.ofReal_coe_nnreal, ← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff hR0).mpr hR1
  have hs := hp.hasSum hmem
  rw [zero_add] at hs
  have e : ∀ n, p n (fun _ => u) = u ^ n * taylorCoeff Φ n := fun n => by
    rw [p.apply_eq_prod_smul_coeff, hcoeff n]
    simp
  simpa only [e] using hs

/-- **The reproducing bound.** `|Φ(u) − Φ(0)|² ≤ (avg |Φ|² − |Φ(0)|²) |u|²/(1 − |u|²)`. -/
theorem norm_sub_sq_le {u : ℂ} (hu : ‖u‖ < 1) :
    ‖Φ u - Φ 0‖ ^ 2 ≤ (Real.circleAverage (fun z => ‖Φ z‖ ^ 2) 0 1 - ‖Φ 0‖ ^ 2) *
      (‖u‖ ^ 2 / (1 - ‖u‖ ^ 2)) := by
  set C := Real.circleAverage (fun z => ‖Φ z‖ ^ 2) 0 1 - ‖Φ 0‖ ^ 2 with hC
  have hu2 : ‖u‖ ^ 2 < 1 := by nlinarith [norm_nonneg u]
  have hden : 0 < 1 - ‖u‖ ^ 2 := by linarith
  have ha0 : taylorCoeff Φ 0 = Φ 0 := rfl
  have hBessel : ∀ n, ∑ k ∈ Finset.range n, ‖taylorCoeff Φ (k + 1)‖ ^ 2 ≤ C := fun n => by
    have h1 := h.sum_norm_sq_le (n + 1)
    rw [Finset.sum_range_succ', ha0] at h1
    rw [hC]
    linarith
  have hC0 : 0 ≤ C := by simpa using hBessel 0
  -- the partial sums of the Taylor series without its constant term
  have hT := (h.hasSum_taylor hu).tendsto_sum_nat
  have hT1 : Tendsto (fun n => ∑ k ∈ Finset.range n, u ^ (k + 1) * taylorCoeff Φ (k + 1)) atTop
      (𝓝 (Φ u - Φ 0)) := by
    have h2 := ((tendsto_add_atTop_iff_nat 1).mpr hT).sub_const (Φ 0)
    refine h2.congr fun n => ?_
    rw [Finset.sum_range_succ']
    simp [ha0]
  have hbound : ∀ n, ‖∑ k ∈ Finset.range n, u ^ (k + 1) * taylorCoeff Φ (k + 1)‖ ^ 2 ≤
      C * (‖u‖ ^ 2 / (1 - ‖u‖ ^ 2)) := fun n => by
    have h1 : ‖∑ k ∈ Finset.range n, u ^ (k + 1) * taylorCoeff Φ (k + 1)‖ ≤
        ∑ k ∈ Finset.range n, ‖u‖ ^ (k + 1) * ‖taylorCoeff Φ (k + 1)‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => by
        rw [norm_mul, norm_pow]))
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n) (fun k => ‖u‖ ^ (k + 1))
      (fun k => ‖taylorCoeff Φ (k + 1)‖)
    have hgeom : ∑ k ∈ Finset.range n, (‖u‖ ^ (k + 1)) ^ 2 ≤ ‖u‖ ^ 2 / (1 - ‖u‖ ^ 2) := by
      rw [le_div_iff₀ hden]
      have e : ∀ k, (‖u‖ ^ (k + 1)) ^ 2 = ‖u‖ ^ 2 * (‖u‖ ^ 2) ^ k := fun k => by ring
      simp only [e]
      rw [← Finset.mul_sum, mul_assoc, geom_sum_mul_neg]
      nlinarith [pow_nonneg (sq_nonneg ‖u‖) n, sq_nonneg ‖u‖]
    have h3 : 0 ≤ ∑ k ∈ Finset.range n, ‖u‖ ^ (k + 1) * ‖taylorCoeff Φ (k + 1)‖ :=
      Finset.sum_nonneg fun k _ => by positivity
    calc ‖∑ k ∈ Finset.range n, u ^ (k + 1) * taylorCoeff Φ (k + 1)‖ ^ 2
        ≤ (∑ k ∈ Finset.range n, ‖u‖ ^ (k + 1) * ‖taylorCoeff Φ (k + 1)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ k ∈ Finset.range n, (‖u‖ ^ (k + 1)) ^ 2) *
            ∑ k ∈ Finset.range n, ‖taylorCoeff Φ (k + 1)‖ ^ 2 := h2
      _ ≤ (‖u‖ ^ 2 / (1 - ‖u‖ ^ 2)) * C :=
          mul_le_mul hgeom (hBessel n) (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = _ := mul_comm _ _
  exact le_of_tendsto' ((hT1.norm).pow 2) hbound

end IsHardyDisc

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
