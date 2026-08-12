import GaloisForLFunctions.RHTower.SuzukiOriginRemainderFirstJet
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Exact regularity of Suzuki's equation-(2.2) remainder

This module finishes the origin analysis of the literal remainder in Suzuki,
*A Hilbert space associated with the Weil distribution and the Riemann hypothesis*
(arXiv:2606.09096).  It proves directly from the prime--Lerch source formula that the even
remainder is globally `C²`, identifies its first and second derivatives through the removable
origin singularity, and strengthens the paper's `r(t) = O(t²)` assertion to the sharp limit

```text
r(t) / t² -> -7/8.
```

All results are unconditional.  In particular, no regularity of the remainder is assumed in order
to prove its regularity.
-/

open Filter Topology Set Asymptotics
open scoped Asymptotics

noncomputable section

namespace GaloisForLFunctions.RHTower

private theorem summable_one_div_suzukiLerchExp_sq :
    Summable (fun k : ℕ => 1 / (lerchExp k) ^ 2) := by
  have hshift : Summable (fun k : ℕ => 1 / |(k : ℝ) + 1 / 4| ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow (1 / 4) 2).2 (by norm_num)
  have hpow : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1 / 4) ^ 2) := by
    convert hshift using 1
    ext k
    rw [abs_of_pos (by positivity : 0 < (k : ℝ) + 1 / 4), Real.rpow_two]
  have heq : (fun k : ℕ => 1 / (lerchExp k) ^ 2) =
      fun k : ℕ => (1 / 4 : ℝ) * (1 / ((k : ℝ) + 1 / 4) ^ 2) := by
    funext k
    rw [lerchExp_sq]
    have hk : ((k : ℝ) + 1 / 4) ^ 2 ≠ 0 := by positivity
    field_simp
  rw [heq]
  exact hpow.mul_left (1 / 4 : ℝ)

theorem tendsto_screwLerchTail_nhdsGT_zero :
    Tendsto screwLerchTail (𝓝[>] 0) (𝓝 (screwLerchTail 0)) := by
  have hpoint (k : ℕ) : Tendsto
      (fun t : ℝ => Real.exp (-(lerchExp k * t)) / (lerchExp k) ^ 2)
      (𝓝[>] 0) (𝓝 (1 / (lerchExp k) ^ 2)) := by
    have hcont : Continuous
        (fun t : ℝ => Real.exp (-(lerchExp k * t)) / (lerchExp k) ^ 2) := by fun_prop
    have h := hcont.continuousAt.tendsto (x := (0 : ℝ))
    have h0 : Tendsto
        (fun t : ℝ => Real.exp (-(lerchExp k * t)) / (lerchExp k) ^ 2)
        (𝓝 (0 : ℝ)) (𝓝 (1 / (lerchExp k) ^ 2)) := by simpa using h
    exact tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi 0) h0
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k : ℕ,
      ‖Real.exp (-(lerchExp k * t)) / (lerchExp k) ^ 2‖ ≤
        1 / (lerchExp k) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht k
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_nonneg _) (by positivity))]
    have hexp : Real.exp (-(lerchExp k * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (mul_nonneg (lerchExp_pos k).le ht.le)
    exact div_le_div_of_nonneg_right hexp (by positivity)
  have h := tendsto_tsum_of_dominated_convergence
    summable_one_div_suzukiLerchExp_sq hpoint hbound
  unfold screwLerchTail
  simpa using h

theorem tendsto_suzukiOriginRemainderPos_nhdsGT_zero :
    Tendsto suzukiOriginRemainderPos (𝓝[>] 0) (𝓝 0) := by
  unfold suzukiOriginRemainderPos screwLerchConst
  have htlog0 : Tendsto (fun t : ℝ => t * Real.log t) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa using Real.continuous_mul_log.continuousAt.tendsto (x := (0 : ℝ))
  have htlog : Tendsto (fun t : ℝ => t * Real.log t) (𝓝[>] 0) (𝓝 0) :=
    htlog0.mono_left nhdsWithin_le_nhds
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hexp : Tendsto
      (fun t : ℝ => (-4 : ℝ) * (Real.exp (t / 2) + Real.exp (-(t / 2)) - 2))
      (𝓝[>] 0) (𝓝 0) := by
    have hp : Tendsto (fun t : ℝ => Real.exp (t / 2)) (𝓝[>] 0) (𝓝 1) := by
      have hc : ContinuousAt (fun t : ℝ => Real.exp (t / 2)) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hm : Tendsto (fun t : ℝ => Real.exp (-(t / 2))) (𝓝[>] 0) (𝓝 1) := by
      have hc : ContinuousAt (fun t : ℝ => Real.exp (-(t / 2))) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have h := ((hp.add hm).sub_const 2).const_mul (-4 : ℝ)
    convert h using 1
    all_goals norm_num
  have hlin : Tendsto (fun t : ℝ => screwLinearCoeff / 2 * t)
      (𝓝[>] 0) (𝓝 0) := by simpa using tendsto_const_nhds.mul hid
  have hA : Tendsto (fun t : ℝ => suzukiOriginLinearCoeff * t)
      (𝓝[>] 0) (𝓝 0) := by simpa using tendsto_const_nhds.mul hid
  have h := ((((hexp.sub hlin).sub_const (screwLerchTail 0)).add
    tendsto_screwLerchTail_nhdsGT_zero).sub
      (htlog.const_mul (1 / 2 : ℝ))).sub hA
  convert h using 1
  · ext t
    ring
  · norm_num

@[simp] theorem suzukiOriginRemainderPos_zero : suzukiOriginRemainderPos 0 = 0 := by
  unfold suzukiOriginRemainderPos screwLerchConst
  norm_num

@[simp] theorem suzukiOriginRemainder_zero : suzukiOriginRemainder 0 = 0 := by
  simp [suzukiOriginRemainder]

theorem hasDerivAt_suzukiOriginRemainderPos_source {t : ℝ} (ht : 0 < t) :
    HasDerivAt suzukiOriginRemainderPos (suzukiOriginRemainderFirstJet t) t := by
  have hlin : HasDerivAt (fun x : ℝ => screwLinearCoeff / 2 * x)
      (screwLinearCoeff / 2) t := by
    simpa using (hasDerivAt_id' t).const_mul (screwLinearCoeff / 2)
  have htlog : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * x * Real.log x)
      ((1 / 2 : ℝ) * (Real.log t + 1)) t := by
    simpa only [Pi.mul_apply, one_mul, mul_inv_cancel₀ ht.ne', mul_add, mul_one, mul_assoc] using
      ((hasDerivAt_id' t).mul (Real.hasDerivAt_log ht.ne')).const_mul (1 / 2 : ℝ)
  have hA : HasDerivAt (fun x : ℝ => suzukiOriginLinearCoeff * x)
      suzukiOriginLinearCoeff t := by
    simpa using (hasDerivAt_id' t).const_mul suzukiOriginLinearCoeff
  unfold suzukiOriginRemainderPos suzukiOriginRemainderFirstJet
  convert (((((hasDerivAt_screwExpBlock t).sub hlin).sub_const screwLerchConst).add
    (hasDerivAt_screwLerchTail ht)).sub htlog).sub hA using 1
  all_goals rfl

theorem hasDerivAt_suzukiOriginRemainderFirstJet {t : ℝ} (ht : 0 < t) :
    HasDerivAt suzukiOriginRemainderFirstJet (suzukiOriginRemainderCurvature t) t := by
  have hExp : HasDerivAt
      (fun x : ℝ => -2 * Real.exp (x / 2) + 2 * Real.exp (-(x / 2)))
      (-(Real.exp (t / 2) + Real.exp (-(t / 2)))) t := by
    convert ((hasDerivAt_exp_half t).const_mul (-2 : ℝ)).add
      ((hasDerivAt_exp_neg_half t).const_mul 2) using 1
    all_goals first | rfl | ring
  have hlog : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * (Real.log x + 1))
      (1 / (2 * t)) t := by
    convert ((Real.hasDerivAt_log ht.ne').add_const 1).const_mul (1 / 2 : ℝ) using 1
    all_goals try rfl
    field_simp [ht.ne']
  have hraw : HasDerivAt suzukiOriginRemainderFirstJet
      (-(Real.exp (t / 2) + Real.exp (-(t / 2))) + screwLerchTail₂ t -
        1 / (2 * t)) t := by
    unfold suzukiOriginRemainderFirstJet
    convert ((((hExp.sub_const (screwLinearCoeff / 2)).add
      (hasDerivAt_screwLerchTail₁ ht)).sub hlog).sub_const suzukiOriginLinearCoeff) using 1
    all_goals rfl
  convert hraw using 1
  rw [suzukiOriginRemainderCurvature_of_ne ht.ne', abs_of_pos ht,
    screwRegularKernel_eq_tailForm ht, screwLerchTail₂_eq ht]
  ring

theorem tendsto_suzukiOriginRemainderPos_div_id :
    Tendsto (fun t : ℝ => suzukiOriginRemainderPos t / t)
      (𝓝[>] 0) (𝓝 0) := by
  apply HasDerivAt.lhopital_zero_nhdsGT
    (f' := suzukiOriginRemainderFirstJet) (g' := fun _ => 1)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact hasDerivAt_suzukiOriginRemainderPos_source ht
  · exact Eventually.of_forall hasDerivAt_id'
  · simp
  · exact tendsto_suzukiOriginRemainderPos_nhdsGT_zero
  · exact tendsto_id.mono_left nhdsWithin_le_nhds
  · simpa using tendsto_suzukiOriginRemainderFirstJet

/-- Odd first derivative of Suzuki's even origin remainder, including its removable value at zero. -/
def suzukiOriginRemainderDerivative (t : ℝ) : ℝ :=
  (SignType.sign t : ℝ) * suzukiOriginRemainderFirstJet |t|

@[simp] theorem suzukiOriginRemainderDerivative_zero :
    suzukiOriginRemainderDerivative 0 = 0 := by
  simp [suzukiOriginRemainderDerivative]

theorem tendsto_suzukiOriginRemainderDerivative_nhdsNE_zero :
    Tendsto suzukiOriginRemainderDerivative (𝓝[≠] 0) (𝓝 0) := by
  have hjet : Tendsto (fun t : ℝ => suzukiOriginRemainderFirstJet |t|)
      (𝓝[≠] 0) (𝓝 0) :=
    tendsto_suzukiOriginRemainderFirstJet.comp tendsto_abs_nhdsNE_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun t : ℝ => ‖suzukiOriginRemainderFirstJet |t|‖)
  · filter_upwards [] with t
    positivity
  · filter_upwards [] with t
    rw [suzukiOriginRemainderDerivative, norm_mul]
    rcases lt_trichotomy t 0 with ht | ht | ht
    · have hnot : ¬ 0 < t := not_lt_of_ge ht.le
      simp [SignType.sign, hnot, ht]
    · simp [ht]
    · simp [SignType.sign, ht]
  · exact tendsto_zero_iff_norm_tendsto_zero.mp hjet

theorem continuousAt_suzukiOriginRemainderDerivative_zero :
    ContinuousAt suzukiOriginRemainderDerivative 0 := by
  rw [continuousAt_iff_punctured_nhds]
  simpa using tendsto_suzukiOriginRemainderDerivative_nhdsNE_zero

theorem hasDerivAt_suzukiOriginRemainder_zero :
    HasDerivAt suzukiOriginRemainder 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hquot : Tendsto
      (fun t : ℝ => suzukiOriginRemainderPos |t| / |t|)
      (𝓝[≠] 0) (𝓝 0) :=
    tendsto_suzukiOriginRemainderPos_div_id.comp tendsto_abs_nhdsNE_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun t : ℝ => ‖suzukiOriginRemainderPos |t| / |t|‖)
  · filter_upwards [] with t
    positivity
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [suzukiOriginRemainder_zero]
    simp [suzukiOriginRemainder, div_eq_mul_inv]
    rw [mul_comm]
  · exact tendsto_zero_iff_norm_tendsto_zero.mp hquot

theorem hasDerivAt_suzukiOriginRemainder_of_pos {t : ℝ} (ht : 0 < t) :
    HasDerivAt suzukiOriginRemainder (suzukiOriginRemainderDerivative t) t := by
  have h := (hasDerivAt_suzukiOriginRemainderPos_source
      (show 0 < |t| by simpa [abs_of_pos ht] using ht)).comp t
    (hasDerivAt_abs_pos ht)
  change HasDerivAt (suzukiOriginRemainderPos ∘ abs)
    (suzukiOriginRemainderDerivative t) t
  simpa [suzukiOriginRemainderDerivative, ht, abs_of_pos] using h

theorem hasDerivAt_suzukiOriginRemainder_of_neg {t : ℝ} (ht : t < 0) :
    HasDerivAt suzukiOriginRemainder (suzukiOriginRemainderDerivative t) t := by
  have hpos : 0 < |t| := abs_pos.mpr ht.ne
  have h := (hasDerivAt_suzukiOriginRemainderPos_source hpos).comp t
    (hasDerivAt_abs_neg ht)
  change HasDerivAt (suzukiOriginRemainderPos ∘ abs)
    (suzukiOriginRemainderDerivative t) t
  simpa [suzukiOriginRemainderDerivative, ht, abs_of_neg] using h

theorem hasDerivAt_suzukiOriginRemainder (t : ℝ) :
    HasDerivAt suzukiOriginRemainder (suzukiOriginRemainderDerivative t) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · exact hasDerivAt_suzukiOriginRemainder_of_neg ht
  · simpa [ht] using hasDerivAt_suzukiOriginRemainder_zero
  · exact hasDerivAt_suzukiOriginRemainder_of_pos ht

theorem deriv_suzukiOriginRemainder :
    deriv suzukiOriginRemainder = suzukiOriginRemainderDerivative := by
  funext t
  exact (hasDerivAt_suzukiOriginRemainder t).deriv

theorem tendsto_suzukiOriginRemainderFirstJet_div_id :
    Tendsto (fun t : ℝ => suzukiOriginRemainderFirstJet t / t)
      (𝓝[>] 0) (𝓝 (-7 / 4 : ℝ)) := by
  apply HasDerivAt.lhopital_zero_nhdsGT
    (f' := suzukiOriginRemainderCurvature) (g' := fun _ => 1)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact hasDerivAt_suzukiOriginRemainderFirstJet ht
  · exact Eventually.of_forall hasDerivAt_id'
  · simp
  · exact tendsto_suzukiOriginRemainderFirstJet
  · exact tendsto_id.mono_left nhdsWithin_le_nhds
  · simpa using continuousAt_suzukiOriginRemainderCurvature_zero.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)

@[simp] theorem suzukiOriginRemainderCurvature_neg (t : ℝ) :
    suzukiOriginRemainderCurvature (-t) = suzukiOriginRemainderCurvature t := by
  simp [suzukiOriginRemainderCurvature]

theorem hasDerivAt_suzukiOriginRemainderDerivative_zero :
    HasDerivAt suzukiOriginRemainderDerivative (-7 / 4 : ℝ) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hquot : Tendsto
      (fun t : ℝ => suzukiOriginRemainderFirstJet |t| / |t|)
      (𝓝[≠] 0) (𝓝 (-7 / 4 : ℝ)) :=
    tendsto_suzukiOriginRemainderFirstJet_div_id.comp tendsto_abs_nhdsNE_zero
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  rcases lt_trichotomy t 0 with htneg | hteq | htpos
  · have hnot : ¬ 0 < t := not_lt_of_ge htneg.le
    simp [suzukiOriginRemainderDerivative, htneg, hnot, SignType.sign,
      abs_of_neg htneg, smul_eq_mul, div_eq_mul_inv]
    field_simp
  · exact (ht0 hteq).elim
  · simp [suzukiOriginRemainderDerivative, htpos, SignType.sign,
      abs_of_pos htpos, smul_eq_mul, div_eq_mul_inv]
    ring

theorem hasDerivAt_suzukiOriginRemainderDerivative_of_pos {t : ℝ} (ht : 0 < t) :
    HasDerivAt suzukiOriginRemainderDerivative (suzukiOriginRemainderCurvature t) t := by
  apply (hasDerivAt_suzukiOriginRemainderFirstJet ht).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  have hspos : 0 < s := hs
  simp [suzukiOriginRemainderDerivative, hspos, SignType.sign, abs_of_pos]

theorem hasDerivAt_suzukiOriginRemainderDerivative_of_neg {t : ℝ} (ht : t < 0) :
    HasDerivAt suzukiOriginRemainderDerivative (suzukiOriginRemainderCurvature t) t := by
  have hpos : 0 < -t := neg_pos.mpr ht
  have hcomp := (hasDerivAt_suzukiOriginRemainderFirstJet hpos).comp t
    (hasDerivAt_neg t)
  have hneg := hcomp.fun_neg
  have hcurv : suzukiOriginRemainderCurvature (-t) = suzukiOriginRemainderCurvature t := by
    exact suzukiOriginRemainderCurvature_neg t
  have hneg' : HasDerivAt (fun s : ℝ => -suzukiOriginRemainderFirstJet (-s))
      (suzukiOriginRemainderCurvature t) t := by
    simpa only [Function.comp_apply, mul_neg, mul_one, neg_neg, hcurv] using hneg
  apply hneg'.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ht] with s hs
  have hsneg : s < 0 := hs
  have hnot : ¬ 0 < s := not_lt_of_ge hsneg.le
  simp [suzukiOriginRemainderDerivative, hsneg, hnot, SignType.sign, abs_of_neg]

theorem hasDerivAt_suzukiOriginRemainderDerivative (t : ℝ) :
    HasDerivAt suzukiOriginRemainderDerivative (suzukiOriginRemainderCurvature t) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · exact hasDerivAt_suzukiOriginRemainderDerivative_of_neg ht
  · simpa [ht] using hasDerivAt_suzukiOriginRemainderDerivative_zero
  · exact hasDerivAt_suzukiOriginRemainderDerivative_of_pos ht

theorem deriv_suzukiOriginRemainderDerivative :
    deriv suzukiOriginRemainderDerivative = suzukiOriginRemainderCurvature := by
  funext t
  exact (hasDerivAt_suzukiOriginRemainderDerivative t).deriv

theorem contDiff_one_suzukiOriginRemainderDerivative :
    ContDiff ℝ 1 suzukiOriginRemainderDerivative := by
  rw [contDiff_one_iff_deriv, deriv_suzukiOriginRemainderDerivative]
  exact ⟨fun t => (hasDerivAt_suzukiOriginRemainderDerivative t).differentiableAt,
    continuous_suzukiOriginRemainderCurvature⟩

/-- Suzuki's literal equation-(2.2) remainder is globally twice continuously differentiable. -/
theorem contDiff_two_suzukiOriginRemainder :
    ContDiff ℝ 2 suzukiOriginRemainder := by
  change ContDiff ℝ (1 + 1) suzukiOriginRemainder
  rw [contDiff_succ_iff_deriv, deriv_suzukiOriginRemainder]
  exact ⟨fun t => (hasDerivAt_suzukiOriginRemainder t).differentiableAt,
    by norm_num, contDiff_one_suzukiOriginRemainderDerivative⟩

theorem tendsto_suzukiOriginRemainderPos_div_sq :
    Tendsto (fun t : ℝ => suzukiOriginRemainderPos t / t ^ 2)
      (𝓝[>] 0) (𝓝 (-7 / 8 : ℝ)) := by
  have hderivDen : ∀ᶠ t : ℝ in 𝓝[>] 0,
      HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    filter_upwards [] with t
    simpa using hasDerivAt_pow 2 t
  have hdenNe : ∀ᶠ t : ℝ in 𝓝[>] 0, (2 * t : ℝ) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_ne_zero (by norm_num) ht.ne'
  have hdenZero : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => t ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using (continuousAt_pow (0 : ℝ) 2).tendsto
    exact h.mono_left nhdsWithin_le_nhds
  have hquot : Tendsto
      (fun t : ℝ => suzukiOriginRemainderFirstJet t / (2 * t))
      (𝓝[>] 0) (𝓝 (-7 / 8 : ℝ)) := by
    have h := tendsto_suzukiOriginRemainderFirstJet_div_id.const_mul (1 / 2 : ℝ)
    convert h using 1
    · ext t
      by_cases ht : t = 0
      · simp [ht]
      · field_simp
    · ring
  exact HasDerivAt.lhopital_zero_nhdsGT
    (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hasDerivAt_suzukiOriginRemainderPos_source ht)
    hderivDen hdenNe tendsto_suzukiOriginRemainderPos_nhdsGT_zero hdenZero hquot

/-- Sharp two-sided origin asymptotic for Suzuki's literal remainder. -/
theorem tendsto_suzukiOriginRemainder_div_sq :
    Tendsto (fun t : ℝ => suzukiOriginRemainder t / t ^ 2)
      (𝓝[≠] 0) (𝓝 (-7 / 8 : ℝ)) := by
  have h := tendsto_suzukiOriginRemainderPos_div_sq.comp tendsto_abs_nhdsNE_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  unfold suzukiOriginRemainder
  change suzukiOriginRemainderPos |t| / |t| ^ 2 =
    suzukiOriginRemainderPos |t| / t ^ 2
  rw [sq_abs]

/-- Suzuki 2026, equation (2.2): the literal remainder satisfies `r(t) = O(t²)` at zero. -/
theorem suzukiOriginRemainder_isBigO_sq :
    suzukiOriginRemainder =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
  let q : ℝ → ℝ := fun t => suzukiOriginRemainder t / t ^ 2
  have hqPunct : q =O[𝓝[≠] 0] (fun _ : ℝ => (1 : ℝ)) := by
    simpa [q] using tendsto_suzukiOriginRemainder_div_sq.isBigO_one ℝ
  have hq : q =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    (isBigO_one_nhds_ne_iff ℝ (f := q)).mp hqPunct
  have hmul := hq.mul (isBigO_refl (fun t : ℝ => t ^ 2) (𝓝 0))
  apply hmul.congr'
  · filter_upwards [] with t
    dsimp [q]
    by_cases ht : t = 0
    · simp [ht]
    · field_simp
  · filter_upwards [] with t
    simp

end GaloisForLFunctions.RHTower
