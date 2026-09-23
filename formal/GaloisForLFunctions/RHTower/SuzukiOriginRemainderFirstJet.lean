import GaloisForLFunctions.RHTower.SuzukiOriginLogarithmicRemainder
import GaloisForLFunctions.RHTower.DigammaQuarter
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

open Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.RHTower

def suzukiLerchTailOneClosed (t : ℝ) : ℝ :=
  -Real.arctan (Real.exp (-(t / 2))) -
    (1 / 2 : ℝ) * Real.log
      ((1 + Real.exp (-(t / 2))) / (1 - Real.exp (-(t / 2))))

theorem hasDerivAt_suzukiLerchTailOneClosed {t : ℝ} (ht : 0 < t) :
    HasDerivAt suzukiLerchTailOneClosed (screwLerchTail₂ t) t := by
  let y : ℝ := Real.exp (-(t / 2))
  have hypos : 0 < y := Real.exp_pos _
  have hylt : y < 1 := by
    dsimp [y]
    rw [Real.exp_lt_one_iff]
    linarith
  have hy1p : 1 + y ≠ 0 := by positivity
  have hy1m : 1 - y ≠ 0 := sub_ne_zero.mpr hylt.ne'
  have hy' : HasDerivAt (fun x : ℝ => Real.exp (-(x / 2))) (-y / 2) t := by
    have hinner : HasDerivAt (fun x : ℝ => -(x / 2)) (-1 / 2) t := by
      convert (hasDerivAt_id' t).div_const 2 |>.fun_neg using 1
      all_goals first | rfl | ring
    convert hinner.exp using 1
    all_goals dsimp [y]
    ring
  have hatan := ((Real.hasDerivAt_arctan y).comp t hy').fun_neg
  have hplus := (hasDerivAt_const t 1).add hy'
  have hminus := (hasDerivAt_const t 1).sub hy'
  have hquot := hplus.div hminus hy1m
  have hquotne : (1 + y) / (1 - y) ≠ 0 := div_ne_zero hy1p hy1m
  have hlog := hquot.log hquotne
  have hraw := hatan.sub (hlog.const_mul (1 / 2 : ℝ))
  have hraw' := hraw.congr_of_eventuallyEq
    (show suzukiLerchTailOneClosed =ᶠ[𝓝 t] _ from by
      filter_upwards [] with x
      simp [suzukiLerchTailOneClosed, Function.comp_apply, Pi.sub_apply])
  apply hraw'.congr_deriv
  rw [screwLerchTail₂_eq ht]
  dsimp [y] at *
  have hpow : y ^ (4 : ℕ) = Real.exp (-(2 * t)) := by
    dsimp [y]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hyden : 1 - y ^ (4 : ℕ) ≠ 0 := by
    rw [hpow]
    exact (one_sub_exp_neg_two_mul_pos ht).ne'
  rw [← hpow]
  field_simp [hy1p, hy1m, hyden]
  ring

theorem tendsto_screwLerchTail₂_atTop :
    Tendsto screwLerchTail₂ atTop (𝓝 0) := by
  have hhalf : Tendsto (fun t : ℝ => Real.exp (-(t / 2))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply tendsto_neg_atTop_atBot.comp
    exact (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id
  have htwo : Tendsto (fun t : ℝ => Real.exp (-(2 * t))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply tendsto_neg_atTop_atBot.comp
    exact (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id
  have hden : Tendsto (fun t : ℝ => 1 - Real.exp (-(2 * t))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub htwo
  have hquot : Tendsto
      (fun t : ℝ => Real.exp (-(t / 2)) / (1 - Real.exp (-(2 * t))))
      atTop (𝓝 0) := by
    have h := hhalf.div hden (by norm_num : (1 : ℝ) ≠ 0)
    convert h using 1
    · ext t
      rfl
    · norm_num
  apply hquot.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (screwLerchTail₂_eq ht).symm

theorem abs_screwLerchTail₁_le {t : ℝ} (ht : 0 < t) :
    |screwLerchTail₁ t| ≤ 2 * screwLerchTail₂ t := by
  rw [show |screwLerchTail₁ t| = ‖screwLerchTail₁ t‖ by rw [Real.norm_eq_abs]]
  calc
    ‖screwLerchTail₁ t‖
        ≤ ∑' k : ℕ, ‖-(Real.exp (-(lerchExp k * t)) / lerchExp k)‖ := by
          exact norm_tsum_le_tsum_norm (summable_screwLerchTerm₁ ht).norm
    _ = ∑' k : ℕ, Real.exp (-(lerchExp k * t)) / lerchExp k := by
          congr 1
          funext k
          rw [norm_neg, Real.norm_eq_abs,
            abs_of_nonneg (div_nonneg (Real.exp_nonneg _) (lerchExp_pos k).le)]
    _ ≤ ∑' k : ℕ, 2 * Real.exp (-(lerchExp k * t)) := by
          have hpos : Summable fun k : ℕ =>
              Real.exp (-(lerchExp k * t)) / lerchExp k := by
            simpa only [neg_neg] using (summable_screwLerchTerm₁ ht).neg
          exact hpos.tsum_le_tsum (fun _ => div_lerchExp_le)
            ((summable_exp_neg_lerchExp ht).mul_left 2)
    _ = 2 * screwLerchTail₂ t := by
          rw [screwLerchTail₂, tsum_mul_left]

theorem tendsto_screwLerchTail₁_atTop :
    Tendsto screwLerchTail₁ atTop (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simpa [Real.norm_eq_abs] using abs_screwLerchTail₁_le ht
  · simpa using tendsto_screwLerchTail₂_atTop.const_mul 2

theorem tendsto_suzukiLerchTailOneClosed_atTop : Tendsto suzukiLerchTailOneClosed atTop (𝓝 0) := by
  have hy : Tendsto (fun t : ℝ => Real.exp (-(t / 2))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply tendsto_neg_atTop_atBot.comp
    exact (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id
  have hplus : Tendsto (fun t : ℝ => 1 + Real.exp (-(t / 2))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hy
  have hminus : Tendsto (fun t : ℝ => 1 - Real.exp (-(t / 2))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hy
  have hquot : Tendsto
      (fun t : ℝ => (1 + Real.exp (-(t / 2))) / (1 - Real.exp (-(t / 2))))
      atTop (𝓝 1) := by
    have h := hplus.div hminus (by norm_num : (1 : ℝ) ≠ 0)
    convert h using 1
    · ext t
      rfl
    · norm_num
  unfold suzukiLerchTailOneClosed
  have hatan : Tendsto (fun t : ℝ => Real.arctan (Real.exp (-(t / 2))))
      atTop (𝓝 0) := by
    have h := Real.continuousAt_arctan.tendsto.comp hy
    convert h using 1
    · ext t
      rfl
    · norm_num
  have hlog : Tendsto
      (fun t : ℝ => Real.log
        ((1 + Real.exp (-(t / 2))) / (1 - Real.exp (-(t / 2)))))
      atTop (𝓝 0) := by
    simpa using hquot.log (by norm_num : (1 : ℝ) ≠ 0)
  simpa using hatan.neg.sub (hlog.const_mul (1 / 2 : ℝ))

theorem screwLerchTail₁_eq_suzukiLerchTailOneClosed {t : ℝ} (ht : 0 < t) :
    screwLerchTail₁ t = suzukiLerchTailOneClosed t := by
  have hd : ∀ x ∈ Ioi (0 : ℝ),
      deriv screwLerchTail₁ x = deriv suzukiLerchTailOneClosed x := by
    intro x hx
    rw [(hasDerivAt_screwLerchTail₁ hx).deriv, (hasDerivAt_suzukiLerchTailOneClosed hx).deriv]
  have hdiff : DifferentiableOn ℝ (fun x => screwLerchTail₁ x - suzukiLerchTailOneClosed x) (Ioi 0) := by
    intro x hx
    exact (hasDerivAt_screwLerchTail₁ hx).differentiableAt.sub
      (hasDerivAt_suzukiLerchTailOneClosed hx).differentiableAt |>.differentiableWithinAt
  have hzero : (Ioi (0 : ℝ)).EqOn
      (deriv (fun x => screwLerchTail₁ x - suzukiLerchTailOneClosed x)) (fun _ => 0) := by
    intro x hx
    have h := ((hasDerivAt_screwLerchTail₁ hx).sub
      (hasDerivAt_suzukiLerchTailOneClosed hx)).deriv
    rw [show (screwLerchTail₁ - suzukiLerchTailOneClosed) =
      (fun x => screwLerchTail₁ x - suzukiLerchTailOneClosed x) by rfl] at h
    simpa only [hd x hx, sub_self] using h
  obtain ⟨c, hc⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero
    isPreconnected_Ioi hdiff hzero
  have hconst : ∀ x : ℝ, 0 < x → screwLerchTail₁ x - suzukiLerchTailOneClosed x = c := by
    intro x hx
    exact hc x hx
  have hlim : Tendsto (fun x => screwLerchTail₁ x - suzukiLerchTailOneClosed x) atTop (𝓝 0) :=
    by simpa using tendsto_screwLerchTail₁_atTop.sub tendsto_suzukiLerchTailOneClosed_atTop
  have hc0 : c = 0 := by
    have hconstlim : Tendsto (fun _ : ℝ => c) atTop (𝓝 0) := by
      apply hlim.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact hconst x hx
    exact tendsto_nhds_unique tendsto_const_nhds hconstlim
  linarith [hconst t ht]

theorem tendsto_suzukiLerchTailOneClosed_sub_half_log :
    Tendsto (fun t : ℝ => suzukiLerchTailOneClosed t - (1 / 2 : ℝ) * Real.log t)
      (𝓝[>] 0) (𝓝 (-Real.pi / 4 - Real.log 2)) := by
  let y : ℝ → ℝ := fun t => Real.exp (-(t / 2))
  have hy : Tendsto y (𝓝[>] 0) (𝓝 1) := by
    have hcont : Continuous y := by
      dsimp [y]
      fun_prop
    have h0 : Tendsto y (𝓝 (0 : ℝ)) (𝓝 (y 0)) := hcont.continuousAt
    have h1 : Tendsto y (𝓝 (0 : ℝ)) (𝓝 1) := by simpa [y] using h0
    exact tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi 0) h1
  have hatan : Tendsto (fun t => -Real.arctan (y t))
      (𝓝[>] 0) (𝓝 (-Real.pi / 4)) := by
    convert (Real.continuousAt_arctan.tendsto.comp hy).neg using 1
    · ext t
      rfl
    · rw [Real.arctan_one]
      ring
  have hslope : Tendsto (fun t : ℝ => (1 - y t) / t)
      (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
    have hinner : HasDerivAt (fun t : ℝ => -(t / 2)) (-1 / 2) 0 := by
      convert (hasDerivAt_id' (0 : ℝ)).div_const 2 |>.fun_neg using 1
      all_goals first | rfl | ring
    have hexp : HasDerivAt y (-1 / 2) 0 := by
      dsimp [y]
      convert hinner.exp using 1
      all_goals norm_num
    have hone : HasDerivAt (fun t : ℝ => 1 - y t) (1 / 2) 0 := by
      convert (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub hexp using 1
      all_goals first | rfl | ring
    have h := hone.tendsto_slope_zero_right
    convert h using 1
    · ext t
      simp [slope, y, div_eq_inv_mul]
  have hrecip : Tendsto (fun t : ℝ => t / (1 - y t))
      (𝓝[>] 0) (𝓝 2) := by
    have h := hslope.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)
    convert h using 1
    · ext t
      by_cases ht0 : t = 0
      · simp [ht0]
      · by_cases hden : 1 - y t = 0
        · simp [hden]
        · field_simp
    · norm_num
  have hplus : Tendsto (fun t => 1 + y t) (𝓝[>] 0) (𝓝 2) := by
    convert (tendsto_const_nhds (x := (1 : ℝ))).add hy using 1
    norm_num
  have hratio : Tendsto (fun t : ℝ => t * (1 + y t) / (1 - y t))
      (𝓝[>] 0) (𝓝 4) := by
    have h := hrecip.mul hplus
    convert h using 1
    · ext t
      ring
    · norm_num
  have hlog : Tendsto
      (fun t : ℝ => -(1 / 2 : ℝ) * Real.log (t * (1 + y t) / (1 - y t)))
      (𝓝[>] 0) (𝓝 (-Real.log 2)) := by
    have h := (hratio.log (by norm_num : (4 : ℝ) ≠ 0)).const_mul (-(1 / 2 : ℝ))
    convert h using 1
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    ring
  apply (hatan.add hlog).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  have ht0 : t ≠ 0 := ht.ne'
  have hplus0 : 1 + y t ≠ 0 := by
    dsimp [y]
    positivity
  have hminus0 : 1 - y t ≠ 0 := by
    dsimp [y]
    have h := (one_sub_exp_neg_two_mul_pos (by linarith [htpos] : 0 < t / 4)).ne'
    convert h using 1 <;> ring
  unfold suzukiLerchTailOneClosed
  dsimp [y]
  rw [Real.log_div hplus0 hminus0, Real.log_div
    (mul_ne_zero ht0 hplus0) hminus0, Real.log_mul ht0 hplus0]
  ring

def suzukiOriginRemainderFirstJet (t : ℝ) : ℝ :=
  -2 * Real.exp (t / 2) + 2 * Real.exp (-(t / 2)) - screwLinearCoeff / 2 +
    screwLerchTail₁ t - (1 / 2 : ℝ) * (Real.log t + 1) - suzukiOriginLinearCoeff

theorem digamma_two_re : (Complex.digamma 2).re = 1 - Real.eulerMascheroniConstant := by
  have h := Complex.digamma_apply_add_one (1 : ℂ) (by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  rw [show (1 : ℂ) + 1 = 2 by norm_num, Complex.digamma_one] at h
  have hre := congrArg Complex.re h
  norm_num at hre ⊢
  linarith

theorem tendsto_suzukiOriginRemainderFirstJet : Tendsto suzukiOriginRemainderFirstJet (𝓝[>] 0) (𝓝 0) := by
  have hexp : Tendsto
      (fun t : ℝ => -2 * Real.exp (t / 2) + 2 * Real.exp (-(t / 2)))
      (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous
        (fun t : ℝ => -2 * Real.exp (t / 2) + 2 * Real.exp (-(t / 2))) := by fun_prop
    have h : Tendsto
        (fun t : ℝ => -2 * Real.exp (t / 2) + 2 * Real.exp (-(t / 2)))
        (𝓝 (0 : ℝ))
        (𝓝 ((fun t : ℝ => -2 * Real.exp (t / 2) + 2 * Real.exp (-(t / 2))) 0)) :=
      hcont.continuousAt
    have h0 : Tendsto
        (fun t : ℝ => -2 * Real.exp (t / 2) + 2 * Real.exp (-(t / 2)))
        (𝓝 (0 : ℝ)) (𝓝 0) := by simpa using h
    exact tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi 0) h0
  have htail : Tendsto
      (fun t : ℝ => screwLerchTail₁ t - (1 / 2 : ℝ) * Real.log t)
      (𝓝[>] 0) (𝓝 (-Real.pi / 4 - Real.log 2)) := by
    apply tendsto_suzukiLerchTailOneClosed_sub_half_log.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [screwLerchTail₁_eq_suzukiLerchTailOneClosed ht]
  have hsum := hexp.add htail
  have hconst :
      (-Real.pi / 4 - Real.log 2) - screwLinearCoeff / 2 - 1 / 2 -
          suzukiOriginLinearCoeff = 0 := by
    rw [screwLinearCoeff, suzukiOriginLinearCoeff,
      GaloisForLFunctions.RHTower.digamma_quarter, digamma_two_re]
    norm_num [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
    have hlog2 : (Complex.log 2).re = Real.log 2 := by
      rw [Complex.log_re]
      norm_num
    rw [hlog2]
    ring
  unfold suzukiOriginRemainderFirstJet
  have h := (((hsum.sub_const (screwLinearCoeff / 2)).sub_const (1 / 2 : ℝ)).sub_const
    suzukiOriginLinearCoeff)
  convert h using 1
  · ext t
    ring
  · rw [show 0 + (-Real.pi / 4 - Real.log 2) - screwLinearCoeff / 2 - 1 / 2 -
        suzukiOriginLinearCoeff = 0 by linarith [hconst]]


end GaloisForLFunctions.RHTower

