import GaloisForLFunctions.RHTower.ReflectedBiHeatFiniteCommensurateChebyshevClassification
import GaloisForLFunctions.RHTower.CCM.CCMGrowingApertureMellin

/-!
# Reflected bi-heat arbitrary two-rate receiver cone

For every ordered pair of positive real rates `0 < lambda < mu`, the quotient
`sinh(mu*t)/sinh(lambda*t)` maps `(0,∞)` strictly increasingly onto
`(mu/lambda,∞)`. This yields the complete signed coefficient cone for which
`a*sinh(lambda*t)+b*sinh(mu*t)` has only its forced wall zero.

The same theorem is transported to physical real-power RBH apertures. In particular,
the irrational packet at rates `(1,sqrt 2)` and weights `(-sqrt 2,1)` is an exact
RH-equivalent receiver.

`[NEW] [INCOMMENSURATE RECEIVER] [EXACT CONE] [LEAN-PROVED]`
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- The logarithmic derivative scale of `sinh` is strictly increasing. -/
theorem self_mul_cosh_div_sinh_strictMonoOn :
    StrictMonoOn (fun x : ℝ => x * Real.cosh x / Real.sinh x) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    exact ne_of_gt (Real.sinh_pos_iff.mpr hx)
  · intro x hx
    rw [interior_Ioi] at hx
    have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
    have hd : HasDerivAt (fun y : ℝ => y * Real.cosh y / Real.sinh y)
        (((1 * Real.cosh x + x * Real.sinh x) * Real.sinh x -
          (x * Real.cosh x) * Real.cosh x) / Real.sinh x ^ 2) x :=
      ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).div
        (Real.hasDerivAt_sinh x) hs.ne'
    rw [hd.deriv]
    apply div_pos
    · have hprod : x < Real.sinh x * Real.cosh x := by
        calc
          x < Real.sinh x := self_lt_sinh hx
          _ = Real.sinh x * 1 := by ring
          _ ≤ Real.sinh x * Real.cosh x :=
            mul_le_mul_of_nonneg_left (Real.one_le_cosh x) hs.le
      have hid := Real.cosh_sq_sub_sinh_sq x
      have heq :
          (1 * Real.cosh x + x * Real.sinh x) * Real.sinh x -
              x * Real.cosh x * Real.cosh x =
            Real.sinh x * Real.cosh x - x := by
        calc
          _ = Real.sinh x * Real.cosh x -
              x * (Real.cosh x ^ 2 - Real.sinh x ^ 2) := by ring
          _ = Real.sinh x * Real.cosh x - x := by rw [hid]; ring
      rw [heq]
      exact sub_pos.mpr hprod
    · positivity

/-- For `0 < lambda < mu`, the unequal-rate hyperbolic quotient is strictly increasing. -/
theorem sinh_rate_ratio_strictMonoOn {lambda mu : ℝ}
    (hlambda : 0 < lambda) (hlamu : lambda < mu) :
    StrictMonoOn
      (fun t : ℝ => Real.sinh (mu * t) / Real.sinh (lambda * t))
      (Ioi 0) := by
  have hmu : 0 < mu := hlambda.trans hlamu
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact ne_of_gt (Real.sinh_pos_iff.mpr (mul_pos hlambda ht))
  · intro t ht
    rw [interior_Ioi] at ht
    have hlt : 0 < lambda * t := mul_pos hlambda ht
    have hmt : 0 < mu * t := mul_pos hmu ht
    have hsl : 0 < Real.sinh (lambda * t) := Real.sinh_pos_iff.mpr hlt
    have hsm : 0 < Real.sinh (mu * t) := Real.sinh_pos_iff.mpr hmt
    have hh := self_mul_cosh_div_sinh_strictMonoOn
      (show lambda * t ∈ Ioi 0 from hlt)
      (show mu * t ∈ Ioi 0 from hmt)
      (mul_lt_mul_of_pos_right hlamu ht)
    have hq :
        lambda * Real.cosh (lambda * t) / Real.sinh (lambda * t) <
          mu * Real.cosh (mu * t) / Real.sinh (mu * t) := by
      have heql :
          lambda * t * Real.cosh (lambda * t) / Real.sinh (lambda * t) =
            t * (lambda * Real.cosh (lambda * t) /
              Real.sinh (lambda * t)) := by ring
      have heqm :
          mu * t * Real.cosh (mu * t) / Real.sinh (mu * t) =
            t * (mu * Real.cosh (mu * t) / Real.sinh (mu * t)) := by ring
      dsimp only at hh
      rw [heql, heqm] at hh
      have ht0 : 0 < t := ht
      nlinarith
    have hcross :
        lambda * Real.cosh (lambda * t) * Real.sinh (mu * t) <
          mu * Real.cosh (mu * t) * Real.sinh (lambda * t) :=
      (div_lt_div_iff₀ hsl hsm).mp hq
    have hd : HasDerivAt
        (fun y : ℝ => Real.sinh (mu * y) / Real.sinh (lambda * y))
        ((mu * Real.cosh (mu * t) * Real.sinh (lambda * t) -
          Real.sinh (mu * t) * (lambda * Real.cosh (lambda * t))) /
            Real.sinh (lambda * t) ^ 2) t := by
      have hdmu : HasDerivAt (fun y : ℝ => mu * y) mu t := by
        simpa using (hasDerivAt_id t).const_mul mu
      have hdlambda : HasDerivAt (fun y : ℝ => lambda * y) lambda t := by
        simpa using (hasDerivAt_id t).const_mul lambda
      have hraw := hdmu.sinh.div hdlambda.sinh hsl.ne'
      apply hraw.congr_deriv
      ring
    rw [hd.deriv]
    apply div_pos
    · nlinarith
    · positivity

/-- Every positive unequal-rate quotient lies strictly above its wall derivative ratio. -/
theorem mu_div_lambda_lt_sinh_rate_ratio {lambda mu t : ℝ}
    (hlambda : 0 < lambda) (hlamu : lambda < mu) (ht : 0 < t) :
    mu / lambda < Real.sinh (mu * t) / Real.sinh (lambda * t) := by
  have hmu : 0 < mu := hlambda.trans hlamu
  have hlt : 0 < lambda * t := mul_pos hlambda ht
  have hmt : 0 < mu * t := mul_pos hmu ht
  have hmono := GaloisForLFunctions.RHTower.sinh_div_self_strictMonoOn
    (show lambda * t ∈ Ioi 0 from hlt)
    (show mu * t ∈ Ioi 0 from hmt)
    (mul_lt_mul_of_pos_right hlamu ht)
  have hcross :
      Real.sinh (lambda * t) * (mu * t) <
        Real.sinh (mu * t) * (lambda * t) :=
    (div_lt_div_iff₀ hlt hmt).mp hmono
  have hsl : 0 < Real.sinh (lambda * t) := Real.sinh_pos_iff.mpr hlt
  apply (div_lt_div_iff₀ hlambda hsl).mpr
  nlinarith

/-- The unequal-rate quotient tends to the derivative ratio at the wall. -/
theorem tendsto_sinh_rate_ratio_nhdsNE_zero {lambda mu : ℝ}
    (hlambda : lambda ≠ 0) (hmu : mu ≠ 0) :
    Tendsto (fun t : ℝ => Real.sinh (mu * t) / Real.sinh (lambda * t))
      (𝓝[≠] 0) (𝓝 (mu / lambda)) := by
  have hscale (c : ℝ) (hc : c ≠ 0) :
      Tendsto (fun t : ℝ => c * t) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hbase : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds.mul hbase)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [mem_compl_iff, mem_singleton_iff] at ht ⊢
      exact mul_ne_zero hc ht
  have hmuDiv : Tendsto (fun t : ℝ => Real.sinh (mu * t) / (mu * t))
      (𝓝[≠] 0) (𝓝 1) :=
    RHTower.tendsto_sinh_div.comp (hscale mu hmu)
  have hlambdaDiv :
      Tendsto (fun t : ℝ => Real.sinh (lambda * t) / (lambda * t))
        (𝓝[≠] 0) (𝓝 1) :=
    RHTower.tendsto_sinh_div.comp (hscale lambda hlambda)
  have hconst : Tendsto (fun _ : ℝ => mu / lambda)
      (𝓝[≠] 0) (𝓝 (mu / lambda)) := tendsto_const_nhds
  have hlim : Tendsto
      (fun t : ℝ =>
        ((mu / lambda) * (Real.sinh (mu * t) / (mu * t))) /
          (Real.sinh (lambda * t) / (lambda * t)))
      (𝓝[≠] 0) (𝓝 (((mu / lambda) * 1) / 1)) :=
    (hconst.mul hmuDiv).div hlambdaDiv (by norm_num : (1 : ℝ) ≠ 0)
  simpa using hlim.congr' (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [mem_compl_iff, mem_singleton_iff] at ht
    field_simp)

/-- The unequal-rate quotient is unbounded at positive infinity. -/
theorem tendsto_sinh_rate_ratio_atTop {lambda mu : ℝ}
    (hlambda : 0 < lambda) (hlamu : lambda < mu) :
    Tendsto (fun t : ℝ => Real.sinh (mu * t) / Real.sinh (lambda * t))
      atTop atTop := by
  have hmu : 0 < mu := hlambda.trans hlamu
  have hdiff : 0 < mu - lambda := sub_pos.mpr hlamu
  have hlin : Tendsto (fun t : ℝ => (mu - lambda) * t) atTop atTop := by
    exact tendsto_id.const_mul_atTop hdiff
  have hexp : Tendsto (fun t : ℝ => Real.exp ((mu - lambda) * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlin
  have hexpHalf : Tendsto (fun t : ℝ => Real.exp ((mu - lambda) * t) / 2)
      atTop atTop := hexp.atTop_div_const (by norm_num)
  refine Filter.tendsto_atTop_mono' atTop ?_ hexpHalf
  filter_upwards [eventually_ge_atTop (max 0 (Real.log 2 / mu))] with t ht
  have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
  have hmut : Real.log 2 ≤ mu * t := by
    have := (le_max_right (0 : ℝ) (Real.log 2 / mu)).trans ht
    rw [div_le_iff₀ hmu] at this
    nlinarith
  have hexp_mu_ge_two : (2 : ℝ) ≤ Real.exp (mu * t) := by
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := by rw [Real.exp_log (by norm_num)]
      _ ≤ Real.exp (mu * t) := Real.exp_le_exp.mpr hmut
  have heminus : Real.exp (-(mu * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hsnum : Real.exp (mu * t) / 4 ≤ Real.sinh (mu * t) := by
    rw [Real.sinh_eq]
    nlinarith
  have hsden : Real.sinh (lambda * t) ≤ Real.exp (lambda * t) / 2 := by
    rw [Real.sinh_eq]
    have := Real.exp_pos (-(lambda * t))
    linarith
  have hsl : 0 < Real.sinh (lambda * t) :=
    Real.sinh_pos_iff.mpr (mul_pos hlambda (lt_of_lt_of_le
      (show 0 < Real.log 2 / mu by positivity) ((le_max_right 0 _).trans ht)))
  rw [le_div_iff₀ hsl]
  calc
    Real.exp ((mu - lambda) * t) / 2 * Real.sinh (lambda * t) ≤
        Real.exp ((mu - lambda) * t) / 2 *
          (Real.exp (lambda * t) / 2) :=
      mul_le_mul_of_nonneg_left hsden (by positivity)
    _ = Real.exp (mu * t) / 4 := by
      calc
        _ = (Real.exp ((mu - lambda) * t) * Real.exp (lambda * t)) / 4 := by ring
        _ = Real.exp ((mu - lambda) * t + lambda * t) / 4 := by
          rw [Real.exp_add]
        _ = Real.exp (mu * t) / 4 := by congr 2; ring
    _ ≤ Real.sinh (mu * t) := hsnum

/-- Exact positive range of the unequal-rate hyperbolic quotient. -/
theorem exists_pos_sinh_rate_ratio_eq_iff {lambda mu r : ℝ}
    (hlambda : 0 < lambda) (hlamu : lambda < mu) :
    (∃ t : ℝ, 0 < t ∧
        Real.sinh (mu * t) / Real.sinh (lambda * t) = r) ↔
      mu / lambda < r := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact mu_div_lambda_lt_sinh_rate_ratio hlambda hlamu ht
  · intro hr
    have hmu : 0 < mu := hlambda.trans hlamu
    let f : ℝ → ℝ := fun t =>
      Real.sinh (mu * t) / Real.sinh (lambda * t)
    have hzeroNE : Tendsto f (𝓝[≠] 0) (𝓝 (mu / lambda)) :=
      tendsto_sinh_rate_ratio_nhdsNE_zero hlambda.ne' hmu.ne'
    have hsubset : Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ := by
      intro t ht
      simpa only [mem_compl_iff, mem_singleton_iff] using ht.ne'
    have hzero : Tendsto f (𝓝[>] 0) (𝓝 (mu / lambda)) :=
      hzeroNE.mono_left (nhdsWithin_mono 0 hsubset)
    have hevLow : ∀ᶠ t in 𝓝[>] 0, f t < r :=
      (tendsto_order.mp hzero).2 r hr
    have hevPos : ∀ᶠ t in 𝓝[>] 0, t ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
    obtain ⟨t0, ht0, hlow⟩ : ∃ t0 : ℝ, 0 < t0 ∧ f t0 < r := by
      have hev : ∀ᶠ t in 𝓝[>] 0, t ∈ Ioi (0 : ℝ) ∧ f t < r :=
        hevPos.and hevLow
      rcases hev.exists with ⟨t, ht, hlt⟩
      exact ⟨t, ht, hlt⟩
    have htop : Tendsto f atTop atTop :=
      tendsto_sinh_rate_ratio_atTop hlambda hlamu
    have hevHigh : ∀ᶠ t in atTop, r ≤ f t := (tendsto_atTop.mp htop) r
    obtain ⟨t1, ht01, hhigh⟩ : ∃ t1 : ℝ, t0 ≤ t1 ∧ r ≤ f t1 := by
      have hev : ∀ᶠ t in atTop, t0 ≤ t ∧ r ≤ f t :=
        (eventually_ge_atTop t0).and hevHigh
      exact hev.exists
    have hcont : ContinuousOn f (Icc t0 t1) := by
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro t ht
      have htpos : 0 < t := lt_of_lt_of_le ht0 ht.1
      exact ne_of_gt (Real.sinh_pos_iff.mpr (mul_pos hlambda htpos))
    have hrmem : r ∈ Icc (f t0) (f t1) := ⟨hlow.le, hhigh⟩
    rcases intermediate_value_Icc ht01 hcont hrmem with ⟨t, ht, hft⟩
    exact ⟨t, lt_of_lt_of_le ht0 ht.1, hft⟩

/-- Signed RBH reporter at two arbitrary positive rates. -/
def reflectedBiHeatArbitraryTwoRateReporter
    (lambda mu a b t : ℝ) : ℝ :=
  a * Real.sinh (lambda * t) + b * Real.sinh (mu * t)

theorem reflectedBiHeatArbitraryTwoRateReporter_neg
    (lambda mu a b t : ℝ) :
    reflectedBiHeatArbitraryTwoRateReporter lambda mu a b (-t) =
      -reflectedBiHeatArbitraryTwoRateReporter lambda mu a b t := by
  simp only [reflectedBiHeatArbitraryTwoRateReporter]
  rw [show lambda * -t = -(lambda * t) by ring,
    show mu * -t = -(mu * t) by ring, Real.sinh_neg, Real.sinh_neg]
  ring

/-- Exact coefficient cone for two arbitrary ordered positive rates. -/
def ReflectedBiHeatArbitraryTwoRateWallSelective
    (lambda mu a b : ℝ) : Prop :=
  (b = 0 ∧ a ≠ 0) ∨
    (b ≠ 0 ∧ 0 ≤ b * (lambda * a + mu * b))

/-- Complete coefficient classification for arbitrary, possibly incommensurate rates. -/
theorem reflectedBiHeatArbitraryTwoRateWallSelective_iff
    {lambda mu : ℝ} (hlambda : 0 < lambda) (hlamu : lambda < mu)
    (a b : ℝ) :
    ReflectedBiHeatArbitraryTwoRateWallSelective lambda mu a b ↔
      ∀ t : ℝ,
        reflectedBiHeatArbitraryTwoRateReporter lambda mu a b t = 0 ↔
          t = 0 := by
  have hmu : 0 < mu := hlambda.trans hlamu
  constructor
  · intro hcone t
    constructor
    · intro hzero
      rcases hcone with ⟨hb, ha⟩ | ⟨hb, hnonneg⟩
      · rw [hb] at hzero
        simp only [reflectedBiHeatArbitraryTwoRateReporter,
          zero_mul, add_zero] at hzero
        have hsinh : Real.sinh (lambda * t) = 0 :=
          (mul_eq_zero.mp hzero).resolve_left ha
        exact (mul_eq_zero.mp (Real.sinh_eq_zero.mp hsinh)).resolve_left
          hlambda.ne'
      · by_contra ht
        have hroot_pos (u : ℝ) (hu : 0 < u)
            (hroot : reflectedBiHeatArbitraryTwoRateReporter
              lambda mu a b u = 0) : False := by
          have hlt : 0 < lambda * u := mul_pos hlambda hu
          have hsl : 0 < Real.sinh (lambda * u) :=
            Real.sinh_pos_iff.mpr hlt
          let R := Real.sinh (mu * u) / Real.sinh (lambda * u)
          have hrel : a + b * R = 0 := by
            dsimp [R]
            rw [show a + b * (Real.sinh (mu * u) / Real.sinh (lambda * u)) =
                (a * Real.sinh (lambda * u) +
                  b * Real.sinh (mu * u)) / Real.sinh (lambda * u) by
              field_simp]
            rw [show a * Real.sinh (lambda * u) + b * Real.sinh (mu * u) = 0 by
              simpa [reflectedBiHeatArbitraryTwoRateReporter] using hroot]
            simp
          have hR : mu / lambda < R :=
            mu_div_lambda_lt_sinh_rate_ratio hlambda hlamu hu
          have hRcross : mu < R * lambda :=
            (div_lt_iff₀ hlambda).mp hR
          have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
          have hneg : b * (lambda * a + mu * b) < 0 := by
            have ha : a = -b * R := by linarith
            have hfac : mu - lambda * R < 0 := by nlinarith
            rw [ha]
            have heq :
                b * (lambda * (-b * R) + mu * b) =
                  b ^ 2 * (mu - lambda * R) := by ring
            rw [heq]
            exact mul_neg_of_pos_of_neg hb2 hfac
          exact (not_lt_of_ge hnonneg) hneg
        rcases lt_or_gt_of_ne ht with htneg | htpos
        · have hnegzero : reflectedBiHeatArbitraryTwoRateReporter
              lambda mu a b (-t) = 0 := by
            rw [reflectedBiHeatArbitraryTwoRateReporter_neg, hzero, neg_zero]
          exact hroot_pos (-t) (neg_pos.mpr htneg) hnegzero
        · exact hroot_pos t htpos hzero
    · rintro rfl
      simp [reflectedBiHeatArbitraryTwoRateReporter]
  · intro hselect
    by_cases hb : b = 0
    · left
      refine ⟨hb, ?_⟩
      intro ha
      have hzero : reflectedBiHeatArbitraryTwoRateReporter
          lambda mu a b 1 = 0 := by
        simp [reflectedBiHeatArbitraryTwoRateReporter, ha, hb]
      have : (1 : ℝ) = 0 := (hselect 1).mp hzero
      norm_num at this
    · right
      refine ⟨hb, ?_⟩
      by_contra hnot
      have hneg : b * (lambda * a + mu * b) < 0 := lt_of_not_ge hnot
      have htarget : mu / lambda < -a / b := by
        rcases lt_or_gt_of_ne hb with hbneg | hbpos
        · rw [show -a / b = a / (-b) by ring]
          apply (div_lt_div_iff₀ hlambda (neg_pos.mpr hbneg)).mpr
          have hsecond : 0 < lambda * a + mu * b := by
            nlinarith
          nlinarith
        · apply (div_lt_div_iff₀ hlambda hbpos).mpr
          have hsecond : lambda * a + mu * b < 0 := by
            nlinarith
          nlinarith
      rcases (exists_pos_sinh_rate_ratio_eq_iff hlambda hlamu).mpr htarget with
        ⟨t, ht, hratio⟩
      have hsl : Real.sinh (lambda * t) ≠ 0 :=
        (Real.sinh_pos_iff.mpr (mul_pos hlambda ht)).ne'
      have hzero : reflectedBiHeatArbitraryTwoRateReporter
          lambda mu a b t = 0 := by
        rw [reflectedBiHeatArbitraryTwoRateReporter]
        have hratio' : Real.sinh (mu * t) =
            (-a / b) * Real.sinh (lambda * t) := by
          rw [← hratio]
          field_simp
        rw [hratio']
        field_simp
        ring
      exact ht.ne' ((hselect t).mp hzero)

/-- Canonically weighted real-power aperture gap at an arbitrary rate. -/
theorem reflectedBiHeatWeightedRealPowerApertureGap_eq_sinh
    (rate : ℝ) {x : ℝ} (hx : 0 < x) (rho : XiDivisorSupport) :
    x ^ (rate / 2) *
        (reflectedBiHeatLeftLeadingJetNorm rho (x ^ rate) ^ 2 -
          reflectedBiHeatRightLeadingJetNorm rho (x ^ rate) ^ 2) =
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
        Real.sinh (rate *
          (Real.log x * ((rho : ℂ).re - 1 / 2))) := by
  have hxr : 0 < x ^ rate := Real.rpow_pos_of_pos hx rate
  rw [reflectedBiHeatLeftLeadingJetNorm_eq rho hxr,
    reflectedBiHeatRightLeadingJetNorm_eq rho hxr]
  simp only [reflectedBiHeatLeftScaleOrder, reflectedBiHeatRightScaleOrder]
  rw [Real.rpow_def_of_pos hx,
    Real.rpow_def_of_pos hxr, Real.rpow_def_of_pos hxr,
    Real.log_rpow hx, Real.sinh_eq]
  let r : ℝ := (rho : ℂ).re
  let L : ℝ := Real.log x
  have h1 : Real.exp (L * (rate / 2)) *
      Real.exp ((rate * L) * ((r - 1) / 2)) ^ 2 =
      Real.exp (rate * (L * (r - 1 / 2))) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
    ring
  have h2 : Real.exp (L * (rate / 2)) *
      Real.exp ((rate * L) * (-r / 2)) ^ 2 =
      Real.exp (-(rate * (L * (r - 1 / 2)))) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
    ring
  change
    Real.exp (L * (rate / 2)) *
        ((‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ *
            Real.exp ((rate * L) * ((r - 1) / 2))) ^ 2 -
          (‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ *
            Real.exp ((rate * L) * (-r / 2))) ^ 2) =
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
        ((Real.exp (rate * (L * (r - 1 / 2))) -
          Real.exp (-(rate * (L * (r - 1 / 2))))) / 2)
  simp only [mul_pow]
  linear_combination
    ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 * h1 -
    ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 * h2

/-- Physical signed diagonal gap at arbitrary real-power apertures. -/
def reflectedBiHeatArbitraryTwoRateApertureGap
    (lambda mu a b x : ℝ) (rho : XiDivisorSupport) : ℝ :=
  a * x ^ (lambda / 2) *
      (reflectedBiHeatLeftLeadingJetNorm rho (x ^ lambda) ^ 2 -
        reflectedBiHeatRightLeadingJetNorm rho (x ^ lambda) ^ 2) +
    b * x ^ (mu / 2) *
      (reflectedBiHeatLeftLeadingJetNorm rho (x ^ mu) ^ 2 -
        reflectedBiHeatRightLeadingJetNorm rho (x ^ mu) ^ 2)

/-- Exact arbitrary-real-rate physical factorization. -/
theorem reflectedBiHeatArbitraryTwoRateApertureGap_eq_reporter
    (lambda mu a b : ℝ) {x : ℝ} (hx : 0 < x)
    (rho : XiDivisorSupport) :
    reflectedBiHeatArbitraryTwoRateApertureGap lambda mu a b x rho =
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
        reflectedBiHeatArbitraryTwoRateReporter lambda mu a b
          (Real.log x * ((rho : ℂ).re - 1 / 2)) := by
  have hl := reflectedBiHeatWeightedRealPowerApertureGap_eq_sinh
    lambda hx rho
  have hm := reflectedBiHeatWeightedRealPowerApertureGap_eq_sinh
    mu hx rho
  rw [reflectedBiHeatArbitraryTwoRateApertureGap,
    reflectedBiHeatArbitraryTwoRateReporter]
  calc
    _ = a * (x ^ (lambda / 2) *
          (reflectedBiHeatLeftLeadingJetNorm rho (x ^ lambda) ^ 2 -
            reflectedBiHeatRightLeadingJetNorm rho (x ^ lambda) ^ 2)) +
        b * (x ^ (mu / 2) *
          (reflectedBiHeatLeftLeadingJetNorm rho (x ^ mu) ^ 2 -
            reflectedBiHeatRightLeadingJetNorm rho (x ^ mu) ^ 2)) := by ring
    _ = _ := by rw [hl, hm]; ring

/-- Under the exact cone, arbitrary-rate physical balance occurs only on the wall. -/
theorem reflectedBiHeatArbitraryTwoRateApertureGap_eq_zero_iff
    {lambda mu : ℝ} (hlambda : 0 < lambda) (hlamu : lambda < mu)
    {a b : ℝ}
    (hcone : ReflectedBiHeatArbitraryTwoRateWallSelective lambda mu a b)
    {x : ℝ} (hx : 1 < x) (rho : XiDivisorSupport) :
    reflectedBiHeatArbitraryTwoRateApertureGap lambda mu a b x rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [reflectedBiHeatArbitraryTwoRateApertureGap_eq_reporter
    lambda mu a b (lt_trans zero_lt_one hx) rho]
  have hcoef :
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr
        (reflectedBiHeatMultiplicityLeadingCoefficient_ne_zero rho)))
  constructor
  · intro hzero
    have hreport : reflectedBiHeatArbitraryTwoRateReporter lambda mu a b
        (Real.log x * ((rho : ℂ).re - 1 / 2)) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hcoef
    have hu :=
      ((reflectedBiHeatArbitraryTwoRateWallSelective_iff hlambda hlamu a b).mp
        hcone (Real.log x * ((rho : ℂ).re - 1 / 2))).mp hreport
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hsub : (rho : ℂ).re - 1 / 2 = 0 :=
      (mul_eq_zero.mp hu).resolve_left hlog.ne'
    exact sub_eq_zero.mp hsub
  · intro hre
    rw [hre, sub_self, mul_zero]
    simp [reflectedBiHeatArbitraryTwoRateReporter]

/-- Every arbitrary-rate pair in the exact cone supplies an RH-equivalent receiver. -/
theorem riemannHypothesis_iff_reflectedBiHeatArbitraryTwoRateApertureGap_eq_zero
    {lambda mu : ℝ} (hlambda : 0 < lambda) (hlamu : lambda < mu)
    {a b : ℝ}
    (hcone : ReflectedBiHeatArbitraryTwoRateWallSelective lambda mu a b)
    {x : ℝ} (hx : 1 < x) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        reflectedBiHeatArbitraryTwoRateApertureGap lambda mu a b x rho = 0 := by
  constructor
  · intro hRH rho
    exact (reflectedBiHeatArbitraryTwoRateApertureGap_eq_zero_iff
      hlambda hlamu hcone hx rho).mpr
        (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (reflectedBiHeatArbitraryTwoRateApertureGap_eq_zero_iff
        hlambda hlamu hcone hx rho).mp (h rho)

/-- Boundary-cone witness at the irrational rate pair `(1, sqrt 2)`. -/
theorem reflectedBiHeatArbitraryTwoRateWallSelective_neg_sqrtTwo_one :
    ReflectedBiHeatArbitraryTwoRateWallSelective
      1 (Real.sqrt 2) (-Real.sqrt 2) 1 := by
  right
  constructor
  · norm_num
  · norm_num [ReflectedBiHeatArbitraryTwoRateWallSelective]

/-- A genuinely incommensurate exact RH receiver at apertures `x` and `x^(sqrt 2)`. -/
theorem riemannHypothesis_iff_reflectedBiHeatIrrationalTwoRateApertureGap_eq_zero
    {x : ℝ} (hx : 1 < x) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        reflectedBiHeatArbitraryTwoRateApertureGap
          1 (Real.sqrt 2) (-Real.sqrt 2) 1 x rho = 0 := by
  have hsqrt : (1 : ℝ) < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by norm_num)
  exact riemannHypothesis_iff_reflectedBiHeatArbitraryTwoRateApertureGap_eq_zero
    (by norm_num) hsqrt
      reflectedBiHeatArbitraryTwoRateWallSelective_neg_sqrtTwo_one hx

end

end RHTower
