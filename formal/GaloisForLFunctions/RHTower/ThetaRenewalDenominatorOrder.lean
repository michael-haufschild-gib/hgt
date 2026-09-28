import GaloisForLFunctions.RHTower.ThetaRenewalExitDensity

/-!
# The renewal denominator is entire of order one and infinite type

Let `ν(t) = 2π Σ n² e^{5t/4 - πn²e^t}`, `N(z) = ∫₀^∞ e^{-zt} ν(t) dt` and `D(z) = c - N(z)`,
`c = Θ(1)`.

* On the real axis `N` is positive and strictly decreasing, with `N'(x) = -∫ t e^{-xt} ν(t) dt`,
  `N(x) → 0` as `x → +∞` and `N(x) → ∞` as `x → -∞`; since `N(-1/4) = cq < c/6`, the equation
  `N(x) = c` has exactly one real solution, and it lies left of `-1/4`.
* `‖N(z)‖ ≤ N(Re z)`, and `σt - e^t ≤ σ log σ` gives
  `N(-R) ≤ K I₀ exp((R + 5/4) log(R + 5/4))`; hence
  `‖D(z)‖ ≤ exp(C(1 + ‖z‖) log(2 + ‖z‖))`.
* Keeping only the first theta summand on `log R ≤ t ≤ log R + 1/R` gives
  `N(-R) ≥ (2π/R) exp((R + 5/4) log R - π(R + 2))`.  Together:
  `log max_{|z| ≤ R} ‖D‖ = R log R + O(R)`, so `D` has order exactly one and infinite type.
-/

open Complex Filter Topology Set MeasureTheory HurwitzZeta

namespace RHTower

noncomputable section

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## Analyticity and the real axis -/

theorem differentiable_thetaRenewalDenominator : Differentiable ℂ thetaRenewalDenominator := by
  have h : thetaRenewalDenominator = fun s => 1 + (s - 1 / 4) * wardMellin (2 * I * s) :=
    funext thetaRenewalDenominator_eq
  rw [h]
  exact (differentiable_const _).add ((differentiable_id.sub_const _).mul
    (differentiable_wardMellin.comp (differentiable_id.const_mul _)))

theorem thetaRenewalLaplace_eq_sub (s : ℂ) :
    thetaRenewalLaplace s = ((Θ 1 : ℝ) : ℂ) - thetaRenewalDenominator s := by
  rw [thetaRenewalDenominator]; ring

theorem differentiable_thetaRenewalLaplace : Differentiable ℂ thetaRenewalLaplace := by
  have h : thetaRenewalLaplace = fun s => ((Θ 1 : ℝ) : ℂ) - thetaRenewalDenominator s :=
    funext thetaRenewalLaplace_eq_sub
  rw [h]
  exact (differentiable_const _).sub differentiable_thetaRenewalDenominator

/-- `N(x) = ∫₀^∞ e^{-xt} ν(t) dt` on the real axis. -/
def thetaRenewalLaplaceReal (x : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-(x * t)) * thetaRenewalIncrement t

theorem thetaRenewalLaplace_ofReal (x : ℝ) :
    thetaRenewalLaplace x = (thetaRenewalLaplaceReal x : ℂ) := by
  rw [thetaRenewalLaplace, thetaRenewalLaplaceReal, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  push_cast; ring_nf

theorem thetaRenewalLaplaceReal_pos (x : ℝ) : 0 < thetaRenewalLaplaceReal x := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ), 0 < Real.exp (-(x * t)) * thetaRenewalIncrement t :=
    fun t _ => mul_pos (Real.exp_pos _) (thetaRenewalIncrement_pos t)
  rw [thetaRenewalLaplaceReal, setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => (hpt t ht).le))
    (integrableOn_exp_mul_thetaRenewalIncrement x),
    show Function.support (fun t => Real.exp (-(x * t)) * thetaRenewalIncrement t) ∩ Ioi 0 =
      Ioi 0 from inter_eq_right.mpr fun t ht => (hpt t ht).ne']
  simp

/-- `‖N(z)‖ ≤ N(Re z)`. -/
theorem norm_thetaRenewalLaplace_le_real (z : ℂ) :
    ‖thetaRenewalLaplace z‖ ≤ thetaRenewalLaplaceReal z.re := by
  rw [thetaRenewalLaplace, thetaRenewalLaplaceReal]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaRenewalIncrement_pos t)]
  simp

theorem setIntegral_Ioi_lt_of_lt {f g : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    (hg : IntegrableOn g (Ioi 0)) (hlt : ∀ t, 0 < t → f t < g t) :
    ∫ t in Ioi (0 : ℝ), f t < ∫ t in Ioi (0 : ℝ), g t := by
  rw [← sub_pos, ← integral_sub hg hf]
  have hpt : ∀ t ∈ Ioi (0 : ℝ), 0 < g t - f t := fun t ht => sub_pos.mpr (hlt t ht)
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => (hpt t ht).le))
    (hg.sub hf), show Function.support (fun t => g t - f t) ∩ Ioi 0 = Ioi 0 from
      inter_eq_right.mpr fun t ht => (hpt t ht).ne']
  simp

/-- `N` is strictly decreasing on the real axis. -/
theorem strictAnti_thetaRenewalLaplaceReal : StrictAnti thetaRenewalLaplaceReal := by
  intro x y hxy
  refine setIntegral_Ioi_lt_of_lt (integrableOn_exp_mul_thetaRenewalIncrement y)
    (integrableOn_exp_mul_thetaRenewalIncrement x) fun t ht => ?_
  refine mul_lt_mul_of_pos_right (Real.exp_lt_exp.mpr ?_) (thetaRenewalIncrement_pos t)
  nlinarith

theorem continuous_thetaRenewalLaplaceReal : Continuous thetaRenewalLaplaceReal := by
  have h := continuous_re.comp (differentiable_thetaRenewalLaplace.continuous.comp continuous_ofReal)
  refine h.congr fun x => ?_
  simp [Function.comp, thetaRenewalLaplace_ofReal]

/-- `ν(t) ≥ 2π e^{5t/4 - π e^t}`: the first theta summand. -/
theorem thetaRenewalIncrement_ge (t : ℝ) :
    2 * Real.pi * Real.exp (5 / 4 * t - Real.pi * Real.exp t) ≤ thetaRenewalIncrement t := by
  rw [thetaRenewalIncrement]
  have h := (summable_thetaMoment_terms 1 (Real.exp_pos t)).le_tsum 0 (fun n _ => by positivity)
  simp only [CharP.cast_eq_zero, zero_add, one_pow, one_mul, mul_one] at h
  rw [show 5 / 4 * t - Real.pi * Real.exp t = 5 / 4 * t + -(Real.pi * Real.exp t) by ring,
    Real.exp_add, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem exp_le_one_add_two_mul_of_le_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 1 + 2 * x := by
  have h := Real.exp_bound' h0 h1 (n := 1) one_pos
  simp at h
  linarith

/-- **(5c).** `N(-R) ≥ (2π/R) exp((R + 5/4) log R - π(R + 2))` for `R ≥ 1`. -/
theorem thetaRenewalLaplaceReal_neg_ge {R : ℝ} (hR : 1 ≤ R) :
    2 * Real.pi / R * Real.exp ((R + 5 / 4) * Real.log R - Real.pi * (R + 2)) ≤
      thetaRenewalLaplaceReal (-R) := by
  have hR0 : 0 < R := by linarith
  set a := Real.log R with ha
  set b := Real.log R + 1 / R with hb
  have hab : a ≤ b := by have := one_div_pos.mpr hR0; linarith
  have ha0 : 0 ≤ a := Real.log_nonneg hR
  set m := 2 * Real.pi * Real.exp ((R + 5 / 4) * Real.log R - Real.pi * (R + 2)) with hm
  have hint := integrableOn_exp_mul_thetaRenewalIncrement (-R)
  have hlow : ∀ t ∈ Ioc a b, m ≤ Real.exp (-(-R * t)) * thetaRenewalIncrement t := by
    intro t ht
    obtain ⟨hat, htb⟩ := ht
    have het : Real.exp t ≤ R + 2 := by
      calc Real.exp t ≤ Real.exp b := Real.exp_le_exp.mpr htb
        _ = R * Real.exp (1 / R) := by rw [hb, Real.exp_add, Real.exp_log hR0]
        _ ≤ R * (1 + 2 * (1 / R)) := by
            gcongr; exact exp_le_one_add_two_mul_of_le_one (by positivity) (by
              rw [div_le_one hR0]; exact hR)
        _ = R + 2 := by field_simp
    have hν := thetaRenewalIncrement_ge t
    calc m = 2 * Real.pi * Real.exp (R * a + (5 / 4 * a - Real.pi * (R + 2))) := by
          rw [hm, ha]; ring_nf
      _ ≤ 2 * Real.pi * Real.exp (R * t + (5 / 4 * t - Real.pi * Real.exp t)) := by
          have := hat.le
          gcongr
      _ = Real.exp (-(-R * t)) * (2 * Real.pi * Real.exp (5 / 4 * t - Real.pi * Real.exp t)) := by
          rw [Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(-R * t)) * thetaRenewalIncrement t :=
          mul_le_mul_of_nonneg_left hν (Real.exp_pos _).le
  have hsub : ∫ t in Ioc a b, Real.exp (-(-R * t)) * thetaRenewalIncrement t ≤
      thetaRenewalLaplaceReal (-R) :=
    setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t _ => (mul_pos (Real.exp_pos _)
        (thetaRenewalIncrement_pos t)).le))
      (Eventually.of_forall fun t ht => lt_of_le_of_lt ha0 ht.1)
  have hconst : ∫ t in Ioc a b, m = m * (1 / R) := by
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),
      smul_eq_mul, hb, ha]; ring
  have hmono : ∫ t in Ioc a b, m ≤ ∫ t in Ioc a b, Real.exp (-(-R * t)) * thetaRenewalIncrement t :=
    setIntegral_mono_on (integrableOn_const (by simp)) (hint.mono_set fun t ht =>
      lt_of_le_of_lt ha0 ht.1) measurableSet_Ioc hlow
  rw [hconst] at hmono
  calc 2 * Real.pi / R * Real.exp ((R + 5 / 4) * Real.log R - Real.pi * (R + 2)) = m * (1 / R) := by
        rw [hm]; ring
    _ ≤ _ := hmono.trans hsub

theorem self_le_thetaRenewalLaplaceReal_neg {R : ℝ} (hR : Real.exp 5 ≤ R) :
    R ≤ thetaRenewalLaplaceReal (-R) := by
  have h6 : 6 ≤ R := le_trans (by linarith [Real.add_one_le_exp (5 : ℝ)]) hR
  have hR0 : 0 < R := by linarith
  have hlog : 5 ≤ Real.log R := (Real.le_log_iff_exp_le hR0).mpr hR
  have hlow := thetaRenewalLaplaceReal_neg_ge (by linarith : 1 ≤ R)
  have hE : 2 * Real.log R ≤ (R + 5 / 4) * Real.log R - Real.pi * (R + 2) := by
    nlinarith [Real.pi_lt_d2]
  have hexp : R ^ 2 ≤ Real.exp ((R + 5 / 4) * Real.log R - Real.pi * (R + 2)) := by
    calc R ^ 2 = Real.exp (2 * Real.log R) := by
          rw [show 2 * Real.log R = Real.log R + Real.log R by ring, Real.exp_add,
            Real.exp_log hR0]; ring
      _ ≤ _ := Real.exp_le_exp.mpr hE
  calc R ≤ 2 * Real.pi / R * R ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hR0]; nlinarith [Real.pi_gt_three]
    _ ≤ _ := le_trans (mul_le_mul_of_nonneg_left hexp (by positivity)) hlow

/-- `N(x) → ∞` as `x → -∞`. -/
theorem tendsto_thetaRenewalLaplaceReal_atBot :
    Tendsto thetaRenewalLaplaceReal atBot atTop := by
  refine tendsto_atTop_mono' atBot ?_ tendsto_neg_atBot_atTop
  filter_upwards [eventually_le_atBot (-Real.exp 5)] with x hx
  have := self_le_thetaRenewalLaplaceReal_neg (R := -x) (by linarith)
  simpa using this

/-- `N(-1/4) = c q < c/6`. -/
theorem thetaRenewalLaplaceReal_neg_quarter :
    thetaRenewalLaplaceReal (-(1 / 4)) = Θ 1 * thetaRenewalMass := by
  rw [thetaRenewalLaplaceReal, thetaRenewalMass, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [thetaRenewalDensity]
  have hc := thetaSeam_pos
  field_simp

theorem thetaRenewalLaplaceReal_neg_quarter_lt : thetaRenewalLaplaceReal (-(1 / 4)) < Θ 1 := by
  rw [thetaRenewalLaplaceReal_neg_quarter]
  have hc := thetaSeam_pos
  nlinarith [thetaRenewalMass_lt]

theorem thetaRenewalDenominator_ofReal (x : ℝ) :
    thetaRenewalDenominator x = ((Θ 1 - thetaRenewalLaplaceReal x : ℝ) : ℂ) := by
  rw [thetaRenewalDenominator, thetaRenewalLaplace_ofReal]; push_cast; ring

/-- **The unique real renewal root.** `D` has exactly one real zero `x_*`, and `x_* < -1/4`. -/
theorem existsUnique_real_thetaRenewalDenominator_eq_zero :
    ∃! x : ℝ, thetaRenewalDenominator x = 0 ∧ x < -(1 / 4) := by
  have hc := thetaSeam_pos
  obtain ⟨R, hR⟩ : ∃ R : ℝ, Real.exp 5 ≤ R ∧ Θ 1 ≤ R ∧ 1 / 4 < R :=
    ⟨Real.exp 5 + Θ 1 + 1, by linarith, by linarith [Real.exp_pos 5], by
      nlinarith [Real.exp_pos 5]⟩
  have hNR : Θ 1 ≤ thetaRenewalLaplaceReal (-R) :=
    hR.2.1.trans (self_le_thetaRenewalLaplaceReal_neg hR.1)
  have hiff : ∀ x : ℝ, thetaRenewalDenominator x = 0 ↔ thetaRenewalLaplaceReal x = Θ 1 := by
    intro x
    rw [thetaRenewalDenominator_ofReal, Complex.ofReal_eq_zero, sub_eq_zero, eq_comm]
  obtain ⟨x, hx, hNx⟩ := intermediate_value_Icc' (by linarith : -R ≤ -(1 / 4))
    continuous_thetaRenewalLaplaceReal.continuousOn
    ⟨thetaRenewalLaplaceReal_neg_quarter_lt.le, hNR⟩
  have hxlt : x < -(1 / 4) := by
    rcases lt_or_eq_of_le hx.2 with h | h
    · exact h
    · have := thetaRenewalLaplaceReal_neg_quarter_lt
      rw [← h, hNx] at this
      exact absurd this (lt_irrefl _)
  refine ⟨x, ⟨(hiff x).mpr hNx, hxlt⟩, fun y hy => ?_⟩
  exact strictAnti_thetaRenewalLaplaceReal.injective (((hiff y).mp hy.1).trans hNx.symm)

/-- `D` has no real zero other than `x_*`: every real zero lies left of `-1/4`. -/
theorem lt_of_thetaRenewalDenominator_ofReal_eq_zero {x : ℝ}
    (hx : thetaRenewalDenominator x = 0) : x < -(1 / 4) := by
  by_contra h
  rw [not_lt] at h
  exact thetaRenewalDenominator_ne_zero (by simpa using h) hx

/-! ## Growth: order one, infinite type -/

/-- `σ t - e^t ≤ σ log σ` for `σ > 0`. -/
theorem mul_sub_exp_le_self_mul_log {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    σ * t - Real.exp t ≤ σ * Real.log σ := by
  have h := Real.log_le_sub_one_of_pos (show 0 < Real.exp t / σ by positivity)
  rw [Real.log_div (Real.exp_pos t).ne' hσ.ne', Real.log_exp] at h
  have h2 : σ * (t - Real.log σ) ≤ σ * (Real.exp t / σ - 1) := mul_le_mul_of_nonneg_left h hσ.le
  rw [mul_sub, mul_sub, mul_div_cancel₀ _ hσ.ne'] at h2
  linarith

/-- The Gaussian-rate tail constant `∫₀^∞ e^{-(π-1)(1+t)} dt`. -/
def thetaRenewalTailConst : ℝ := ∫ t in Ioi (0 : ℝ), Real.exp (-(Real.pi - 1) * (1 + t))

theorem integrableOn_thetaRenewalTail :
    IntegrableOn (fun t : ℝ => Real.exp (-(Real.pi - 1) * (1 + t))) (Ioi 0) := by
  have h := (integrableOn_exp_mul_Ioi (a := -(Real.pi - 1)) (by linarith [Real.pi_gt_three])
    0).const_mul (Real.exp (-(Real.pi - 1)))
  refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
  rw [← Real.exp_add]; ring_nf

/-- `N(-R) ≤ K I₀ e^{σ log σ}` with `σ = R + 5/4`. -/
theorem thetaRenewalLaplaceReal_neg_le {R : ℝ} (hR : 0 ≤ R) :
    thetaRenewalLaplaceReal (-R) ≤ 2 * Real.pi * thetaMoment 1 1 * Real.exp Real.pi *
      thetaRenewalTailConst * Real.exp ((R + 5 / 4) * Real.log (R + 5 / 4)) := by
  set σ := R + 5 / 4 with hσ
  have hσ0 : 0 < σ := by linarith
  set K := 2 * Real.pi * thetaMoment 1 1 * Real.exp Real.pi
  have hK : 0 ≤ K := by
    have := thetaMoment_pos 1 (show (0 : ℝ) < 1 by norm_num); positivity
  rw [thetaRenewalLaplaceReal, thetaRenewalTailConst, mul_assoc K, ← integral_mul_const,
    ← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_exp_mul_thetaRenewalIncrement (-R))
    ((integrableOn_thetaRenewalTail.mul_const _).const_mul _) measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 ≤ t := le_of_lt ht
  have h1 := thetaRenewalIncrement_le ht0
  have h2 := mul_sub_exp_le_self_mul_log hσ0 t
  have h3 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hexp : Real.exp (-(-R * t)) * Real.exp (5 / 4 * t - Real.pi * Real.exp t) ≤
      Real.exp (σ * Real.log σ) * Real.exp (-(Real.pi - 1) * (1 + t)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hpi : 0 ≤ Real.pi - 1 := by linarith [Real.pi_gt_three]
    nlinarith
  calc Real.exp (-(-R * t)) * thetaRenewalIncrement t
      ≤ Real.exp (-(-R * t)) * (K * Real.exp (5 / 4 * t - Real.pi * Real.exp t)) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = K * (Real.exp (-(-R * t)) * Real.exp (5 / 4 * t - Real.pi * Real.exp t)) := by ring
    _ ≤ K * (Real.exp (σ * Real.log σ) * Real.exp (-(Real.pi - 1) * (1 + t))) :=
        mul_le_mul_of_nonneg_left hexp hK
    _ = _ := by ring

theorem thetaRenewalTailConst_nonneg : 0 ≤ thetaRenewalTailConst :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => (Real.exp_pos _).le

/-- The constant `c + K I₀` of the upper growth bound. -/
def thetaRenewalGrowthConst : ℝ :=
  Θ 1 + 2 * Real.pi * thetaMoment 1 1 * Real.exp Real.pi * thetaRenewalTailConst

theorem thetaRenewalGrowthConst_pos : 0 < thetaRenewalGrowthConst := by
  have hc := thetaSeam_pos
  have := thetaMoment_pos 1 (show (0 : ℝ) < 1 by norm_num)
  have := thetaRenewalTailConst_nonneg
  unfold thetaRenewalGrowthConst
  positivity

/-- `‖D(z)‖ ≤ (c + K I₀) e^{σ log σ}`, `σ = ‖z‖ + 5/4`. -/
theorem norm_thetaRenewalDenominator_le (z : ℂ) :
    ‖thetaRenewalDenominator z‖ ≤
      thetaRenewalGrowthConst * Real.exp ((‖z‖ + 5 / 4) * Real.log (‖z‖ + 5 / 4)) := by
  have hc := thetaSeam_pos
  have hN : ‖thetaRenewalLaplace z‖ ≤ 2 * Real.pi * thetaMoment 1 1 * Real.exp Real.pi *
      thetaRenewalTailConst * Real.exp ((‖z‖ + 5 / 4) * Real.log (‖z‖ + 5 / 4)) := by
    refine (norm_thetaRenewalLaplace_le_real z).trans ?_
    refine le_trans (strictAnti_thetaRenewalLaplaceReal.antitone ?_)
      (thetaRenewalLaplaceReal_neg_le (norm_nonneg z))
    have := Complex.abs_re_le_norm z
    linarith [neg_abs_le z.re]
  have hE : 1 ≤ Real.exp ((‖z‖ + 5 / 4) * Real.log (‖z‖ + 5 / 4)) := by
    have hz := norm_nonneg z
    exact Real.one_le_exp (mul_nonneg (by positivity) (Real.log_nonneg (by linarith)))
  calc ‖thetaRenewalDenominator z‖ ≤ ‖((Θ 1 : ℝ) : ℂ)‖ + ‖thetaRenewalLaplace z‖ := by
        rw [thetaRenewalDenominator]; exact norm_sub_le _ _
    _ ≤ Θ 1 * Real.exp ((‖z‖ + 5 / 4) * Real.log (‖z‖ + 5 / 4)) +
          2 * Real.pi * thetaMoment 1 1 * Real.exp Real.pi * thetaRenewalTailConst *
            Real.exp ((‖z‖ + 5 / 4) * Real.log (‖z‖ + 5 / 4)) := by
        rw [Complex.norm_real, Real.norm_of_nonneg hc.le]
        gcongr
        nlinarith
    _ = _ := by rw [thetaRenewalGrowthConst]; ring

/-- **(5), order-one envelope.** `‖D(z)‖ ≤ exp(C (1 + ‖z‖) log(2 + ‖z‖))`. -/
theorem exists_norm_thetaRenewalDenominator_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖thetaRenewalDenominator z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  set M := max 0 (Real.log thetaRenewalGrowthConst)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨5 / 4 + M / Real.log 2, by positivity, fun z => ?_⟩
  set r := ‖z‖
  have hr := norm_nonneg z
  have hL2 : Real.log 2 ≤ Real.log (2 + r) := Real.log_le_log two_pos (by linarith)
  have hLpos : 0 < Real.log (2 + r) := lt_of_lt_of_le hl2 hL2
  have hlogσ : Real.log (r + 5 / 4) ≤ Real.log (2 + r) := Real.log_le_log (by linarith)
    (by linarith)
  have hlogσ0 : 0 ≤ Real.log (r + 5 / 4) := Real.log_nonneg (by linarith)
  have h1 : (r + 5 / 4) * Real.log (r + 5 / 4) ≤ 5 / 4 * (1 + r) * Real.log (2 + r) := by
    have : r + 5 / 4 ≤ 5 / 4 * (1 + r) := by linarith
    calc (r + 5 / 4) * Real.log (r + 5 / 4) ≤ 5 / 4 * (1 + r) * Real.log (r + 5 / 4) :=
          mul_le_mul_of_nonneg_right this hlogσ0
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogσ (by positivity)
  have h2 : Real.log thetaRenewalGrowthConst ≤ M / Real.log 2 * (1 + r) * Real.log (2 + r) := by
    have hM : 0 ≤ M := le_max_left _ _
    have : M ≤ M / Real.log 2 * (1 + r) * Real.log (2 + r) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hl2]
      have : Real.log 2 ≤ (1 + r) * Real.log (2 + r) := by nlinarith
      nlinarith
    exact (le_max_right _ _).trans this
  calc ‖thetaRenewalDenominator z‖
      ≤ thetaRenewalGrowthConst * Real.exp ((r + 5 / 4) * Real.log (r + 5 / 4)) :=
        norm_thetaRenewalDenominator_le z
    _ = Real.exp (Real.log thetaRenewalGrowthConst + (r + 5 / 4) * Real.log (r + 5 / 4)) := by
        rw [Real.exp_add, Real.exp_log thetaRenewalGrowthConst_pos]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- **(5), finite order.** `‖D(z)‖ ≤ exp(C (1 + ‖z‖)²)`. -/
theorem exists_norm_thetaRenewalDenominator_le_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖thetaRenewalDenominator z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ 2) := by
  obtain ⟨C, hC, h⟩ := exists_norm_thetaRenewalDenominator_le
  refine ⟨C, hC, fun z => (h z).trans (Real.exp_le_exp.mpr ?_)⟩
  have hr := norm_nonneg z
  have hlog : Real.log (2 + ‖z‖) ≤ 1 + ‖z‖ := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 + ‖z‖ by linarith); linarith
  have : (1 + ‖z‖) * Real.log (2 + ‖z‖) ≤ (1 + ‖z‖) ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hlog (by linarith)
  nlinarith

theorem mul_log_le_mul_log_add {R : ℝ} (hR : 1 ≤ R) :
    (R + 5 / 4) * Real.log (R + 5 / 4) ≤ R * Real.log R + 3 * R := by
  have hR0 : 0 < R := by linarith
  have h1 : Real.log (R + 5 / 4) ≤ Real.log R + 5 / (4 * R) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (R + 5 / 4) / R by positivity)
    rw [Real.log_div (by linarith) hR0.ne'] at h
    have : (R + 5 / 4) / R - 1 = 5 / (4 * R) := by field_simp; ring
    linarith
  have h2 : Real.log R ≤ R - 1 := by have := Real.log_le_sub_one_of_pos hR0; linarith
  have h3 : 0 ≤ Real.log R := Real.log_nonneg hR
  have h4 : (R + 5 / 4) * (5 / (4 * R)) ≤ 5 / 4 + 25 / 16 := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc (R + 5 / 4) * Real.log (R + 5 / 4) ≤ (R + 5 / 4) * (Real.log R + 5 / (4 * R)) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = R * Real.log R + 5 / 4 * Real.log R + (R + 5 / 4) * (5 / (4 * R)) := by ring
    _ ≤ R * Real.log R + 3 * R := by nlinarith

theorem mul_log_monotone {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    x * Real.log x ≤ y * Real.log y :=
  mul_le_mul hxy (Real.log_le_log (by linarith) hxy) (Real.log_nonneg hx) (by linarith)

/-- **(5b).** `log M_D(R) = R log R + O(R)`: for large `R`, every `|z| ≤ R` has
`log ‖D(z)‖ ≤ R log R + C R`, and `log ‖D(-R)‖ ≥ R log R - C R`. -/
theorem thetaRenewalDenominator_log_growth :
    ∃ C R₀ : ℝ, 0 ≤ C ∧ 1 ≤ R₀ ∧ ∀ R, R₀ ≤ R →
      (∀ z : ℂ, ‖z‖ ≤ R → Real.log ‖thetaRenewalDenominator z‖ ≤ R * Real.log R + C * R) ∧
      R * Real.log R - C * R ≤ Real.log ‖thetaRenewalDenominator (-R : ℝ)‖ ∧
      thetaRenewalDenominator (-R : ℝ) ≠ 0 := by
  have hc := thetaSeam_pos
  have hG := thetaRenewalGrowthConst_pos
  set C := max (3 + |Real.log thetaRenewalGrowthConst|) (3 * Real.pi)
  refine ⟨C, max (Real.exp 5) (2 * Θ 1 + 1), le_trans (by positivity) (le_max_right _ _),
    le_trans (by linarith [Real.add_one_le_exp (5 : ℝ)]) (le_max_left _ _), fun R hR => ?_⟩
  have hR5 : Real.exp 5 ≤ R := le_trans (le_max_left _ _) hR
  have hR1 : 1 ≤ R := le_trans (by linarith [Real.add_one_le_exp (5 : ℝ)]) hR5
  have hR0 : 0 < R := by linarith
  have hRc : 2 * Θ 1 + 1 ≤ R := le_trans (le_max_right _ _) hR
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hNR := self_le_thetaRenewalLaplaceReal_neg hR5
  have hD : thetaRenewalDenominator (-R : ℝ) = ((Θ 1 - thetaRenewalLaplaceReal (-R) : ℝ) : ℂ) :=
    thetaRenewalDenominator_ofReal (-R)
  have hnorm : ‖thetaRenewalDenominator (-R : ℝ)‖ = thetaRenewalLaplaceReal (-R) - Θ 1 := by
    rw [hD, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]; ring
  refine ⟨fun z hz => ?_, ?_, ?_⟩
  · have hz0 := norm_nonneg z
    have hmono : (‖z‖ + 5 / 4) * Real.log (‖z‖ + 5 / 4) ≤ (R + 5 / 4) * Real.log (R + 5 / 4) :=
      mul_log_monotone (by linarith) (by linarith)
    have hb := mul_log_le_mul_log_add hR1
    have hCge : 3 + |Real.log thetaRenewalGrowthConst| ≤ C := le_max_left _ _
    have habs := le_abs_self (Real.log thetaRenewalGrowthConst)
    rcases eq_or_lt_of_le (norm_nonneg (thetaRenewalDenominator z)) with h0 | hpos
    · rw [← h0, Real.log_zero]
      nlinarith [abs_nonneg (Real.log thetaRenewalGrowthConst)]
    · have hle := norm_thetaRenewalDenominator_le z
      have hlog := Real.log_le_log hpos hle
      rw [Real.log_mul hG.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
      have hCR : |Real.log thetaRenewalGrowthConst| ≤ (C - 3) * R := by
        have h0 : 0 ≤ C - 3 - |Real.log thetaRenewalGrowthConst| := by linarith
        nlinarith [abs_nonneg (Real.log thetaRenewalGrowthConst)]
      nlinarith
  · have hlow := thetaRenewalLaplaceReal_neg_ge hR1
    have hhalf : Real.pi / R * Real.exp ((R + 5 / 4) * Real.log R - Real.pi * (R + 2)) ≤
        ‖thetaRenewalDenominator (-R : ℝ)‖ := by
      rw [hnorm]
      have : 2 * Real.pi / R * Real.exp ((R + 5 / 4) * Real.log R - Real.pi * (R + 2)) =
          2 * (Real.pi / R * Real.exp ((R + 5 / 4) * Real.log R - Real.pi * (R + 2))) := by ring
      linarith
    have hposl : 0 < Real.pi / R * Real.exp ((R + 5 / 4) * Real.log R - Real.pi * (R + 2)) := by
      positivity
    have hlog := Real.log_le_log hposl hhalf
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
      Real.log_div Real.pi_ne_zero hR0.ne'] at hlog
    have hlogpi : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
    have hlogR' : Real.log R ≤ R := by have := Real.log_le_sub_one_of_pos hR0; linarith
    have hC3 : 3 * Real.pi ≤ C := le_max_right _ _
    nlinarith [Real.pi_gt_three]
  · rw [hD, Complex.ofReal_ne_zero]; linarith

/-- **Order one.** For every `ε > 0`, `‖D(z)‖ ≤ exp(‖z‖^{1+ε})` for large `‖z‖`. -/
theorem thetaRenewalDenominator_order_le_one {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, ∀ z : ℂ, R₀ ≤ ‖z‖ →
      ‖thetaRenewalDenominator z‖ ≤ Real.exp (‖z‖ ^ (1 + ε)) := by
  obtain ⟨C, R₁, hC, hR₁, hgrowth⟩ := thetaRenewalDenominator_log_growth
  have hlo := (isLittleO_log_rpow_atTop hε).bound (show (0 : ℝ) < 1 / 2 by norm_num)
  have hpow : ∀ᶠ x : ℝ in atTop, 2 * C ≤ x ^ ε :=
    (tendsto_rpow_atTop hε).eventually_ge_atTop (2 * C)
  obtain ⟨R₂, hR₂⟩ := eventually_atTop.mp (hlo.and (hpow.and (eventually_ge_atTop R₁)))
  refine ⟨max R₂ 1, fun z hz => ?_⟩
  set r := ‖z‖
  obtain ⟨h1, h2, h3⟩ := hR₂ r (le_trans (le_max_left _ _) hz)
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hz
  have hr0 : 0 < r := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hr1),
    abs_of_nonneg (by positivity)] at h1
  have hup := (hgrowth r h3).1 z le_rfl
  rcases eq_or_lt_of_le (norm_nonneg (thetaRenewalDenominator z)) with h0 | hpos
  · rw [← h0]; exact (Real.exp_pos _).le
  · rw [← Real.exp_log hpos]
    refine Real.exp_le_exp.mpr (hup.trans ?_)
    rw [Real.rpow_add hr0, Real.rpow_one]
    nlinarith

/-- **Infinite exponential type.** No bound `‖D(z)‖ ≤ A e^{B‖z‖}` holds for large `‖z‖`: along the
negative real axis `‖D(-R)‖` eventually exceeds every `A e^{BR}`. -/
theorem thetaRenewalDenominator_infinite_type (A B R₀ : ℝ) :
    ∃ z : ℂ, R₀ ≤ ‖z‖ ∧ A * Real.exp (B * ‖z‖) < ‖thetaRenewalDenominator z‖ := by
  obtain ⟨C, R₁, hC, hR₁, hgrowth⟩ := thetaRenewalDenominator_log_growth
  set R := max (max R₀ R₁) (Real.exp (C + |B| + |Real.log (abs A)| + 1))
  have hR1 : R₁ ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  have hR0 : R₀ ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hRe : Real.exp (C + |B| + |Real.log (abs A)| + 1) ≤ R := le_max_right _ _
  have hRpos : 0 < R := lt_of_lt_of_le (Real.exp_pos _) hRe
  have hRge1 : 1 ≤ R := le_trans hR₁ hR1
  have hlog : C + |B| + |Real.log (abs A)| + 1 ≤ Real.log R := (Real.le_log_iff_exp_le hRpos).mpr hRe
  obtain ⟨-, hlow, hne⟩ := hgrowth R hR1
  refine ⟨(-R : ℝ), ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hRpos]; exact hR0
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hRpos]
    have hpos : 0 < ‖thetaRenewalDenominator (-R : ℝ)‖ := norm_pos_iff.mpr hne
    rcases le_or_gt A 0 with hA | hA
    · exact lt_of_le_of_lt (mul_nonpos_of_nonpos_of_nonneg hA (Real.exp_pos _).le) hpos
    · rw [← Real.exp_log hpos, ← Real.exp_log hA, ← Real.exp_add]
      refine Real.exp_lt_exp.mpr (lt_of_lt_of_le ?_ hlow)
      have h1 : Real.log A ≤ |Real.log (abs A)| := by rw [abs_of_pos hA]; exact le_abs_self _
      have h2 : B * R ≤ |B| * R := mul_le_mul_of_nonneg_right (le_abs_self B) hRpos.le
      have h3 : |Real.log (abs A)| ≤ |Real.log (abs A)| * R := le_mul_of_one_le_right (abs_nonneg _) hRge1
      nlinarith [abs_nonneg B, abs_nonneg (Real.log (abs A))]

/-- **Order exactly one.** For every `ρ < 1`, `‖D(z)‖ > exp(‖z‖^ρ)` at arbitrarily large `‖z‖`. -/
theorem thetaRenewalDenominator_order_ge_one {ρ : ℝ} (hρ : ρ < 1) (R₀ : ℝ) :
    ∃ z : ℂ, R₀ ≤ ‖z‖ ∧ Real.exp (‖z‖ ^ ρ) < ‖thetaRenewalDenominator z‖ := by
  obtain ⟨z, hz, hlt⟩ := thetaRenewalDenominator_infinite_type 1 1 (max R₀ 1)
  refine ⟨z, le_trans (le_max_left _ _) hz, lt_of_le_of_lt ?_ hlt⟩
  have h1 : 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz
  rw [one_mul, one_mul]
  refine Real.exp_le_exp.mpr ?_
  calc ‖z‖ ^ ρ ≤ ‖z‖ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hρ.le
    _ = ‖z‖ := Real.rpow_one _

/-! ## The derivative of `N` and the seam values -/

theorem integrableOn_mul_exp_mul_thetaRenewalIncrement (K : ℝ) :
    IntegrableOn (fun t : ℝ => t * Real.exp (K * t) * thetaRenewalIncrement t) (Ioi 0) := by
  obtain ⟨C, hC, hle⟩ := thetaRenewalIncrement_superexp (K + 1)
  refine ((integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).const_mul C).mono'
    (by have := continuous_thetaRenewalIncrement; fun_prop) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 < t := ht
  have hν := thetaRenewalIncrement_pos t
  have h1 := hle t ht0.le
  rw [abs_of_pos hν] at h1
  have h2 : t * Real.exp (-t) ≤ 1 := by
    have := Real.add_one_le_exp t
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos t)]; linarith
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), neg_one_mul]
  calc t * Real.exp (K * t) * thetaRenewalIncrement t
      = t * Real.exp (-t) * (Real.exp ((K + 1) * t) * thetaRenewalIncrement t) := by
        have he : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
        rw [show (K + 1) * t = K * t + t by ring, Real.exp_add]
        linear_combination (-(t * Real.exp (K * t) * thetaRenewalIncrement t)) * he
    _ ≤ 1 * (C * Real.exp (-t)) := mul_le_mul h2 h1 (by positivity) zero_le_one
    _ = C * Real.exp (-t) := one_mul _

/-- `N'(x) = -∫₀^∞ t e^{-xt} ν(t) dt`. -/
theorem hasDerivAt_thetaRenewalLaplaceReal (x : ℝ) :
    HasDerivAt thetaRenewalLaplaceReal
      (-∫ t in Ioi (0 : ℝ), t * Real.exp (-(x * t)) * thetaRenewalIncrement t) x := by
  have hνc := continuous_thetaRenewalIncrement
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun y (t : ℝ) => Real.exp (-(y * t)) * thetaRenewalIncrement t)
    (F' := fun y (t : ℝ) => -(t * Real.exp (-(y * t)) * thetaRenewalIncrement t))
    (bound := fun t => t * Real.exp ((-x + 1) * t) * thetaRenewalIncrement t) (x₀ := x)
    (Metric.ball_mem_nhds x one_pos)
    (Eventually.of_forall fun y => ((by fun_prop : Continuous fun t : ℝ =>
      Real.exp (-(y * t)) * thetaRenewalIncrement t)).aestronglyMeasurable.restrict)
    (integrableOn_exp_mul_thetaRenewalIncrement x)
    ((by fun_prop : Continuous fun t : ℝ =>
      -(t * Real.exp (-(x * t)) * thetaRenewalIncrement t)).aestronglyMeasurable.restrict)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht y hy => by
      have ht0 : (0 : ℝ) < t := ht
      have hy' : |y - x| < 1 := by rw [← Real.dist_eq]; exact Metric.mem_ball.mp hy
      have hν := (thetaRenewalIncrement_pos t).le
      rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by
        have := thetaRenewalIncrement_pos t; positivity)]
      gcongr
      rw [abs_lt] at hy'
      nlinarith))
    (integrableOn_mul_exp_mul_thetaRenewalIncrement (-x + 1))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ y _ => by
      have h := (((hasDerivAt_mul_const t (x := y)).neg).exp).mul_const (thetaRenewalIncrement t)
      simp only [Pi.neg_apply] at h
      refine h.congr_deriv ?_
      ring))
  have h := key.2
  rw [integral_neg] at h
  exact h

theorem integral_mul_thetaRenewalIncrement_pos :
    0 < ∫ t in Ioi (0 : ℝ), t * thetaRenewalIncrement t := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ), 0 < t * thetaRenewalIncrement t :=
    fun t ht => mul_pos ht (thetaRenewalIncrement_pos t)
  have hint : IntegrableOn (fun t : ℝ => t * thetaRenewalIncrement t) (Ioi 0) := by
    refine (integrableOn_mul_exp_mul_thetaRenewalIncrement 0).congr_fun (fun t _ => ?_)
      measurableSet_Ioi
    simp
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => (hpt t ht).le))
    hint, show Function.support (fun t : ℝ => t * thetaRenewalIncrement t) ∩ Ioi 0 = Ioi 0 from
      inter_eq_right.mpr fun t ht => (hpt t ht).ne']
  simp

/-- `D'(x) = ∫₀^∞ t e^{-xt} ν(t) dt` on the real axis; in particular `D'(0) = ∫ tν > 0`. -/
theorem deriv_thetaRenewalDenominator_ofReal (x : ℝ) :
    deriv thetaRenewalDenominator x =
      ((∫ t in Ioi (0 : ℝ), t * Real.exp (-(x * t)) * thetaRenewalIncrement t : ℝ) : ℂ) := by
  have hD := (differentiable_thetaRenewalDenominator x).hasDerivAt.comp_ofReal
  have hR : HasDerivAt (fun y : ℝ => thetaRenewalDenominator y)
      (((∫ t in Ioi (0 : ℝ), t * Real.exp (-(x * t)) * thetaRenewalIncrement t : ℝ)) : ℂ) x := by
    have h := ((hasDerivAt_thetaRenewalLaplaceReal x).const_sub (Θ 1)).ofReal_comp
    refine (h.congr_deriv (by push_cast; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun y => thetaRenewalDenominator_ofReal y)
  exact hD.unique hR

theorem thetaRenewalDenominator_zero_eq :
    thetaRenewalDenominator 0 = ((Θ 1 - thetaRenewalLaplaceReal 0 : ℝ) : ℂ) := by
  simpa using thetaRenewalDenominator_ofReal 0

theorem thetaRenewalLaplaceReal_zero_lt : thetaRenewalLaplaceReal 0 < Θ 1 :=
  (strictAnti_thetaRenewalLaplaceReal (show -(1 / 4 : ℝ) < 0 by norm_num)).trans
    thetaRenewalLaplaceReal_neg_quarter_lt

/-- `N(x) → 0` as `x → +∞`. -/
theorem tendsto_thetaRenewalLaplaceReal_atTop :
    Tendsto thetaRenewalLaplaceReal atTop (𝓝 0) := by
  obtain ⟨C, hC, hle⟩ := exists_exp_mul_thetaRenewalIncrement_le 0
  have hbound : ∀ x : ℝ, 0 < x → thetaRenewalLaplaceReal x ≤ C / x := by
    intro x hx
    have hI : ∫ t in Ioi (0 : ℝ), C * Real.exp (-x * t) = C / x := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]; simp; ring
    rw [← hI]
    refine setIntegral_mono_on (integrableOn_exp_mul_thetaRenewalIncrement x)
      ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul C) measurableSet_Ioi fun t ht => ?_
    have h := hle t (le_of_lt ht)
    rw [zero_mul, Real.exp_zero, one_mul] at h
    have h2 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [mem_Ioi.mp ht])
    calc Real.exp (-(x * t)) * thetaRenewalIncrement t ≤ Real.exp (-(x * t)) * C :=
          mul_le_mul_of_nonneg_left (h.trans (by nlinarith)) (Real.exp_pos _).le
      _ = C * Real.exp (-x * t) := by ring_nf
  refine squeeze_zero' (g := fun x => C / x)
    (Eventually.of_forall fun x => (thetaRenewalLaplaceReal_pos x).le) ?_
    (tendsto_const_nhds.div_atTop tendsto_id)
  filter_upwards [eventually_gt_atTop 0] with x hx using hbound x hx

end

end RHTower
