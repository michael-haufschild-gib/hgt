import GaloisForLFunctions.RHTower.ThetaRenewalPhaseLevel
import GaloisForLFunctions.HTGeometry.DecreasingSineTransformPositivity

/-!
# The theta source as the exit density of the renewal input

By the source identity `v'(2x) = -e^{x/2} k(x)/(2c)`, the exit density `g = -v'/a` satisfies
`2ac e^{-at} g(t) = k(t/2)`.  Since `v(0) = a` and `v → 0`, `g` is a probability density; its mean
is `q/a < 2/3`.  The even-source cosine formula then gives the service-law form
`Ξ(2z) = 2ac ∫₀^∞ e^{-at} cos(zt) g(t) dt`, and the one-sided connection is
`H(2z) = ac E_g[e^{-(a - iz)T}] = (a - iz) D(-iz) + icz`, the seam terms cancelling in
`H(2z) + H(-2z)`.

For `Re λ ≥ -a`, `Im λ > 0` the function `e^{-xt} ν(t)` is positive and strictly decreasing, so
`Im D(λ) = ∫₀^∞ e^{-xt} ν(t) sin(yt) dt > 0`; with `Re D ≥ c(1 - q)` and `D(λ̄) = conj D(λ)` this
puts `D(λ)` in the first and `D(-λ)` in the fourth quadrant.  Since `Q̂ = -log(D/c)` and
`2S(λ) = Q̂(-λ) - Q̂(λ)`, `Im S(λ) = (arg D(λ) - arg D(-λ))/2 ∈ (0, 1/5)`; equivalently
`0 < Re[Φ(z) - arctan(z/a)] < 1/5` for `Re z > 0`.

Finally `R = e^{at} Q` is the Lévy density of the geometric compound workload
`Y = Σ_{i<N} X_i` (`P(N = m) = (1 - q)q^m`, independent increments with density `v/q`):
`E[e^{-sY}] = (1 - q)/(1 - v̂(s)) = exp ∫₀^∞ (e^{-st} - 1) R(t) dt` for `Re s ≥ 0`, and
`D(λ) = c(1 - q)/E[e^{-(a + λ)Y}]` for `Re λ ≥ -a`; such a workload exists on
`ℕ × ℝ^ℕ`.
-/

open Complex Filter Topology Set MeasureTheory HurwitzZeta ProbabilityTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## The exit density of the renewal input -/

/-- The odd boundary kernel `W(t) = e^{-at}/t + Q(t)` is positive for `t > 0`. -/
theorem thetaRenewalOddKernel_pos {t : ℝ} (ht : 0 < t) : 0 < thetaRenewalOddKernel t :=
  add_pos (div_pos (Real.exp_pos _) ht) (thetaRenewalLogKernel_pos ht)

/-- The exit density `g = -v'/a`. -/
def thetaRenewalExitDensity (t : ℝ) : ℝ := -deriv thetaRenewalDensity t / (1 / 4)

theorem thetaRenewalExitDensity_pos (t : ℝ) : 0 < thetaRenewalExitDensity t :=
  div_pos (neg_pos.mpr (deriv_thetaRenewalDensity_neg t)) (by norm_num)

theorem continuous_thetaRenewalExitDensity : Continuous thetaRenewalExitDensity :=
  (continuous_deriv_thetaRenewalDensity.neg).div_const _

/-- `2ac e^{-at} g(t) = k(t/2)`: the literal theta source is the weighted exit density. -/
theorem thetaCuspFullSource_half_eq_exitDensity (t : ℝ) :
    thetaCuspFullSource (t / 2) =
      2 * (1 / 4) * Θ 1 * Real.exp (-(t / 4)) * thetaRenewalExitDensity t := by
  have hc := thetaSeam_pos
  have h := hasDerivAt_thetaRenewalDensity_two_mul (t / 2)
  rw [show 2 * (t / 2) = t by ring] at h
  rw [thetaRenewalExitDensity, h.deriv, show t / 2 / 2 = t / 4 by ring, neg_neg]
  have he : Real.exp (-(t / 4)) * Real.exp (t / 4) = 1 := by rw [← Real.exp_add]; simp
  have hc0 : Θ 1 ≠ 0 := hc.ne'
  have key : 2 * (1 / 4) * Θ 1 * Real.exp (-(t / 4)) *
      (Real.exp (t / 4) * thetaCuspFullSource (t / 2) / (2 * Θ 1) / (1 / 4)) =
      thetaCuspFullSource (t / 2) * (Real.exp (-(t / 4)) * Real.exp (t / 4)) := by
    field_simp
  rw [key, he, mul_one]

theorem tendsto_thetaRenewalDensity_atTop : Tendsto thetaRenewalDensity atTop (𝓝 0) := by
  have hβ : 0 < Real.pi - 3 / 2 := by linarith [Real.pi_gt_three]
  have hlim : Tendsto (fun t : ℝ => 1 / 4 * Real.exp (-((Real.pi - 3 / 2) * t))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_id.const_mul_atTop hβ))).const_mul (1 / 4 : ℝ)
    rw [mul_zero] at this; exact this
  refine squeeze_zero' (Eventually.of_forall fun t => (thetaRenewalDensity_pos t).le) ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact thetaRenewalDensity_le ht

/-- `g` is a probability density on `[0, ∞)`. -/
theorem integral_thetaRenewalExitDensity :
    ∫ t in Ioi (0 : ℝ), thetaRenewalExitDensity t = 1 := by
  have hG : ∀ x, HasDerivAt (fun t => -thetaRenewalDensity t / (1 / 4))
      (thetaRenewalExitDensity x) x := fun x =>
    ((hasDerivAt_thetaRenewalDensity_deriv x).neg.div_const _)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (g := fun t => -thetaRenewalDensity t / (1 / 4))
    ((continuous_thetaRenewalDensity.neg.div_const _).continuousWithinAt) (fun x _ => hG x)
    (fun x _ => (thetaRenewalExitDensity_pos x).le)
    (by simpa using (tendsto_thetaRenewalDensity_atTop.neg.div_const (1 / 4 : ℝ)))]
  rw [thetaRenewalDensity_zero]; norm_num

theorem integrableOn_thetaRenewalExitDensity : IntegrableOn thetaRenewalExitDensity (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg (g := fun t => -thetaRenewalDensity t / (1 / 4))
    ((continuous_thetaRenewalDensity.neg.div_const _).continuousWithinAt)
    (fun x _ => (hasDerivAt_thetaRenewalDensity_deriv x).neg.div_const _)
    (fun x _ => (thetaRenewalExitDensity_pos x).le)
    (by simpa using (tendsto_thetaRenewalDensity_atTop.neg.div_const (1 / 4 : ℝ)))

/-- **Mean exit time.** `∫₀^∞ t g(t) dt = q/a < 2/3`. -/
theorem integral_mul_thetaRenewalExitDensity :
    IntegrableOn (fun t => t * thetaRenewalExitDensity t) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), t * thetaRenewalExitDensity t = thetaRenewalMass / (1 / 4) := by
  have hcont : Continuous fun t => t * thetaRenewalExitDensity t :=
    continuous_id.mul continuous_thetaRenewalExitDensity
  have hparts : ∀ T : ℝ, ∫ t in (0 : ℝ)..T, t * thetaRenewalExitDensity t =
      -(T * thetaRenewalDensity T) / (1 / 4) + (∫ t in (0 : ℝ)..T, thetaRenewalDensity t) / (1 / 4) := by
    intro T
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := T)
      (u := fun t : ℝ => t) (u' := fun _ => 1) (v := fun t => -thetaRenewalDensity t / (1 / 4))
      (fun t _ => hasDerivAt_id t)
      (fun t _ => (hasDerivAt_thetaRenewalDensity_deriv t).neg.div_const _)
      intervalIntegrable_const (continuous_thetaRenewalExitDensity.intervalIntegrable _ _)
    rw [show (∫ t in (0 : ℝ)..T, t * thetaRenewalExitDensity t) =
      ∫ x in (0 : ℝ)..T, x * (-deriv thetaRenewalDensity x / (1 / 4)) from rfl, h]
    simp only [one_mul, zero_mul, sub_zero]
    rw [show (fun x => -thetaRenewalDensity x / (1 / 4)) =
      fun x => (-4) * thetaRenewalDensity x by funext x; ring,
      intervalIntegral.integral_const_mul]
    ring
  have hmassT : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, thetaRenewalDensity t ≤ thetaRenewalMass := by
    intro T hT
    rw [intervalIntegral.integral_of_le hT, thetaRenewalMass]
    exact setIntegral_mono_set integrableOn_thetaRenewalDensity
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ =>
        (thetaRenewalDensity_pos t).le)) Ioc_subset_Ioi_self.eventuallyLE
  have hint : IntegrableOn (fun t => t * thetaRenewalExitDensity t) (Ioi 0) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (thetaRenewalMass / (1 / 4)) 0
      (fun T => hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self) tendsto_id ?_
    filter_upwards [eventually_ge_atTop 0] with T hT
    have hnorm : ∫ t in (0 : ℝ)..id T, ‖t * thetaRenewalExitDensity t‖ =
        ∫ t in (0 : ℝ)..T, t * thetaRenewalExitDensity t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      have ht : t ∈ Icc 0 T := by simpa [uIcc_of_le hT] using ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht.1 (thetaRenewalExitDensity_pos t).le)]
    rw [hnorm, hparts]
    have h1 := hmassT T hT
    have h2 : 0 ≤ T * thetaRenewalDensity T := mul_nonneg hT (thetaRenewalDensity_pos T).le
    have : -(T * thetaRenewalDensity T) / (1 / 4) ≤ 0 := by
      rw [neg_div]; exact neg_nonpos.mpr (div_nonneg h2 (by norm_num))
    have h3 : (∫ t in (0 : ℝ)..T, thetaRenewalDensity t) / (1 / 4) ≤ thetaRenewalMass / (1 / 4) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    linarith
  refine ⟨hint, ?_⟩
  have hL1 := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have hL2 := intervalIntegral_tendsto_integral_Ioi 0 integrableOn_thetaRenewalDensity tendsto_id
  have hbd : Tendsto (fun T : ℝ => T * thetaRenewalDensity T) atTop (𝓝 0) := by
    have hβ : 0 < Real.pi - 3 / 2 := by linarith [Real.pi_gt_three]
    have hdom := (tendsto_mul_exp_neg_mul_atTop hβ).const_mul (1 / 4 : ℝ)
    rw [mul_zero] at hdom
    refine squeeze_zero' ?_ ?_ hdom
    · filter_upwards [eventually_ge_atTop 0] with T hT
      exact mul_nonneg hT (thetaRenewalDensity_pos T).le
    · filter_upwards [eventually_ge_atTop 0] with T hT
      calc T * thetaRenewalDensity T ≤ T * (1 / 4 * Real.exp (-((Real.pi - 3 / 2) * T))) :=
            mul_le_mul_of_nonneg_left (thetaRenewalDensity_le hT) hT
        _ = _ := by ring
  have hlim := (hbd.neg.div_const (1 / 4 : ℝ)).add (hL2.div_const (1 / 4 : ℝ))
  rw [neg_zero, zero_div, zero_add] at hlim
  exact tendsto_nhds_unique (hL1.congr fun T => hparts T) hlim

theorem integral_mul_thetaRenewalExitDensity_lt :
    ∫ t in Ioi (0 : ℝ), t * thetaRenewalExitDensity t < 2 / 3 := by
  rw [integral_mul_thetaRenewalExitDensity.2]
  have := thetaRenewalMass_lt
  rw [div_lt_iff₀ (by norm_num)]
  linarith

/-! ## The service-law form of `Ξ` (19) and the one-sided connection (19a) -/

/-- `∫₀^∞ F(t) dt = 2 ∫₀^∞ F(2x) dx`. -/
theorem setIntegral_Ioi_eq_two_mul_comp (F : ℝ → ℂ) :
    ∫ t in Ioi (0 : ℝ), F t = 2 * ∫ x in Ioi (0 : ℝ), F (2 * x) := by
  rw [integral_comp_mul_left_Ioi F 0 two_pos, mul_zero, Complex.real_smul]
  push_cast
  field_simp

/-- **The service-law form (19).** For every complex `z`,
`Ξ(2z) = 2ac ∫₀^∞ e^{-at} cos(zt) g(t) dt`. -/
theorem XiC_two_mul_eq_exitDensity (z : ℂ) :
    XiC (2 * z) = 2 * (1 / 4) * (Θ 1 : ℂ) *
      ∫ t in Ioi (0 : ℝ), (Real.exp (-(t / 4)) : ℂ) * Complex.cos (z * t) *
        (thetaRenewalExitDensity t : ℂ) := by
  have hL : XiC (2 * z) = 2 * ∫ x in Ioi (0 : ℝ), Complex.cos (2 * z * x) *
      (thetaCuspFullSource x : ℂ) := by
    rw [← sourceTransform_thetaSourceC,
      expMomentSource_thetaSourceC.sourceTransform_eq_integral_cos thetaSourceC_neg]
    rfl
  have hR : 2 * (1 / 4) * (Θ 1 : ℂ) * ∫ t in Ioi (0 : ℝ), (Real.exp (-(t / 4)) : ℂ) *
      Complex.cos (z * t) * (thetaRenewalExitDensity t : ℂ) =
      ∫ t in Ioi (0 : ℝ), (thetaCuspFullSource (t / 2) : ℂ) * Complex.cos (z * t) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [thetaCuspFullSource_half_eq_exitDensity]
    push_cast
    ring
  rw [hL, hR, setIntegral_Ioi_eq_two_mul_comp (fun t => (thetaCuspFullSource (t / 2) : ℂ) *
    Complex.cos (z * t))]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [show 2 * x / 2 = x by ring]
  push_cast
  ring_nf

/-- **The one-sided connection (19a).** `H(2z) = ac E_g[e^{-(a - iz)T}]`. -/
theorem thetaOneSidedConnection_two_mul_eq_exitDensity (z : ℂ) :
    thetaOneSidedConnection (2 * z) = (1 / 4) * (Θ 1 : ℂ) *
      ∫ t in Ioi (0 : ℝ), Complex.exp (-((1 / 4 - I * z) * t)) *
        (thetaRenewalExitDensity t : ℂ) := by
  rw [thetaOneSidedConnection, ← integral_const_mul,
    setIntegral_Ioi_eq_two_mul_comp (fun t => (1 / 4) * (Θ 1 : ℂ) *
      (Complex.exp (-((1 / 4 - I * z) * t)) * (thetaRenewalExitDensity t : ℂ))),
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  have h := thetaCuspFullSource_half_eq_exitDensity (2 * x)
  rw [show 2 * x / 2 = x by ring] at h
  rw [h]
  push_cast
  rw [show -((1 / 4 - I * z) * (2 * (x : ℂ))) = ((-(2 * x / 4) : ℝ) : ℂ) + I * (2 * z) * x by
    push_cast; ring, Complex.exp_add, ← Complex.ofReal_exp]
  push_cast
  ring

/-- **The seam term (19a).** `H(2z) = (a - iz) D(-iz) + icz`. -/
theorem thetaOneSidedConnection_two_mul_eq_denominator (z : ℂ) :
    thetaOneSidedConnection (2 * z) =
      (1 / 4 - I * z) * thetaRenewalDenominator (-(I * z)) + I * (Θ 1 : ℂ) * z := by
  have h := thetaOneSidedConnection_two_I_mul (-(I * z))
  have hj : jacobiThetaSum 1 = (Θ 1 : ℂ) := by
    simpa using jacobiThetaSum_ofReal_eq_evenKernel 1
  rw [show 2 * I * -(I * z) = 2 * z by linear_combination (-2 * z) * I_sq, hj] at h
  rw [h, thetaRenewalDenominator_eq, show 2 * I * -(I * z) = 2 * z by
    linear_combination (-2 * z) * I_sq]
  ring

/-- The seam terms cancel: `H(2z) + H(-2z) = (a - iz) D(-iz) + (a + iz) D(iz) = Ξ(2z)`. -/
theorem thetaOneSidedConnection_add_eq_two_ended (z : ℂ) :
    thetaOneSidedConnection (2 * z) + thetaOneSidedConnection (-(2 * z)) =
      (1 / 4 - I * z) * thetaRenewalDenominator (-(I * z)) +
        (1 / 4 + I * z) * thetaRenewalDenominator (I * z) := by
  rw [thetaOneSidedConnection_two_mul_eq_denominator, show -(2 * z) = 2 * (-z) by ring,
    thetaOneSidedConnection_two_mul_eq_denominator]
  simp only [mul_neg, neg_neg]
  ring

/-! ## The strict complex quadrant law (21) and the phase orientation (22) -/

theorem thetaMoment_one_le_two {y : ℝ} (hy : 0 < y) : thetaMoment 1 y ≤ thetaMoment 2 y := by
  refine (summable_thetaMoment_terms 1 hy).tsum_le_tsum (fun n => ?_)
    (summable_thetaMoment_terms 2 hy)
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hn (by norm_num)) (Real.exp_pos _).le

theorem hasDerivAt_exp_mul_thetaRenewalIncrement (x t : ℝ) :
    HasDerivAt (fun t => Real.exp (-(x * t)) * thetaRenewalIncrement t)
      (2 * Real.pi * Real.exp (-(x * t)) * Real.exp (5 / 4 * t) *
        ((5 / 4 - x) * thetaMoment 1 (Real.exp t) -
          Real.pi * Real.exp t * thetaMoment 2 (Real.exp t))) t := by
  have h1 : HasDerivAt (fun t => Real.exp (-(x * t))) (Real.exp (-(x * t)) * (-x)) t := by
    simpa using ((hasDerivAt_id t).const_mul x).neg.exp
  have h2 : HasDerivAt (fun t => Real.exp (5 / 4 * t)) (Real.exp (5 / 4 * t) * (5 / 4)) t := by
    simpa using ((hasDerivAt_id t).const_mul (5 / 4 : ℝ)).exp
  have h3 : HasDerivAt (fun t => thetaMoment 1 (Real.exp t))
      (-(Real.pi * thetaMoment 2 (Real.exp t)) * Real.exp t) t :=
    (hasDerivAt_thetaMoment 1 (Real.exp_pos t)).comp t (Real.hasDerivAt_exp t)
  exact (h1.fun_mul ((h2.const_mul (2 * Real.pi)).fun_mul h3)).congr_deriv (by ring)

/-- For `x ≥ -a`, `t ↦ e^{-xt} ν(t)` is strictly decreasing on `[0, ∞)`: every theta summand has
logarithmic derivative `a + 1 - x - πn²e^t ≤ 1 + 2a - π < 0`. -/
theorem strictAntiOn_exp_mul_thetaRenewalIncrement {x : ℝ} (hx : -(1 / 4) ≤ x) :
    StrictAntiOn (fun t => Real.exp (-(x * t)) * thetaRenewalIncrement t) (Ici 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici 0) (by
    have := continuous_thetaRenewalIncrement; fun_prop : Continuous fun t =>
      Real.exp (-(x * t)) * thetaRenewalIncrement t).continuousOn fun t ht => ?_
  rw [interior_Ici] at ht
  rw [(hasDerivAt_exp_mul_thetaRenewalIncrement x t).deriv]
  have hM1 := thetaMoment_pos 1 (Real.exp_pos t)
  have hM := thetaMoment_one_le_two (Real.exp_pos t)
  have he : 1 ≤ Real.exp t := Real.one_le_exp (le_of_lt ht)
  have hpi := Real.pi_gt_three
  have hin : (5 / 4 - x) * thetaMoment 1 (Real.exp t) -
      Real.pi * Real.exp t * thetaMoment 2 (Real.exp t) < 0 := by
    have h1 : Real.pi * thetaMoment 1 (Real.exp t) ≤ Real.pi * Real.exp t * thetaMoment 2 (Real.exp t) := by
      have : thetaMoment 1 (Real.exp t) ≤ Real.exp t * thetaMoment 2 (Real.exp t) := by
        nlinarith
      nlinarith [Real.pi_pos]
    nlinarith
  have hpos : 0 < 2 * Real.pi * Real.exp (-(x * t)) * Real.exp (5 / 4 * t) := by positivity
  exact mul_neg_of_pos_of_neg hpos hin

theorem integrableOn_exp_mul_thetaRenewalIncrement (x : ℝ) :
    IntegrableOn (fun t => Real.exp (-(x * t)) * thetaRenewalIncrement t) (Ioi 0) := by
  have h := (integrableOn_cexp_mul_of_superexp continuous_thetaRenewalIncrement
    thetaRenewalIncrement_superexp (x : ℂ)).norm
  refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaRenewalIncrement_pos t)]
  simp

/-- **Strict complex orientation (21).** For `Re λ ≥ -a` and `Im λ > 0`, `Im D(λ) > 0`. -/
theorem im_thetaRenewalDenominator_pos {s : ℂ} (hs : -(1 / 4) ≤ s.re) (him : 0 < s.im) :
    0 < (thetaRenewalDenominator s).im := by
  have hint := integrableOn_cexp_mul_of_superexp continuous_thetaRenewalIncrement
    thetaRenewalIncrement_superexp s
  have key : (thetaRenewalDenominator s).im = ∫ t in Ioi (0 : ℝ),
      Real.exp (-(s.re * t)) * thetaRenewalIncrement t * Real.sin (s.im * t) := by
    have hi := integral_im hint
    simp only [RCLike.im_to_complex] at hi
    rw [thetaRenewalDenominator, Complex.sub_im, Complex.ofReal_im, zero_sub, thetaRenewalLaplace,
      ← hi, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add, Complex.exp_im]
    simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, zero_add, Real.sin_neg]
    ring
  rw [key]
  exact integral_mul_sin_pos_of_strictAntiOn (by
    have := continuous_thetaRenewalIncrement; fun_prop)
    (strictAntiOn_exp_mul_thetaRenewalIncrement hs) (integrableOn_exp_mul_thetaRenewalIncrement _) him

/-- The renewal denominator is real on the real axis: `D(s̄) = conj D(s)`. -/
theorem thetaRenewalDenominator_conj (s : ℂ) :
    thetaRenewalDenominator ((starRingEnd ℂ) s) = (starRingEnd ℂ) (thetaRenewalDenominator s) := by
  rw [thetaRenewalDenominator, thetaRenewalDenominator, map_sub, Complex.conj_ofReal,
    thetaRenewalLaplace, thetaRenewalLaplace, ← integral_conj]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, map_neg, map_mul, Complex.conj_ofReal]

/-- **The quadrant law (21).** In the upper half of `|Re λ| < a`, `D(λ)` lies in the open first
quadrant and `D(-λ)` in the open fourth quadrant. -/
theorem thetaRenewalDenominator_quadrant {s : ℂ} (hs : |s.re| < 1 / 4) (him : 0 < s.im) :
    0 < (thetaRenewalDenominator s).re ∧ 0 < (thetaRenewalDenominator s).im ∧
      0 < (thetaRenewalDenominator (-s)).re ∧ (thetaRenewalDenominator (-s)).im < 0 := by
  have hc := thetaSeam_pos
  have hq := thetaRenewalMass_lt
  have hpos : 0 < Θ 1 * (1 - thetaRenewalMass) := mul_pos hc (by linarith)
  have hs1 : -(1 / 4) ≤ s.re := by linarith [abs_lt.mp hs]
  have hs2 : -(1 / 4) ≤ (-s).re := by simp; linarith [abs_lt.mp hs]
  refine ⟨lt_of_lt_of_le hpos (re_thetaRenewalDenominator_ge hs1),
    im_thetaRenewalDenominator_pos hs1 him, lt_of_lt_of_le hpos (re_thetaRenewalDenominator_ge hs2),
    ?_⟩
  have h3 : -(1 / 4) ≤ (-(starRingEnd ℂ) s).re := by simp; linarith [abs_lt.mp hs]
  have h4 : 0 < (-(starRingEnd ℂ) s).im := by simp; exact him
  have h := im_thetaRenewalDenominator_pos h3 h4
  have e : -s = (starRingEnd ℂ) (-(starRingEnd ℂ) s) := by simp
  rw [e, thetaRenewalDenominator_conj, Complex.conj_im]
  linarith

/-- `Q̂(s) = -log(D(s)/c)` has imaginary part `-arg D(s)`. -/
theorem im_thetaRenewalLogKernelLaplace {s : ℂ} (hs : -(1 / 4) ≤ s.re) :
    (thetaRenewalLogKernelLaplace s).im = -(thetaRenewalDenominator s).arg := by
  have hc := thetaSeam_pos
  have hcC : ((Θ 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have e : 1 - thetaRenewalLaplace s / (Θ 1 : ℂ) =
      ((1 / Θ 1 : ℝ) : ℂ) * thetaRenewalDenominator s := by
    rw [thetaRenewalDenominator]; push_cast; field_simp
  rw [thetaRenewalLogKernelLaplace_eq hs, Complex.neg_im, Complex.log_im, e,
    Complex.arg_real_mul _ (by positivity)]

/-- **Phase orientation (22).** In the upper half of `|Re λ| < a`, `0 < Im S(λ) < 1/5`. -/
theorem im_thetaRenewalSinTransform_mem {s : ℂ} (hs : |s.re| < 1 / 4) (him : 0 < s.im) :
    0 < (thetaRenewalSinTransform s).im ∧ (thetaRenewalSinTransform s).im < 1 / 5 := by
  obtain ⟨-, hI1, -, hI2⟩ := thetaRenewalDenominator_quadrant hs him
  refine ⟨?_, lt_of_le_of_lt (Complex.im_le_norm _) (norm_thetaRenewalSinTransform_lt hs.le)⟩
  have hs1 : -(1 / 4) ≤ s.re := by linarith [abs_lt.mp hs]
  have hs2 : -(1 / 4) ≤ (-s).re := by simp; linarith [abs_lt.mp hs]
  have hQ := thetaRenewalLogKernelLaplace_eq_cos_sub_sin hs.le
  have hQn := thetaRenewalLogKernelLaplace_eq_cos_sub_sin (s := -s) (by simpa using hs.le)
  rw [thetaRenewalCosTransform_neg, thetaRenewalSinTransform_neg] at hQn
  have h2S : 2 * thetaRenewalSinTransform s =
      thetaRenewalLogKernelLaplace (-s) - thetaRenewalLogKernelLaplace s := by
    rw [hQ, hQn]; ring
  have hIm := congrArg Complex.im h2S
  rw [Complex.sub_im, im_thetaRenewalLogKernelLaplace hs1, im_thetaRenewalLogKernelLaplace hs2]
    at hIm
  simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero] at hIm
  have ha1 : 0 < (thetaRenewalDenominator s).arg := by
    rcases (Complex.arg_nonneg_iff.mpr hI1.le).lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.arg_eq_zero_iff.mp h.symm).2 hI1.ne'
  have ha2 := Complex.arg_neg_iff.mpr hI2
  linarith

/-- **Phase orientation on the waiting-time side (22).** For `Re z > 0`, `|Im z| < a`,
`0 < Re[Φ(z) - arctan(z/a)] < 1/5`. -/
theorem re_thetaWaitingPhase_sub_arctan_mem {z : ℂ} (hz : |z.im| < 1 / 4) (hre : 0 < z.re) :
    0 < (thetaWaitingPhase z - Complex.arctan (4 * z)).re ∧
      (thetaWaitingPhase z - Complex.arctan (4 * z)).re < 1 / 5 := by
  have hs : |(I * z).re| < 1 / 4 := by simpa using hz
  have him : 0 < (I * z).im := by simpa using hre
  rw [thetaWaitingPhase_eq_arctan_add hz, add_sub_cancel_left,
    ← neg_I_mul_thetaRenewalSinTransform_I_mul]
  have h := im_thetaRenewalSinTransform_mem hs him
  simpa using h

/-! ## The compound-Poisson workload (20) -/

/-- The Laplace transform `v̂(s) = ∫₀^∞ e^{-st} v(t) dt` of the renewal density. -/
def thetaRenewalDensityLaplace (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (thetaRenewalDensity t : ℂ)

/-- `v̂(s) = N(s - a)/c`. -/
theorem thetaRenewalDensityLaplace_eq (s : ℂ) :
    thetaRenewalDensityLaplace s = thetaRenewalLaplace (s - 1 / 4) / (Θ 1 : ℂ) := by
  rw [thetaRenewalDensityLaplace, thetaRenewalLaplace, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [thetaRenewalDensity, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_exp,
    show cexp (-((s - 1 / 4) * t)) = cexp (-(s * t)) * cexp ((t / 4 : ℝ) : ℂ) by
      rw [← Complex.exp_add]; push_cast; ring_nf]
  ring

theorem thetaRenewalDensityLaplace_zero :
    thetaRenewalDensityLaplace 0 = (thetaRenewalMass : ℂ) := by
  rw [thetaRenewalDensityLaplace, thetaRenewalMass, ← integral_complex_ofReal]
  simp

theorem norm_thetaRenewalDensityLaplace_le {s : ℂ} (hs : 0 ≤ s.re) :
    ‖thetaRenewalDensityLaplace s‖ ≤ thetaRenewalMass := by
  have hc := thetaSeam_pos
  rw [thetaRenewalDensityLaplace_eq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
    div_le_iff₀ hc, mul_comm]
  exact norm_thetaRenewalLaplace_le (by simp; linarith)

theorem norm_thetaRenewalDensityLaplace_lt_one {s : ℂ} (hs : 0 ≤ s.re) :
    ‖thetaRenewalDensityLaplace s‖ < 1 :=
  (norm_thetaRenewalDensityLaplace_le hs).trans_lt (thetaRenewalMass_lt.trans (by norm_num))

theorem one_sub_thetaRenewalDensityLaplace_ne_zero {s : ℂ} (hs : 0 ≤ s.re) :
    1 - thetaRenewalDensityLaplace s ≠ 0 := by
  intro h
  have h1 : thetaRenewalDensityLaplace s = 1 := by linear_combination -h
  have := norm_thetaRenewalDensityLaplace_lt_one hs
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

/-- `D(λ) = c (1 - v̂(λ + a))`. -/
theorem thetaRenewalDenominator_eq_densityLaplace (s : ℂ) :
    thetaRenewalDenominator s = (Θ 1 : ℂ) * (1 - thetaRenewalDensityLaplace (1 / 4 + s)) := by
  have hc : (Θ 1 : ℂ) ≠ 0 := by exact_mod_cast thetaSeam_pos.ne'
  rw [thetaRenewalDensityLaplace_eq, show 1 / 4 + s - 1 / 4 = s by ring, thetaRenewalDenominator]
  field_simp

/-- The Lévy density `R(t) = e^{at} Q(t)` of the workload. -/
def thetaRenewalLevyDensity (t : ℝ) : ℝ := Real.exp (t / 4) * thetaRenewalLogKernel t

theorem integrableOn_thetaRenewalLevyDensity : IntegrableOn thetaRenewalLevyDensity (Ioi 0) :=
  integrableOn_exp_mul_thetaRenewalLogKernel

theorem integral_cexp_mul_thetaRenewalLevyDensity {s : ℂ} (hs : 0 ≤ s.re) :
    ∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (thetaRenewalLevyDensity t : ℂ) =
      -Complex.log (1 - thetaRenewalDensityLaplace s) := by
  have h := thetaRenewalLogKernelLaplace_eq (s := s - 1 / 4) (by simp; linarith)
  rw [thetaRenewalDensityLaplace_eq, ← h, thetaRenewalLogKernelLaplace]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [thetaRenewalLevyDensity, Complex.ofReal_mul, Complex.ofReal_exp,
    show cexp (-((s - 1 / 4) * t)) = cexp (-(s * t)) * cexp ((t / 4 : ℝ) : ℂ) by
      rw [← Complex.exp_add]; push_cast; ring_nf]
  ring

theorem integral_thetaRenewalLevyDensity :
    ∫ t in Ioi (0 : ℝ), (thetaRenewalLevyDensity t : ℂ) =
      -Complex.log (1 - (thetaRenewalMass : ℂ)) := by
  rw [← thetaRenewalDensityLaplace_zero, ← integral_cexp_mul_thetaRenewalLevyDensity le_rfl]
  simp

/-- **Compound-Poisson form (20).** For `Re s ≥ 0`,
`exp ∫₀^∞ (e^{-st} - 1) R(t) dt = (1 - q)/(1 - v̂(s))`. -/
theorem cexp_integral_thetaRenewalLevyDensity {s : ℂ} (hs : 0 ≤ s.re) :
    cexp (∫ t in Ioi (0 : ℝ), (cexp (-(s * t)) - 1) * (thetaRenewalLevyDensity t : ℂ)) =
      (1 - thetaRenewalMass) / (1 - thetaRenewalDensityLaplace s) := by
  have hR := integrableOn_thetaRenewalLevyDensity
  have hA : IntegrableOn (fun t : ℝ => cexp (-(s * t)) * (thetaRenewalLevyDensity t : ℂ))
      (Ioi 0) := by
    refine hR.mono' (by
      have := continuous_thetaRenewalLogKernel
      unfold thetaRenewalLevyDensity; fun_prop : Continuous fun t : ℝ =>
        cexp (-(s * t)) * (thetaRenewalLevyDensity t : ℂ)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have hpos : 0 < thetaRenewalLevyDensity t :=
      mul_pos (Real.exp_pos _) (thetaRenewalLogKernel_pos ht)
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    refine mul_le_of_le_one_left hpos.le (Real.exp_le_one_iff.mpr ?_)
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, neg_nonpos]
    exact mul_nonneg hs (le_of_lt ht)
  have hB : IntegrableOn (fun t : ℝ => (thetaRenewalLevyDensity t : ℂ)) (Ioi 0) := hR.ofReal
  have e : ∀ t : ℝ, (cexp (-(s * t)) - 1) * (thetaRenewalLevyDensity t : ℂ) =
      cexp (-(s * t)) * (thetaRenewalLevyDensity t : ℂ) - (thetaRenewalLevyDensity t : ℂ) :=
    fun t => by ring
  simp_rw [e]
  have hq : (1 : ℂ) - thetaRenewalMass ≠ 0 := by
    have := thetaRenewalMass_lt
    exact_mod_cast (show (1 : ℝ) - thetaRenewalMass ≠ 0 by linarith)
  rw [integral_sub hA hB, integral_cexp_mul_thetaRenewalLevyDensity hs,
    integral_thetaRenewalLevyDensity, show -Complex.log (1 - thetaRenewalDensityLaplace s) -
      -Complex.log (1 - (thetaRenewalMass : ℂ)) = Complex.log (1 - (thetaRenewalMass : ℂ)) -
        Complex.log (1 - thetaRenewalDensityLaplace s) by ring, Complex.exp_sub,
    Complex.exp_log hq, Complex.exp_log (one_sub_thetaRenewalDensityLaplace_ne_zero hs)]

/-- The survival function in Lévy form: `s(t) = e^{-at} (1 + t R(t))`. -/
theorem thetaRenewalReflectionProfile_eq_levy (t : ℝ) :
    thetaRenewalReflectionProfile t =
      Real.exp (-(t / 4)) * (1 + t * thetaRenewalLevyDensity t) := by
  rw [thetaRenewalReflectionProfile, thetaRenewalMomentKernel, thetaRenewalLevyDensity]
  have : Real.exp (-(t / 4)) * Real.exp (t / 4) = 1 := by rw [← Real.exp_add]; simp
  linear_combination (-(t * thetaRenewalLogKernel t)) * this

/-- The law of one increment of the workload: density `v/q` on `(0, ∞)`. -/
def thetaRenewalIncrementLaw : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal (thetaRenewalDensity t / thetaRenewalMass)

theorem thetaRenewalIncrementLaw_Iic : thetaRenewalIncrementLaw (Iic 0) = 0 := by
  rw [thetaRenewalIncrementLaw, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, show Iic (0 : ℝ) ∩ Ioi 0 = ∅ by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and,
        not_lt]; intro h; exact h]
  simp

theorem integral_cexp_thetaRenewalIncrementLaw (s : ℂ) :
    ∫ x, cexp (-(s * x)) ∂thetaRenewalIncrementLaw =
      thetaRenewalDensityLaplace s / (thetaRenewalMass : ℂ) := by
  have hq := thetaRenewalMass_pos
  rw [thetaRenewalIncrementLaw, integral_withDensity_eq_integral_toReal_smul
    ((continuous_thetaRenewalDensity.div_const _).measurable.ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), thetaRenewalDensityLaplace,
    ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [ENNReal.toReal_ofReal (div_nonneg (thetaRenewalDensity_pos t).le hq.le), Complex.real_smul]
  push_cast
  ring

/-- **The geometric compound workload (20).** Let `Y = Σ_{i < N} X_i`, where `N` is geometric,
`P(N = m) = (1 - q) q^m`, the increments `X_i` are independent with density `v/q`, and `N` is
independent of `(X_i)`.  Then `E[e^{-sY}] = (1 - q)/(1 - v̂(s))` for `Re s ≥ 0`. -/
theorem integral_cexp_compoundGeometric {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {N : Ω → ℕ} {X : ℕ → Ω → ℝ} (hN : Measurable N)
    (hX : ∀ i, Measurable (X i))
    (hlawN : ∀ m, P (N ⁻¹' {m}) = ENNReal.ofReal ((1 - thetaRenewalMass) * thetaRenewalMass ^ m))
    (hlawX : ∀ i, P.map (X i) = thetaRenewalIncrementLaw) (hindX : iIndepFun X P)
    (hindN : IndepFun N (fun ω i => X i ω) P) {s : ℂ} (hs : 0 ≤ s.re) :
    ∫ ω, cexp (-(s * ∑ i ∈ Finset.range (N ω), X i ω)) ∂P =
      (1 - thetaRenewalMass) / (1 - thetaRenewalDensityLaplace s) := by
  have hq0 := thetaRenewalMass_pos
  have hq1 := thetaRenewalMass_lt
  set q := thetaRenewalMass
  set S : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ Finset.range m, X i ω with hSdef
  have hSm : ∀ m, Measurable (S m) := fun m => Finset.measurable_sum _ fun i _ => hX i
  have hY : Measurable fun ω => S (N ω) ω := by
    have hG : Measurable fun p : Ω × ℕ => S p.2 p.1 :=
      measurable_from_prod_countable_left fun m => hSm m
    exact hG.comp (measurable_id.prodMk hN)
  -- the increments are nonnegative almost surely
  have hnn : ∀ᵐ ω ∂P, ∀ i, 0 ≤ X i ω := by
    refine ae_all_iff.mpr fun i => ?_
    have h0 : P (X i ⁻¹' Iio 0) = 0 := by
      rw [← Measure.map_apply (hX i) measurableSet_Iio, hlawX]
      exact measure_mono_null Iio_subset_Iic_self thetaRenewalIncrementLaw_Iic
    rw [ae_iff]
    simp only [not_le]
    exact h0
  have hbound : ∀ᵐ ω ∂P, ‖cexp (-(s * S (N ω) ω))‖ ≤ 1 := by
    filter_upwards [hnn] with ω hω
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, neg_nonpos]
    exact mul_nonneg hs (Finset.sum_nonneg fun i _ => hω i)
  have hFm : Measurable fun ω => cexp (-(s * S (N ω) ω)) :=
    Complex.continuous_exp.measurable.comp ((measurable_const.mul
      (Complex.measurable_ofReal.comp hY)).neg)
  have hFint : Integrable (fun ω => cexp (-(s * S (N ω) ω))) P :=
    (integrable_const (1 : ℝ)).mono' hFm.aestronglyMeasurable hbound
  -- decomposition over the value of `N`
  have hU : (⋃ m, N ⁻¹' {m}) = univ := by ext ω; simp
  have hdisj : Pairwise (Function.onFun Disjoint fun m : ℕ => N ⁻¹' {m}) := by
    intro m n hmn
    exact Disjoint.preimage _ (disjoint_singleton.mpr hmn)
  have hdec := integral_iUnion (μ := P) (f := fun ω => cexp (-(s * S (N ω) ω)))
    (fun m => hN (measurableSet_singleton m)) hdisj (by rw [hU]; exact hFint.integrableOn)
  rw [hU, setIntegral_univ] at hdec
  -- the increment Laplace transform
  have hφ : ∀ i, ∫ ω, cexp (-(s * X i ω)) ∂P = thetaRenewalDensityLaplace s / (q : ℂ) := by
    intro i
    rw [← integral_cexp_thetaRenewalIncrementLaw, ← hlawX i,
      integral_map (hX i).aemeasurable (by fun_prop : Continuous fun x : ℝ =>
        cexp (-(s * x))).aestronglyMeasurable]
  -- each slice
  have hslice : ∀ m, ∫ ω in N ⁻¹' {m}, cexp (-(s * S (N ω) ω)) ∂P =
      ((1 - q) * q ^ m : ℝ) * (thetaRenewalDensityLaplace s / (q : ℂ)) ^ m := by
    intro m
    have hcongr : ∫ ω in N ⁻¹' {m}, cexp (-(s * S (N ω) ω)) ∂P =
        ∫ ω, (fun n : ℕ => if n = m then (1 : ℂ) else 0) (N ω) *
          (fun x : ℕ → ℝ => cexp (-(s * ∑ i ∈ Finset.range m, x i))) (fun i => X i ω) ∂P := by
      rw [← integral_indicator (hN (measurableSet_singleton m))]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      by_cases h : N ω = m
      · simp [indicator, h, hSdef]
      · simp [indicator, h]
    have hXseq : Measurable fun ω => fun i => X i ω := measurable_pi_lambda _ hX
    have hg : Measurable fun x : ℕ → ℝ => cexp (-(s * ∑ i ∈ Finset.range m, x i)) :=
      Complex.continuous_exp.measurable.comp ((measurable_const.mul (Complex.measurable_ofReal.comp
        (Finset.measurable_sum _ fun i _ => measurable_pi_apply i))).neg)
    rw [hcongr, hindN.integral_fun_comp_mul_comp (f := fun n : ℕ => if n = m then (1 : ℂ) else 0)
      (g := fun x : ℕ → ℝ => cexp (-(s * ∑ i ∈ Finset.range m, x i))) hN.aemeasurable
      hXseq.aemeasurable (measurable_of_countable _).aestronglyMeasurable hg.aestronglyMeasurable]
    congr 1
    · have h1 : ∫ ω, (fun n : ℕ => if n = m then (1 : ℂ) else 0) (N ω) ∂P =
          ((P.real (N ⁻¹' {m}) : ℝ) : ℂ) := by
        rw [← integral_indicator_one (hN (measurableSet_singleton m)), ← integral_complex_ofReal]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        by_cases h : N ω = m <;> simp [indicator, h]
      rw [h1, measureReal_def, hlawN,
        ENNReal.toReal_ofReal (mul_nonneg (by linarith) (pow_nonneg hq0.le m))]
    · have hind : iIndepFun (fun i : Fin m => X i) P := hindX.precomp Fin.val_injective
      have hprod := hind.integral_fun_prod_comp (X := fun i : Fin m => X i)
        (f := fun _ (x : ℝ) => cexp (-(s * x)))
        (fun i => (hX i).aemeasurable) (fun i => (by fun_prop : Continuous fun x : ℝ =>
          cexp (-(s * x))).aestronglyMeasurable)
      have e : ∀ ω, cexp (-(s * ∑ i ∈ Finset.range m, X i ω)) =
          ∏ i : Fin m, cexp (-(s * X i ω)) := by
        intro ω
        rw [← Complex.exp_sum, Finset.sum_range (fun i => X i ω)]
        push_cast
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      simp only
      simp_rw [e]
      rw [hprod]
      simp only [hφ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hdec, tsum_congr hslice]
  have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hgeom : ∀ m : ℕ, ((((1 - q) * q ^ m : ℝ)) : ℂ) *
      (thetaRenewalDensityLaplace s / (q : ℂ)) ^ m =
      ((1 - q : ℝ) : ℂ) * thetaRenewalDensityLaplace s ^ m := by
    intro m
    rw [div_pow]
    push_cast
    field_simp
  rw [tsum_congr hgeom, tsum_mul_left, tsum_geometric_of_norm_lt_one
    (norm_thetaRenewalDensityLaplace_lt_one hs), div_eq_mul_inv]
  push_cast
  ring

/-- **Reciprocal workload form (20).** Under the hypotheses of the previous theorem,
`D(λ) = c(1 - q)/E[e^{-(a + λ)Y}]` for `Re λ ≥ -a`. -/
theorem thetaRenewalDenominator_eq_compoundGeometric {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : Ω → ℕ} {X : ℕ → Ω → ℝ} (hN : Measurable N)
    (hX : ∀ i, Measurable (X i))
    (hlawN : ∀ m, P (N ⁻¹' {m}) = ENNReal.ofReal ((1 - thetaRenewalMass) * thetaRenewalMass ^ m))
    (hlawX : ∀ i, P.map (X i) = thetaRenewalIncrementLaw) (hindX : iIndepFun X P)
    (hindN : IndepFun N (fun ω i => X i ω) P) {s : ℂ} (hs : -(1 / 4) ≤ s.re) :
    thetaRenewalDenominator s = (Θ 1 : ℂ) * (1 - thetaRenewalMass) /
      ∫ ω, cexp (-((1 / 4 + s) * ∑ i ∈ Finset.range (N ω), X i ω)) ∂P := by
  have hs' : 0 ≤ (1 / 4 + s).re := by simp; linarith
  have hq : (1 : ℂ) - thetaRenewalMass ≠ 0 := by
    have := thetaRenewalMass_lt
    exact_mod_cast (show (1 : ℝ) - thetaRenewalMass ≠ 0 by linarith)
  rw [integral_cexp_compoundGeometric hN hX hlawN hlawX hindX hindN hs',
    thetaRenewalDenominator_eq_densityLaplace]
  have := one_sub_thetaRenewalDensityLaplace_ne_zero hs'
  field_simp

instance isProbabilityMeasure_thetaRenewalIncrementLaw :
    IsProbabilityMeasure thetaRenewalIncrementLaw := by
  constructor
  have hq := thetaRenewalMass_pos
  have hint : IntegrableOn (fun t => thetaRenewalDensity t / thetaRenewalMass) (Ioi 0) :=
    integrableOn_thetaRenewalDensity.div_const _
  rw [thetaRenewalIncrementLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t _ => div_nonneg (thetaRenewalDensity_pos t).le hq.le)),
    integral_div, ← thetaRenewalMass, div_self hq.ne', ENNReal.ofReal_one]

/-- The geometric compound workload exists: on `ℕ × ℝ^ℕ` with the geometric law of parameter
`1 - q` times the infinite product of increment laws, the coordinates satisfy all hypotheses of
`integral_cexp_compoundGeometric`. -/
theorem exists_compoundGeometric :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (N : Ω → ℕ) (X : ℕ → Ω → ℝ), Measurable N ∧ (∀ i, Measurable (X i)) ∧
      (∀ m, P (N ⁻¹' {m}) = ENNReal.ofReal ((1 - thetaRenewalMass) * thetaRenewalMass ^ m)) ∧
      (∀ i, P.map (X i) = thetaRenewalIncrementLaw) ∧ iIndepFun X P ∧
      IndepFun N (fun ω i => X i ω) P := by
  have hq0 := thetaRenewalMass_pos
  have hq1 := thetaRenewalMass_lt
  set p : unitInterval := ⟨1 - thetaRenewalMass, by constructor <;> linarith⟩ with hpdef
  have hp : p ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    simp [hpdef] at this
    linarith
  set Q : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => thetaRenewalIncrementLaw
  set P : Measure (ℕ × (ℕ → ℝ)) := (geometricMeasure p).prod Q
  have hXm : ∀ i, Measurable fun ω : ℕ × (ℕ → ℝ) => ω.2 i := fun i =>
    (measurable_pi_apply i).comp measurable_snd
  have hlawX : ∀ i, P.map (fun ω : ℕ × (ℕ → ℝ) => ω.2 i) = thetaRenewalIncrementLaw := by
    intro i
    rw [show (fun ω : ℕ × (ℕ → ℝ) => ω.2 i) = (fun x : ℕ → ℝ => x i) ∘ Prod.snd from rfl,
      ← Measure.map_map (measurable_pi_apply i) measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul, Measure.infinitePi_map_eval]
  refine ⟨ℕ × (ℕ → ℝ), inferInstance, P, inferInstance, Prod.fst, fun i ω => ω.2 i,
    measurable_fst, hXm, fun m => ?_, hlawX, ?_, ?_⟩
  · rw [show (Prod.fst ⁻¹' {m} : Set (ℕ × (ℕ → ℝ))) = {m} ×ˢ univ by ext; simp,
      Measure.prod_prod, measure_univ, mul_one, geometricMeasure_singleton hp]
    congr 1
    simp only [hpdef]
    ring
  · rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀ (by fun_prop)]
    simp_rw [hlawX]
    rw [show (fun ω : ℕ × (ℕ → ℝ) => fun i => ω.2 i) = Prod.snd from rfl, Measure.map_snd_prod,
      measure_univ, one_smul]
  · exact indepFun_prod (X := fun n : ℕ => n) (Y := fun x : ℕ → ℝ => x) measurable_id measurable_id

end RHTower
