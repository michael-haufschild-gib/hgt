import Mathlib

/-!
# Connes' complex-place log-area asymptotics

Formalization of Appendix II (49)-(53) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

To compare his principal value `∫'` with Weil's `Pfw` at a complex place, Connes must show that the
truncated area

  `j(ε) = ∫_{|z| ≤ 1, |1-z| ≥ ε} |1-z|_ℂ^{-1} |dz ∧ dz̄|`

satisfies `j(ε) = 2π log(1/ε) + o(1)`.  Under `Z = log(1-z)` the region becomes a subdomain `D` of
the rectangle `R_ε = [log ε, log 2] × [-π/2, π/2]`, bounded by the curve `x = log(2 cos y)`, and

  `j(ε) = 4 ∫_{log ε}^{log 2} arccos(e^x/2) dx`,      (51)
  `area(R_ε ∖ D) → 4 ∫_{-∞}^{log 2} arcsin(e^x/2) dx = -4 ∫_0^{π/2} log(sin u) du = 2π log 2`.  (53)

Everything here is proved unconditionally:

* `connes_arccos_add_arcsin_integral` - (51) in complement form: the `arccos` area plus the `arcsin`
  area is the rectangle area `2π(log 2 - log ε)`.
* `connes_arcIntegral_substitution` - the substitution `x = log(2 sin θ)` turning the `arcsin`
  integral into `∫ θ cot θ dθ`.
* `connes_arcIntegral_ibp` - the integration by parts `∫_θ^{π/2} u cot u du =
  -θ log sin θ - ∫_θ^{π/2} log sin u du`.
* `connes_theta_mul_log_sin_tendsto`, `connes_logSin_integral_tendsto` - the two endpoint limits.
* `connes_arcIntegral_tendsto_atBot` - (53): the complementary area tends to `(π/2) log 2`, using
  mathlib's `integral_log_sin_zero_pi_div_two`.
* `connes_j_asymptotics` - the conclusion `j(ε) - 2π log(1/ε) → 0`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open MeasureTheory Set Real Filter Topology intervalIntegral

/-- Connes' integrand of Appendix II (51). -/
def connesArcIntegrand (x : ℝ) : ℝ := Real.arcsin (Real.exp x / 2)

theorem continuous_connesArcIntegrand : Continuous connesArcIntegrand :=
  Real.continuous_arcsin.comp (by fun_prop)

/-- **Appendix II (51), complement form.**  `arccos = π/2 - arcsin` turns the area under the
hyperbola-bounded region into the rectangle area minus the complementary area. -/
theorem connes_arccos_add_arcsin_integral (a : ℝ) :
    4 * (∫ x in a..(Real.log 2), Real.arccos (Real.exp x / 2))
      + 4 * (∫ x in a..(Real.log 2), connesArcIntegrand x)
      = 2 * π * (Real.log 2 - a) := by
  have h : (fun x : ℝ => Real.arccos (Real.exp x / 2))
      = fun x : ℝ => π / 2 - connesArcIntegrand x := by
    funext x
    exact Real.arccos_eq_pi_div_two_sub_arcsin _
  rw [h, intervalIntegral.integral_sub intervalIntegrable_const
    (continuous_connesArcIntegrand.intervalIntegrable _ _), intervalIntegral.integral_const,
    smul_eq_mul]
  ring

/-- `θ log (sin θ) → 0` as `θ → 0⁺`. -/
theorem connes_theta_mul_log_sin_tendsto :
    Tendsto (fun θ : ℝ => θ * Real.log (Real.sin θ)) (𝓝[>] 0) (𝓝 0) := by
  have hmul : Tendsto (fun θ : ℝ => θ * Real.log θ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := Real.continuous_mul_log.tendsto (0:ℝ)
    simp only [Real.log_zero, mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hconst : Tendsto (fun θ : ℝ => θ * Real.log (2 / π)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h : Tendsto (fun θ : ℝ => θ * Real.log (2 / π)) (𝓝 (0:ℝ)) (𝓝 (0 * Real.log (2/π))) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlow : Tendsto (fun θ : ℝ => θ * Real.log θ + θ * Real.log (2 / π))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have := hmul.add hconst
    rwa [add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hmul ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
      (Iio_mem_nhds (by positivity : (0:ℝ) < π / 2))] with θ hθ0 hθ
    have hθ0' : (0:ℝ) < θ := hθ0
    have hθ' : θ < π / 2 := hθ
    have hsin : 2 / π * θ ≤ Real.sin θ := Real.mul_le_sin hθ0'.le (le_of_lt hθ')
    have hpos : (0:ℝ) < 2 / π * θ := by positivity
    have hlog : Real.log (2 / π * θ) ≤ Real.log (Real.sin θ) :=
      Real.log_le_log hpos hsin
    rw [Real.log_mul (by positivity) (ne_of_gt hθ0')] at hlog
    nlinarith [hlog, hθ0']
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
      (Iio_mem_nhds (by positivity : (0:ℝ) < π / 2))] with θ hθ0 hθ
    have hθ0' : (0:ℝ) < θ := hθ0
    have hθ' : θ < π / 2 := hθ
    have hsinpos : (0:ℝ) < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ0' (by linarith [Real.pi_pos])
    have hsin : Real.sin θ ≤ θ := Real.sin_le hθ0'.le
    have hlog : Real.log (Real.sin θ) ≤ Real.log θ := Real.log_le_log hsinpos hsin
    nlinarith [hlog, hθ0']

theorem connes_sin_pos_of_mem {θ u : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ π / 2)
    (hu : u ∈ uIcc θ (π / 2)) : 0 < Real.sin u := by
  rw [uIcc_of_le hθ] at hu
  exact Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hθ0 hu.1)
    (lt_of_le_of_lt hu.2 (by linarith [Real.pi_pos]))

/-- **Appendix II (51), the substitution `x = log (2 sin θ)`.** -/
theorem connes_arcIntegral_substitution {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ π / 2) :
    (∫ x in (Real.log (2 * Real.sin θ))..(Real.log 2), connesArcIntegrand x)
      = ∫ u in θ..(π / 2), (Real.cos u / Real.sin u) * u := by
  have hderiv : ∀ u ∈ uIcc θ (π / 2),
      HasDerivAt (fun t : ℝ => Real.log (2 * Real.sin t)) (Real.cos u / Real.sin u) u := by
    intro u hu
    have hspos : 0 < Real.sin u := connes_sin_pos_of_mem hθ0 hθ hu
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.sin t) (2 * Real.cos u) u :=
      (Real.hasDerivAt_sin u).const_mul 2
    have h2 := h1.log (by positivity)
    have hval : 2 * Real.cos u / (2 * Real.sin u) = Real.cos u / Real.sin u := by
      rw [mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]
    rwa [hval] at h2
  have hcont : ContinuousOn (fun u : ℝ => Real.cos u / Real.sin u) (uIcc θ (π / 2)) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro u hu
    exact ne_of_gt (connes_sin_pos_of_mem hθ0 hθ hu)
  have hsub := intervalIntegral.integral_deriv_smul_comp hderiv hcont
    continuous_connesArcIntegrand
  have hend : Real.log (2 * Real.sin (π / 2)) = Real.log 2 := by
    rw [Real.sin_pi_div_two, mul_one]
  rw [hend] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr ?_
  intro u hu
  have hspos : 0 < Real.sin u := connes_sin_pos_of_mem hθ0 hθ hu
  rw [uIcc_of_le hθ] at hu
  have hu1 : -(π / 2) ≤ u := by linarith [hu.1, Real.pi_pos, hθ0]
  have hu2 : u ≤ π / 2 := hu.2
  simp only [Function.comp_apply, smul_eq_mul, connesArcIntegrand]
  rw [Real.exp_log (by positivity)]
  rw [show 2 * Real.sin u / 2 = Real.sin u by ring, Real.arcsin_sin hu1 hu2]

/-- **Appendix II, the integration by parts.**  `∫_θ^{π/2} u cot u du = -θ log sin θ
- ∫_θ^{π/2} log sin u du`. -/
theorem connes_arcIntegral_ibp {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ π / 2) :
    (∫ u in θ..(π / 2), (Real.cos u / Real.sin u) * u)
      = -(θ * Real.log (Real.sin θ)) - ∫ u in θ..(π / 2), Real.log (Real.sin u) := by
  have hderiv : ∀ u ∈ uIcc θ (π / 2),
      HasDerivAt (fun t : ℝ => t * Real.log (Real.sin t))
        (Real.log (Real.sin u) + (Real.cos u / Real.sin u) * u) u := by
    intro u hu
    have hspos : 0 < Real.sin u := connes_sin_pos_of_mem hθ0 hθ hu
    have hlog : HasDerivAt (fun t : ℝ => Real.log (Real.sin t))
        (Real.cos u / Real.sin u) u := (Real.hasDerivAt_sin u).log (ne_of_gt hspos)
    have hprod : HasDerivAt (fun t : ℝ => t * Real.log (Real.sin t))
        (1 * Real.log (Real.sin u) + u * (Real.cos u / Real.sin u)) u :=
      HasDerivAt.mul (hasDerivAt_id u) hlog
    rw [one_mul] at hprod
    rw [mul_comm (Real.cos u / Real.sin u) u]
    exact hprod
  have hcontlog : ContinuousOn (fun u : ℝ => Real.log (Real.sin u)) (uIcc θ (π / 2)) := by
    refine ContinuousOn.log (by fun_prop) ?_
    intro u hu
    exact ne_of_gt (connes_sin_pos_of_mem hθ0 hθ hu)
  have hcontcot : ContinuousOn (fun u : ℝ => (Real.cos u / Real.sin u) * u)
      (uIcc θ (π / 2)) := by
    refine ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) ?_) (by fun_prop)
    intro u hu
    exact ne_of_gt (connes_sin_pos_of_mem hθ0 hθ hu)
  have hint : IntervalIntegrable
      (fun u : ℝ => Real.log (Real.sin u) + (Real.cos u / Real.sin u) * u) volume θ (π / 2) :=
    (hcontlog.intervalIntegrable).add (hcontcot.intervalIntegrable)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_add hcontlog.intervalIntegrable hcontcot.intervalIntegrable] at hftc
  rw [Real.sin_pi_div_two, Real.log_one, mul_zero] at hftc
  linarith [hftc]

theorem connes_nhdsGT_le_nhdsWithin_uIcc :
    𝓝[>] (0:ℝ) ≤ 𝓝[uIcc (0:ℝ) (π / 2)] 0 := by
  rw [uIcc_of_le (by positivity : (0:ℝ) ≤ π / 2)]
  have h1 : 𝓝[Ioi (0:ℝ)] 0 = 𝓝[Ioi (0:ℝ) ∩ Iio (π / 2)] 0 :=
    nhdsWithin_restrict' _ (Iio_mem_nhds (by positivity : (0:ℝ) < π / 2))
  rw [h1]
  exact nhdsWithin_mono _ (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)

/-- The primitive of `log ∘ sin` is continuous at the origin. -/
theorem connes_logSin_primitive_tendsto :
    Tendsto (fun θ : ℝ => ∫ u in (0:ℝ)..θ, Real.log (Real.sin u)) (𝓝[>] 0) (𝓝 0) := by
  have hint : IntegrableOn (fun u : ℝ => Real.log (Real.sin u)) (uIcc (0:ℝ) (π / 2)) := by
    rw [uIcc_of_le (by positivity : (0:ℝ) ≤ π / 2)]
    have h := (intervalIntegrable_log_sin (a := (0:ℝ)) (b := π / 2))
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity : (0:ℝ) ≤ π / 2)] at h
    exact h
  have hc := intervalIntegral.continuousOn_primitive_interval hint
  have h0 : (0:ℝ) ∈ uIcc (0:ℝ) (π / 2) := by
    rw [uIcc_of_le (by positivity : (0:ℝ) ≤ π / 2)]
    exact ⟨le_refl 0, by positivity⟩
  have hcw := hc 0 h0
  have hzero : (∫ u in (0:ℝ)..(0:ℝ), Real.log (Real.sin u)) = 0 :=
    intervalIntegral.integral_same
  rw [ContinuousWithinAt, hzero] at hcw
  exact hcw.mono_left connes_nhdsGT_le_nhdsWithin_uIcc

theorem connes_logSin_integral_tendsto :
    Tendsto (fun θ : ℝ => ∫ u in θ..(π / 2), Real.log (Real.sin u)) (𝓝[>] 0)
      (𝓝 (-Real.log 2 * π / 2)) := by
  have hsplit : ∀ θ : ℝ, (∫ u in θ..(π / 2), Real.log (Real.sin u))
      = (∫ u in (0:ℝ)..(π / 2), Real.log (Real.sin u))
        - ∫ u in (0:ℝ)..θ, Real.log (Real.sin u) := by
    intro θ
    have h := intervalIntegral.integral_add_adjacent_intervals
      (a := (0:ℝ)) (b := θ) (c := π / 2)
      (f := fun u : ℝ => Real.log (Real.sin u))
      (intervalIntegrable_log_sin) (intervalIntegrable_log_sin)
    linarith [h]
  have hlim : Tendsto (fun θ : ℝ => (∫ u in (0:ℝ)..(π / 2), Real.log (Real.sin u))
      - ∫ u in (0:ℝ)..θ, Real.log (Real.sin u)) (𝓝[>] 0)
      (𝓝 ((∫ u in (0:ℝ)..(π / 2), Real.log (Real.sin u)) - 0)) :=
    tendsto_const_nhds.sub connes_logSin_primitive_tendsto
  rw [sub_zero] at hlim
  have hgoal := hlim.congr (fun θ => (hsplit θ).symm)
  rwa [integral_log_sin_zero_pi_div_two] at hgoal

/-- **Appendix II (53).**  The complementary area tends to `(π/2) log 2`. -/
theorem connes_arcIntegral_theta_tendsto :
    Tendsto (fun θ : ℝ => ∫ x in (Real.log (2 * Real.sin θ))..(Real.log 2), connesArcIntegrand x)
      (𝓝[>] 0) (𝓝 (π / 2 * Real.log 2)) := by
  have hlim : Tendsto (fun θ : ℝ =>
      -(θ * Real.log (Real.sin θ)) - ∫ u in θ..(π / 2), Real.log (Real.sin u))
      (𝓝[>] 0) (𝓝 (-0 - (-Real.log 2 * π / 2))) :=
    (connes_theta_mul_log_sin_tendsto.neg).sub connes_logSin_integral_tendsto
  have hval : (-0 : ℝ) - (-Real.log 2 * π / 2) = π / 2 * Real.log 2 := by ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (by positivity : (0:ℝ) < π / 2))] with θ hθ0 hθ
  have hθ0' : (0:ℝ) < θ := hθ0
  have hθ' : θ ≤ π / 2 := le_of_lt hθ
  rw [connes_arcIntegral_substitution hθ0' hθ', connes_arcIntegral_ibp hθ0' hθ']

theorem connes_arcsin_exp_tendsto :
    Tendsto (fun a : ℝ => Real.arcsin (Real.exp a / 2)) atBot (𝓝[>] 0) := by
  have hexp : Tendsto (fun a : ℝ => Real.exp a / 2) atBot (𝓝 0) := by
    have := Real.tendsto_exp_atBot
    simpa using this.div_const 2
  have hcont : Tendsto (fun t : ℝ => Real.arcsin t) (𝓝 0) (𝓝 0) := by
    have := Real.continuous_arcsin.tendsto (0:ℝ)
    rwa [Real.arcsin_zero] at this
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hcont.comp hexp) ?_
  filter_upwards with a
  refine Real.arcsin_pos.mpr ?_
  positivity

/-- **Appendix II (51)-(53), the complementary area.** -/
theorem connes_arcIntegral_tendsto_atBot :
    Tendsto (fun a : ℝ => ∫ x in a..(Real.log 2), connesArcIntegrand x) atBot
      (𝓝 (π / 2 * Real.log 2)) := by
  have hcomp := connes_arcIntegral_theta_tendsto.comp connes_arcsin_exp_tendsto
  refine hcomp.congr' ?_
  filter_upwards [eventually_le_atBot (Real.log 2)] with a ha
  have hle : Real.exp a / 2 ≤ 1 := by
    have : Real.exp a ≤ 2 := by
      have h2 : Real.exp a ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr ha
      rwa [Real.exp_log (by norm_num)] at h2
    linarith
  have hnn : (0:ℝ) ≤ Real.exp a / 2 := by positivity
  have hsin : Real.sin (Real.arcsin (Real.exp a / 2)) = Real.exp a / 2 :=
    Real.sin_arcsin (by linarith) hle
  simp only [Function.comp_apply, hsin]
  rw [show 2 * (Real.exp a / 2) = Real.exp a by ring, Real.log_exp]

/-- **Appendix II (49)-(53).**  `j(ε) = 2π log(1/ε) + o(1)`: with `a = log ε`, the area
`j = 4 ∫_{log ε}^{log 2} arccos(e^x/2) dx` differs from `2π log(1/ε)` by a quantity tending to
zero.  The excess is exactly the limiting area `2π log 2` of `R_ε ∖ D`, computed in (53) by the
log-sine integral. -/
theorem connes_j_asymptotics :
    Tendsto (fun a : ℝ => 4 * (∫ x in a..(Real.log 2), Real.arccos (Real.exp x / 2))
        - 2 * π * (-a)) atBot (𝓝 0) := by
  have hlim : Tendsto (fun a : ℝ => 2 * π * Real.log 2
      - 4 * (∫ x in a..(Real.log 2), connesArcIntegrand x)) atBot
      (𝓝 (2 * π * Real.log 2 - 4 * (π / 2 * Real.log 2))) :=
    tendsto_const_nhds.sub (connes_arcIntegral_tendsto_atBot.const_mul 4)
  have hval : 2 * π * Real.log 2 - 4 * (π / 2 * Real.log 2) = 0 := by ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards with a
  have h := connes_arccos_add_arcsin_integral a
  linarith [h]

end

end GaloisForLFunctions.RHTower
