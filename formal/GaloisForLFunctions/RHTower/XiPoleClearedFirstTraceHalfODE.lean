import GaloisForLFunctions.RHTower.XiPoleClearedFirstTraceRootReduction

/-!
# Singular first-trace half ODE

Let `E₁` be the pole-cleared valuation-one continuation isolated from Xi.  An analytic square root
of `E₁` satisfies the singular linear equation

`2 E₁ e' = E₁' e`.

Conversely, one analytic solution anchored to the fixed Euler branch at `s = 2` squares to `E₁`.
Indeed, near `2` the quotient `e² / E₁` is defined and has zero derivative; its anchored value is
one.  The identity theorem then propagates `e² = E₁` through the full strict right half-plane,
including its zeros.  This gives a divisor-free, coefficient-explicit form of the exact first-rung
obligation.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- Existence of a globally analytic solution to the pole-cleared first-trace half equation,
oriented by the fixed Euler branch at `s = 2`. -/
def PoleClearedFirstTraceHalfODESolvable : Prop :=
  ∃ e : ℂ → ℂ,
    AnalyticOnNhd ℂ e rightHalf ∧
      e 2 = poleClearedPrimeZetaHalfEulerGerm 2 ∧
      ∀ s ∈ rightHalf,
        2 * poleClearedFirstTraceExponentialContinuation s * deriv e s =
          deriv poleClearedFirstTraceExponentialContinuation s * e s

/-- A square root of the valuation-one continuation satisfies its singular half ODE. -/
theorem poleClearedFirstTraceHalfODE_of_sqrt
    {e : ℂ → ℂ} (he : AnalyticOnNhd ℂ e rightHalf)
    (hesq : ∀ s ∈ rightHalf,
      e s ^ (2 : ℕ) = poleClearedFirstTraceExponentialContinuation s) :
    ∀ s ∈ rightHalf,
      2 * poleClearedFirstTraceExponentialContinuation s * deriv e s =
        deriv poleClearedFirstTraceExponentialContinuation s * e s := by
  intro s hs
  have heq : (fun z : ℂ => e z ^ (2 : ℕ)) =ᶠ[𝓝 s]
      poleClearedFirstTraceExponentialContinuation := by
    filter_upwards [isOpen_rightHalf.mem_nhds hs] with z hz
    exact hesq z hz
  have hderiv : deriv (fun z : ℂ => e z ^ (2 : ℕ)) s =
      deriv poleClearedFirstTraceExponentialContinuation s := heq.deriv_eq
  have he' : HasDerivAt e (deriv e s) s :=
    (he s hs).differentiableAt.hasDerivAt
  have hfun : (fun z : ℂ => e z ^ (2 : ℕ)) = e ^ (2 : ℕ) := by
    funext z
    rfl
  have hpow : deriv (fun z : ℂ => e z ^ (2 : ℕ)) s = 2 * e s * deriv e s := by
    rw [hfun]
    simpa [mul_assoc] using (he'.pow 2).deriv
  rw [hpow] at hderiv
  rw [← hesq s hs]
  linear_combination e s * hderiv

/-- An anchored analytic solution of the singular half ODE squares to the valuation-one field on
the full right half-plane. -/
theorem poleClearedFirstTrace_sqrt_of_halfODE
    {e : ℂ → ℂ} (he : AnalyticOnNhd ℂ e rightHalf)
    (hanchor : e 2 = poleClearedPrimeZetaHalfEulerGerm 2)
    (hODE : ∀ s ∈ rightHalf,
      2 * poleClearedFirstTraceExponentialContinuation s * deriv e s =
        deriv poleClearedFirstTraceExponentialContinuation s * e s) :
    ∀ s ∈ rightHalf,
      e s ^ (2 : ℕ) = poleClearedFirstTraceExponentialContinuation s := by
  let E : ℂ → ℂ := poleClearedFirstTraceExponentialContinuation
  let q : ℂ → ℂ := fun s => e s ^ (2 : ℕ) / E s
  have htwoRH : (2 : ℂ) ∈ rightHalf := farHalf_subset_rightHalf two_mem_farHalf
  have hEan : AnalyticOnNhd ℂ E rightHalf :=
    analyticOnNhd_poleClearedFirstTraceExponentialContinuation_rightHalf
  have hE2 : E 2 ≠ 0 := by
    rw [show E 2 = poleClearedPrimeZetaHalfEulerGerm 2 ^ (2 : ℕ) by
      exact (poleClearedPrimeZetaHalfEulerGerm_sq two_mem_farHalf).symm]
    exact pow_ne_zero 2 (poleClearedPrimeZetaHalfEulerGerm_ne_zero 2)
  have hEne : {s : ℂ | E s ≠ 0} ∈ 𝓝 (2 : ℂ) :=
    (hEan 2 htwoRH).continuousAt.tendsto.eventually_ne hE2
  have hlocal : rightHalf ∩ {s : ℂ | E s ≠ 0} ∈ 𝓝 (2 : ℂ) :=
    inter_mem (isOpen_rightHalf.mem_nhds htwoRH) hEne
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hlocal
  have hballRH : Metric.ball (2 : ℂ) r ⊆ rightHalf := fun z hz => (hrsub hz).1
  have hballE : ∀ z ∈ Metric.ball (2 : ℂ) r, E z ≠ 0 :=
    fun z hz => (hrsub hz).2
  have hqdiff : DifferentiableOn ℂ q (Metric.ball (2 : ℂ) r) := by
    intro z hz
    have hez := (he z (hballRH hz)).differentiableAt
    have hEz := (hEan z (hballRH hz)).differentiableAt
    exact (hez.pow 2).div hEz (hballE z hz) |>.differentiableWithinAt
  have hqderiv : EqOn (deriv q) 0 (Metric.ball (2 : ℂ) r) := by
    intro z hz
    have hez : HasDerivAt e (deriv e z) z :=
      (he z (hballRH hz)).differentiableAt.hasDerivAt
    have hEz : HasDerivAt E (deriv E z) z :=
      (hEan z (hballRH hz)).differentiableAt.hasDerivAt
    have hquot := (hez.pow 2).div hEz (hballE z hz)
    have hode := hODE z (hballRH hz)
    change deriv (e ^ (2 : ℕ) / E) z = 0
    rw [hquot.deriv]
    dsimp only [E] at hode ⊢
    apply div_eq_zero_iff.mpr
    left
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply]
    linear_combination e z * hode
  have hqconst : ∀ z ∈ Metric.ball (2 : ℂ) r, q z = q 2 := by
    intro z hz
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero
      (Metric.isConnected_ball hr).isPreconnected hqdiff hqderiv hz
      (Metric.mem_ball_self hr)
  have hq2 : q 2 = 1 := by
    change e 2 ^ (2 : ℕ) / E 2 = 1
    rw [hanchor, show E 2 = poleClearedFirstTraceExponentialContinuation 2 by rfl,
      ← poleClearedPrimeZetaHalfEulerGerm_sq two_mem_farHalf]
    exact div_self (pow_ne_zero 2 (poleClearedPrimeZetaHalfEulerGerm_ne_zero 2))
  have heqBall : EqOn (fun z : ℂ => e z ^ (2 : ℕ)) E (Metric.ball (2 : ℂ) r) := by
    intro z hz
    have hqz : q z = 1 := (hqconst z hz).trans hq2
    dsimp only [q] at hqz
    exact (div_eq_one_iff_eq (hballE z hz)).mp hqz
  have hevent : (fun z : ℂ => e z ^ (2 : ℕ)) =ᶠ[𝓝 (2 : ℂ)] E :=
    by
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with z hz
      exact heqBall hz
  have hsqAn : AnalyticOnNhd ℂ (fun z : ℂ => e z ^ (2 : ℕ)) rightHalf := he.pow 2
  have hEqOn : EqOn (fun z : ℂ => e z ^ (2 : ℕ)) E rightHalf :=
    hsqAn.eqOn_of_preconnected_of_eventuallyEq hEan
      convex_rightHalf.isPreconnected htwoRH hevent
  exact hEqOn

/-- Exact ODE form of the first multiplicity-parity rung. -/
theorem rhLadder_one_iff_poleClearedFirstTraceHalfODESolvable :
    RHLadder 1 ↔ PoleClearedFirstTraceHalfODESolvable := by
  rw [rhLadder_one_iff_poleClearedPrimeZetaHalfEulerGerm_extends]
  constructor
  · rintro ⟨e, he, hesq, hmatch⟩
    exact ⟨e, he, hmatch two_mem_farHalf,
      poleClearedFirstTraceHalfODE_of_sqrt he hesq⟩
  · rintro ⟨e, he, hanchor, hODE⟩
    have hesq := poleClearedFirstTrace_sqrt_of_halfODE he hanchor hODE
    refine ⟨e, he, hesq, ?_⟩
    exact Bottcher.eqOn_of_pow_eq_of_isPreconnected (N := 2) (by norm_num)
      convex_farHalf.isPreconnected
      (he.continuousOn.mono farHalf_subset_rightHalf)
      analyticOnNhd_poleClearedPrimeZetaHalfEulerGerm_farHalf.continuousOn
      (fun s _ => poleClearedPrimeZetaHalfEulerGerm_ne_zero s)
      (fun s hs => by rw [hesq s (farHalf_subset_rightHalf hs),
        poleClearedPrimeZetaHalfEulerGerm_sq hs])
      two_mem_farHalf hanchor

end

end RHTower
