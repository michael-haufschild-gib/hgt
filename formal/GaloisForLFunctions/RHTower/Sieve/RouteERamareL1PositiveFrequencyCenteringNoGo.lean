import GaloisForLFunctions.RHTower.Sieve.RouteERamareSourceFaithfulFiniteCenteringNoGo
import GaloisForLFunctions.RHTower.CoefficientHardyLSeries
import GaloisForLFunctions.Bottcher.SchwarzReflection
import GaloisForLFunctions.RHTower.Sieve.PrimeBlockTwistBound
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Route E: regular-infinite positive-frequency centering is impossible

Finite source-faithful centering was already classified and killed. This module kills its regular
infinite survivor. If the compensation is absolutely summable and uses only the one-sided positive
natural logarithmic spectrum, interval vanishing gives a continuous ordinary Dirichlet series on
the closed right half-plane. Zero extension across its boundary interval is holomorphic by Morera,
so the identity theorem and Dirichlet coefficient extraction force coefficientwise cancellation.
That contradicts source faithfulness on every nonempty squarefree Ramaré packet.

The exact remaining centering mechanisms are therefore source-overlapping cancellation,
non-`ℓ¹`/singular compensation, or a two-sided spectrum. No finite or regular-infinite
source-disjoint positive-frequency centering remains.
-/

open Complex Set Filter Topology LSeries
open GaloisForLFunctions

namespace RHTower.Sieve

open scoped ArithmeticFunction.Moebius

noncomputable section

private theorem continuousOn_LSeries_closedRight_of_summable
    {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖) :
    ContinuousOn (LSeries a) {z : ℂ | 0 ≤ z.re} := by
  refine continuousOn_tsum (u := fun n => ‖a n‖) (fun n => ?_) ha (fun n z hz => ?_)
  · rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
      exact continuousOn_const
    · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp only [LSeries.term_of_ne_zero hn.ne']
      exact (continuous_const.div
        (Continuous.const_cpow continuous_id (Or.inl hn0))
        (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hn0))).continuousOn
  · rcases n.eq_zero_or_pos with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn.ne', norm_div,
        Complex.norm_natCast_cpow_of_pos hn]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hpow : 1 ≤ (n : ℝ) ^ z.re := Real.one_le_rpow hn1 hz
      exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hpow)).mpr
        (by simpa using mul_le_mul_of_nonneg_left hpow (norm_nonneg (a n)))

private theorem LSeriesSummable_zero_of_summable
    {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖) :
    LSeriesSummable a 0 := by
  change Summable (LSeries.term a 0)
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ ha
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [LSeries.term_zero]
  · simp [LSeries.term_of_ne_zero hn.ne']

/-- An absolutely summable ordinary Dirichlet series whose continuous boundary values vanish on
an imaginary-axis interval has every coefficient zero, including the explicitly normalized index
zero. -/
theorem LSeries_coeff_eq_zero_of_l1_boundary_interval
    {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖) (ha0 : a 0 = 0)
    {y₀ r : ℝ} (hr : 0 < r)
    (hzero : ∀ y : ℝ, |y - y₀| < r → LSeries a ((y : ℂ) * I) = 0) :
    ∀ n : ℕ, a n = 0 := by
  classical
  let R : Set ℂ := {z : ℂ | 0 ≤ z.re}
  let U : Set ℂ := Metric.ball ((y₀ : ℂ) * I) r
  let G : ℂ → ℂ := R.piecewise (LSeries a) 0
  have hRclosed : IsClosed R := by
    simpa only [R] using isClosed_le continuous_const continuous_re
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hFcont : ContinuousOn (LSeries a) R :=
    continuousOn_LSeries_closedRight_of_summable ha
  have hGcont : ContinuousOn G U := by
    apply ContinuousOn.piecewise
    · intro z hz
      have hzre : z.re = 0 :=
        (frontier_le_subset_eq continuous_const continuous_re hz.2).symm
      have hdist : ‖z - (y₀ : ℂ) * I‖ < r := by
        simpa [U, Metric.mem_ball, Complex.dist_eq] using hz.1
      have him : |z.im - y₀| < r := by
        calc
          |z.im - y₀| = |(z - (y₀ : ℂ) * I).im| := by simp
          _ ≤ ‖z - (y₀ : ℂ) * I‖ := Complex.abs_im_le_norm _
          _ < r := hdist
      have hzform : z = (z.im : ℂ) * I := by
        apply Complex.ext
        · simp [hzre]
        · simp
      rw [hzform]
      exact hzero z.im him
    · exact hFcont.mono (fun z hz => by
        have hzcl : z ∈ closure R := hz.2
        simpa [hRclosed.closure_eq] using hzcl)
    · exact continuousOn_const
  have hFsum0 : LSeriesSummable a 0 := LSeriesSummable_zero_of_summable ha
  have hFdiff : DifferentiableOn ℂ (LSeries a) {z : ℂ | 0 < z.re} :=
    RHTower.differentiableOn_LSeries_rightHalf_of_summable hFsum0
  have hGoff : DifferentiableOn ℂ G
      (U ∩ {z : ℂ | (I * z + 0).im ≠ 0}) := by
    intro z hz
    have hzre : z.re ≠ 0 := by simpa [Complex.mul_im] using hz.2
    by_cases hpos : 0 < z.re
    · have hFat : DifferentiableAt ℂ (LSeries a) z :=
        (hFdiff z hpos).differentiableAt
          ((isOpen_lt continuous_const continuous_re).mem_nhds hpos)
      apply (hFat.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hpos] with w hw
      simp [G, R, hw.le]
    · have hneg : z.re < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hzre
      have hzeroAt : DifferentiableAt ℂ (fun _ : ℂ => (0 : ℂ)) z := differentiableAt_const 0
      apply (hzeroAt.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds hneg] with w hw
      simp [G, R, not_le.mpr hw]
  have hGdiff : DifferentiableOn ℂ G U :=
    Bottcher.differentiableOn_of_off_line (c := I) (d := 0) (a := 0)
      Complex.I_ne_zero hUopen hGcont hGoff
  have hGan : AnalyticOnNhd ℂ G U := hGdiff.analyticOnNhd hUopen
  let zL : ℂ := (y₀ : ℂ) * I - (r / 2 : ℝ)
  have hzLU : zL ∈ U := by
    simp only [U, Metric.mem_ball, Complex.dist_eq]
    simp only [zL]
    have hnorm : ‖((r / 2 : ℝ) : ℂ)‖ = r / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [show (y₀ : ℂ) * I - (r / 2 : ℝ) - (y₀ : ℂ) * I = -((r / 2 : ℝ) : ℂ) by ring,
      norm_neg, hnorm]
    linarith
  have hzLneg : zL.re < 0 := by simp [zL]; linarith
  have hseedG : G =ᶠ[𝓝 zL] 0 := by
    filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds hzLneg] with z hz
    simp [G, R, not_le.mpr hz]
  have hzeroAn : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) U := fun _ _ => analyticAt_const
  have hGeq : Set.EqOn G 0 U :=
    hGan.eqOn_of_preconnected_of_eventuallyEq hzeroAn
      (convex_ball ((y₀ : ℂ) * I) r).isPreconnected hzLU hseedG
  let zR : ℂ := (y₀ : ℂ) * I + (r / 2 : ℝ)
  have hzRU : zR ∈ U := by
    simp only [U, Metric.mem_ball, Complex.dist_eq]
    simp only [zR]
    have hnorm : ‖((r / 2 : ℝ) : ℂ)‖ = r / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [show (y₀ : ℂ) * I + (r / 2 : ℝ) - (y₀ : ℂ) * I = ((r / 2 : ℝ) : ℂ) by ring,
      hnorm]
    linarith
  have hzRpos : 0 < zR.re := by simp [zR]; linarith
  have hseedF : LSeries a =ᶠ[𝓝 zR] 0 := by
    filter_upwards [hUopen.mem_nhds hzRU,
      (isOpen_lt continuous_const continuous_re).mem_nhds hzRpos] with z hzU hzpos
    have h := hGeq hzU
    simpa [G, R, hzpos.le] using h
  let V : Set ℂ := {z : ℂ | 0 < z.re}
  have hVopen : IsOpen V := by simpa [V] using isOpen_lt continuous_const continuous_re
  have hFan : AnalyticOnNhd ℂ (LSeries a) V := by
    simpa [V] using hFdiff.analyticOnNhd hVopen
  have hFeq : Set.EqOn (LSeries a) 0 V :=
    hFan.eqOn_of_preconnected_of_eventuallyEq (fun _ _ => analyticAt_const)
      (convex_halfSpace_re_gt 0).isPreconnected hzRpos hseedF
  have hzeroRay : (fun x : ℝ => LSeries a (x : ℂ)) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact hFeq hx
  have habs : LSeries.abscissaOfAbsConv a < ⊤ :=
    (hFsum0.abscissaOfAbsConv_le).trans_lt (by simp)
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      rcases n with _ | k
      · exact ha0
      · have hprefix : ∀ m ≤ k, a m = 0 := fun m hm => ih m (Nat.lt_succ_of_le hm)
        have ht := LSeries.tendsto_cpow_mul_atTop hprefix habs
        have hscaledZero :
            (fun x : ℝ => ((k : ℂ) + 1) ^ (x : ℂ) * LSeries a (x : ℂ)) =ᶠ[atTop] 0 := by
          filter_upwards [hzeroRay] with x hx
          simp [hx]
        have ht0 : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 (a (k + 1))) :=
          ht.congr' hscaledZero
        have hz : (0 : ℂ) = a (k + 1) := by
          simpa only [tendsto_const_nhds_iff] using ht0
        exact hz.symm

/-- Literal Ramaré source plus an infinite compensation on positive natural log-frequencies. -/
def routeERamareLOneCenteringCoefficient
    (P : Finset ℕ) (M : ℕ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  (if n ∈ ramareSquarefreeActiveSet P M then ((μ n : ℤ) : ℂ) else 0) + b n

@[simp] theorem routeERamareLOneCenteringCoefficient_zero
    (P : Finset ℕ) (M : ℕ) {b : ℕ → ℂ} (hb0 : b 0 = 0) :
    routeERamareLOneCenteringCoefficient P M b 0 = 0 := by
  simp [routeERamareLOneCenteringCoefficient, ramareSquarefreeActiveSet,
    ramareActiveSet, hb0]

theorem summable_norm_routeERamareLOneCenteringCoefficient
    (P : Finset ℕ) (M : ℕ) {b : ℕ → ℂ}
    (hb : Summable fun n => ‖b n‖) :
    Summable fun n => ‖routeERamareLOneCenteringCoefficient P M b n‖ := by
  let source : ℕ → ℂ := fun n =>
    if n ∈ ramareSquarefreeActiveSet P M then ((μ n : ℤ) : ℂ) else 0
  have hsource : Summable source := by
    apply summable_of_ne_finset_zero (s := ramareSquarefreeActiveSet P M)
    intro n hn
    simp [source, hn]
  have htotal : Summable fun n => source n + b n := hsource.add hb.of_norm
  simpa only [source, routeERamareLOneCenteringCoefficient] using htotal.norm

/-- Boundary value of the ordinary Dirichlet series of a literal Ramaré source plus compensation.
The argument `-2πit` makes every positive index carry exactly `unitLogPhase t n`. -/
def routeERamareLOneCenteringBoundary
    (P : Finset ℕ) (M : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  LSeries (routeERamareLOneCenteringCoefficient P M b)
    (-(((2 * Real.pi * t : ℝ) : ℂ) * I))

/-- Exact source-facing expansion: the boundary carrier is the absolutely convergent positive
natural log-frequency series. -/
theorem routeERamareLOneCenteringBoundary_eq_tsum
    (P : Finset ℕ) (M : ℕ) {b : ℕ → ℂ}
    (hb : Summable fun n => ‖b n‖) (hb0 : b 0 = 0) (t : ℝ) :
    routeERamareLOneCenteringBoundary P M b t =
      ∑' k : ℕ, routeERamareLOneCenteringCoefficient P M b (k + 1) *
        unitLogPhase t (k + 1) := by
  let a := routeERamareLOneCenteringCoefficient P M b
  have ha : Summable fun n => ‖a n‖ :=
    summable_norm_routeERamareLOneCenteringCoefficient P M hb
  have ha0 : a 0 = 0 := routeERamareLOneCenteringCoefficient_zero P M hb0
  have hs : LSeriesSummable a (-(((2 * Real.pi * t : ℝ) : ℂ) * I)) := by
    change Summable (LSeries.term a (-(((2 * Real.pi * t : ℝ) : ℂ) * I)))
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ ha
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn.ne', norm_div,
        Complex.norm_natCast_cpow_of_pos hn]
      simp
  have hshift := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, LSeries.term_zero, zero_add] at hshift
  rw [routeERamareLOneCenteringBoundary, LSeries, ← hshift]
  apply tsum_congr
  intro k
  rw [LSeries.term_def₀ ha0, unitLogPhase_eq_cpow (Nat.succ_pos k) t]
  congr 1
  simp

/-- **Route E regular-infinite centering no-go.** A nonempty literal squarefree Ramaré packet cannot
be centered on a nondegenerate interval by any source-disjoint absolutely summable compensation on
the one-sided positive-natural logarithmic spectrum. -/
theorem not_routeERamare_sourceFaithfulLOnePositiveFrequencyCentering
    (P : Finset ℕ) (M : ℕ)
    (hactive : (ramareSquarefreeActiveSet P M).Nonempty) :
    ¬ ∃ (b : ℕ → ℂ) (t₀ r : ℝ),
      Summable (fun n => ‖b n‖) ∧ b 0 = 0 ∧ 0 < r ∧
      (∀ n ∈ ramareSquarefreeActiveSet P M, b n = 0) ∧
      ∀ t : ℝ, |t - t₀| < r → routeERamareLOneCenteringBoundary P M b t = 0 := by
  rintro ⟨b, t₀, r, hb, hb0, hr, hfaithful, hboundary⟩
  let a := routeERamareLOneCenteringCoefficient P M b
  have ha : Summable fun n => ‖a n‖ :=
    summable_norm_routeERamareLOneCenteringCoefficient P M hb
  have ha0 : a 0 = 0 := routeERamareLOneCenteringCoefficient_zero P M hb0
  have hpi : 0 < 2 * Real.pi := by positivity
  have hzeroY : ∀ y : ℝ, |y - (-(2 * Real.pi * t₀))| < 2 * Real.pi * r →
      LSeries a ((y : ℂ) * I) = 0 := by
    intro y hy
    let t : ℝ := -y / (2 * Real.pi)
    have hden : 2 * Real.pi ≠ 0 := hpi.ne'
    have heq : t - t₀ = -(y + 2 * Real.pi * t₀) / (2 * Real.pi) := by
      dsimp only [t]
      field_simp
      ring
    have hy' : |y + 2 * Real.pi * t₀| < 2 * Real.pi * r := by
      simpa only [sub_neg_eq_add] using hy
    have ht : |t - t₀| < r := by
      rw [heq, abs_div, abs_neg, abs_of_pos hpi, div_lt_iff₀ hpi]
      simpa [mul_comm] using hy'
    have hz := hboundary t ht
    have harg : ((y : ℂ) * I) = -(((2 * Real.pi * t : ℝ) : ℂ) * I) := by
      dsimp only [t]
      push_cast
      field_simp
    rw [harg]
    exact hz
  have hall := LSeries_coeff_eq_zero_of_l1_boundary_interval ha ha0
    (y₀ := -(2 * Real.pi * t₀)) (r := 2 * Real.pi * r) (mul_pos hpi hr) hzeroY
  obtain ⟨n, hn⟩ := hactive
  have hnzero := hall n
  dsimp only [a] at hnzero
  rw [routeERamareLOneCenteringCoefficient, if_pos hn, hfaithful n hn] at hnzero
  simp only [add_zero] at hnzero
  have hsf : Squarefree n := (Finset.mem_filter.mp hn).2
  have hmul := moebius_real_mul_self_eq_one_of_squarefree hsf
  have hmu0 : (((μ n : ℤ) : ℝ)) = 0 := by exact_mod_cast hnzero
  rw [hmu0] at hmul
  norm_num at hmul

end

end RHTower.Sieve
