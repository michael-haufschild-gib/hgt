import GaloisForLFunctions.RHTower.ExponentialTypeNotSummableOnPrimeLogs
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Prime-log divergence of entire functions of exponential type at the natural rate

Let `Φ ≢ 0` be entire with `‖Φ ξ‖ ≤ C e^{ρ‖ξ‖}` and let `0 ≤ σ`.  Then the partial sums
`Σ_{p<N} p^{−σ} ‖Φ(log p)‖` over the primes are unbounded as soon as `ρ < 1 − σ` and `2ρ < 5/12`
(`exists_primeLogWeightedSum_gt_of_lt_one_sub`).  This replaces the constraint `3ρ < 1 − σ` of
`exists_primeLogWeightedSum_gt` by the natural one — the disc `|z − σ| < ρ` lies in `Re z < 1` —
up to the cap `ρ < 5/24` inherited from the exponent `7/12` of the short-interval prime theorem.

The gain comes from replacing the pointwise largeness `‖Φ x‖ ≥ e^{−(ρ+δ)x}` at a single point by
the largeness of the unit-window integral `∫_0^1 ‖Φ(x+t)‖ dt ≥ e^{−(ρ+δ)x}`.

* **Window two-ray theorem** (`eq_zero_of_two_ray_window_integral_decay`): an entire function of
  exponential type that decays exponentially on the negative ray and whose unit-window integrals
  decay exponentially on the positive ray vanishes.  Its unit-window average
  `F(w) = ∫_0^1 g(w+t) dt` is entire with the same two-ray decay, so `F ≡ 0` by the Paley–Wiener
  two-ray theorem; then `F' = g(·+1) − g ≡ 0` makes `g` periodic, the decay on the negative ray
  forces `g = 0` on `ℝ`, and the identity theorem finishes.
* **Window largeness** (`exists_window_integral_ge_of_exponentialType`): applied to
  `Φ(w) e^{(ρ+δ/2)w}` this gives `∫_0^1 ‖Φ(x+t)‖ dt ≥ e^{−(ρ+δ)} e^{−(ρ+δ)x}` at arbitrarily
  large `x`.
* **Riemann sum over prime windows**: cut `[x, x+1]` into `N` windows of length `h ≍ y^{−γ}`,
  `y = e^x`, `γ = 2ρ + 2δ < 5/12`.  The Lipschitz bound `‖Φ'‖ ≤ C e^{ρ(x+3)}` compares the window
  integral with the lower Riemann sum up to an error `≤ ½ e^{−(ρ+δ)x}`
  (`integral_le_sum_window_values_add`); every window carries Chebyshev mass `≥ yh/4` by the `7/12`
  theorem; summing the window bounds of `window_sum_ge_theta_window` gives a prime sum over
  `(y, ey]` of size `≥ c y^{1−σ−ρ−δ} / log(ey)`, which is unbounded.
-/

open Complex Filter Topology Set Finset Metric MeasureTheory
open scoped Real

noncomputable section

namespace RHTower

/-! ## The unit-window average of an entire function -/

/-- The unit-window average `∫_0^1 g(w + t) dt` of a function on `ℂ`. -/
def unitWindowAverage (g : ℂ → ℂ) (w : ℂ) : ℂ := ∫ t in (0 : ℝ)..1, g (w + t)

/-- For entire `g`, the unit-window average is entire, with derivative `g(w+1) − g(w)`:
differentiation under the integral sign and the fundamental theorem of calculus. -/
theorem hasDerivAt_unitWindowAverage {g : ℂ → ℂ} (hg : Differentiable ℂ g) (w : ℂ) :
    HasDerivAt (unitWindowAverage g) (g (w + 1) - g w) w := by
  have hgc : Continuous g := hg.continuous
  have hg'c : Continuous (deriv g) := (hg.contDiff (n := 1)).continuous_deriv le_rfl
  have hcont : ∀ x : ℂ, Continuous fun t : ℝ => g (x + t) := fun x =>
    hgc.comp (continuous_const.add continuous_ofReal)
  have hcont' : Continuous fun t : ℝ => deriv g (w + t) :=
    hg'c.comp (continuous_const.add continuous_ofReal)
  -- a bound for `g'` on the closed ball of radius `2` about `w`
  obtain ⟨B, hB⟩ := (isCompact_closedBall w 2).exists_bound_of_continuousOn hg'c.continuousOn
  have hderiv := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1) (F := fun x t => g (x + t))
    (F' := fun x t => deriv g (x + t)) (x₀ := w) (s := ball w 1) (bound := fun _ => B)
    (ball_mem_nhds w one_pos)
    (Eventually.of_forall fun x => (hcont x).aestronglyMeasurable)
    ((hcont w).intervalIntegrable 0 1) hcont'.aestronglyMeasurable
    (Eventually.of_forall fun t ht x hx => hB _ ?_) intervalIntegrable_const
    (Eventually.of_forall fun t _ x _ => (hg (x + t)).hasDerivAt.comp_add_const x (t : ℂ))
  · -- the derivative integral is `g(w+1) − g(w)` by the fundamental theorem of calculus
    have hint : ∫ t in (0 : ℝ)..1, deriv g (w + t) = g (w + 1) - g w := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => g (w + t))
        (f' := fun t : ℝ => deriv g (w + t)) (a := 0) (b := 1)
        (fun t _ => ((hg (w + t)).hasDerivAt.comp_const_add w (t : ℂ)).comp_ofReal)
        (hcont'.intervalIntegrable 0 1)
      simpa using h
    exact hint ▸ hderiv.2
  · -- `x + t` stays in the closed ball of radius `2`
    rw [Set.uIoc_of_le zero_le_one] at ht
    rw [mem_ball, dist_eq_norm] at hx
    rw [mem_closedBall, dist_eq_norm]
    calc ‖x + t - w‖ = ‖(x - w) + (t : ℂ)‖ := by ring_nf
      _ ≤ ‖x - w‖ + ‖(t : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + 1 := by
          gcongr
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
          exact ht.2
      _ = 2 := by norm_num

/-- A uniform bound on the window bounds the window average. -/
theorem norm_unitWindowAverage_le {g : ℂ → ℂ} {w : ℂ} {B : ℝ}
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖g (w + t)‖ ≤ B) : ‖unitWindowAverage g w‖ ≤ B := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => g (w + t)) (C := B)
    (fun t ht => hB t (Set.Ioc_subset_Icc_self ((Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)) ▸ ht)))
  simpa [unitWindowAverage] using h

/-! ## The window two-ray theorem -/

/-- An entire function vanishing on the real axis vanishes identically. -/
theorem eq_zero_of_forall_ofReal_eq_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hreal : ∀ x : ℝ, g x = 0) : g = 0 := by
  have hAnal : AnalyticOnNhd ℂ g Set.univ := hg.differentiableOn.analyticOnNhd isOpen_univ
  have hseq : Tendsto (fun n : ℕ => (((1 / (n + 1) : ℝ)) : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h1 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h0
      rw [show ((0 : ℂ)) = ((0 : ℝ) : ℂ) from by norm_num]
      exact h1
    · filter_upwards with n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcontra
      rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from by norm_num, Complex.ofReal_inj] at hcontra
      have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), g z = 0 :=
    hseq.frequently (Eventually.of_forall fun n => hreal _).frequently
  have hEq := hAnal.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ 0) hfreq
  funext z
  exact hEq (Set.mem_univ z)

/-- **Window two-ray theorem.**  An entire `g` of exponential type with `‖g x‖ ≤ C e^{εx}` on the
negative ray and `∫_0^1 ‖g(x+t)‖ dt ≤ C e^{−εx}` on the positive ray vanishes identically. -/
theorem eq_zero_of_two_ray_window_integral_decay {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {A C τ ε : ℝ} (hA : 0 ≤ A) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (hgrow : ∀ z : ℂ, ‖g z‖ ≤ A * Real.exp (τ * ‖z‖))
    (hplus : ∀ x : ℝ, 0 ≤ x → ∫ t in (0 : ℝ)..1, ‖g (x + t)‖ ≤ C * Real.exp (-(ε * x)))
    (hminus : ∀ x : ℝ, x ≤ 0 → ‖g x‖ ≤ C * Real.exp (ε * x)) :
    g = 0 := by
  have hC : 0 ≤ C := by
    have h := hminus 0 le_rfl
    simp only [Complex.ofReal_zero, mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (norm_nonneg _) h
  set F : ℂ → ℂ := unitWindowAverage g with hF
  have hFd : Differentiable ℂ F := fun w => (hasDerivAt_unitWindowAverage hg w).differentiableAt
  -- exponential type of the window average
  have hFgrow : ∀ z : ℂ, ‖F z‖ ≤ (A * Real.exp τ) * Real.exp (τ * ‖z‖) := fun z => by
    refine norm_unitWindowAverage_le fun t ht => ?_
    calc ‖g (z + t)‖ ≤ A * Real.exp (τ * ‖z + (t : ℂ)‖) := hgrow _
      _ ≤ A * Real.exp (τ * (‖z‖ + 1)) := by
          gcongr
          calc ‖z + (t : ℂ)‖ ≤ ‖z‖ + ‖(t : ℂ)‖ := norm_add_le _ _
            _ ≤ ‖z‖ + 1 := by
                rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
                linarith [ht.2]
      _ = (A * Real.exp τ) * Real.exp (τ * ‖z‖) := by
          rw [mul_add, mul_one, Real.exp_add, mul_assoc, mul_comm (Real.exp (τ * ‖z‖))]
  -- the two-ray decay of the window average
  set C' : ℝ := max C (A * Real.exp τ) * Real.exp ε with hC'
  have hCC' : C ≤ C' :=
    le_trans (le_max_left _ _)
      (le_mul_of_one_le_right (le_max_of_le_left hC) (Real.one_le_exp hε.le))
  have hplusF : ∀ x : ℝ, 0 ≤ x → ‖F x‖ ≤ C' * Real.exp (-(ε * x)) := fun x hx => by
    calc ‖F x‖ ≤ ∫ t in (0 : ℝ)..1, ‖g (x + t)‖ :=
          intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ C * Real.exp (-(ε * x)) := hplus x hx
      _ ≤ C' * Real.exp (-(ε * x)) := by gcongr
  have hminusF : ∀ x : ℝ, x ≤ 0 → ‖F x‖ ≤ C' * Real.exp (ε * x) := fun x hx => by
    refine norm_unitWindowAverage_le fun t ht => ?_
    rcases le_or_gt (x + t) 0 with hxt | hxt
    · -- still on the decaying negative ray
      have h := hminus (x + t) hxt
      rw [Complex.ofReal_add] at h
      calc ‖g (x + t)‖ ≤ C * Real.exp (ε * (x + t)) := h
        _ = (C * Real.exp (ε * t)) * Real.exp (ε * x) := by
            rw [mul_add, Real.exp_add, mul_assoc, mul_comm (Real.exp (ε * x))]
        _ ≤ C' * Real.exp (ε * x) := by
            gcongr
            rw [hC']
            calc C * Real.exp (ε * t) ≤ C * Real.exp ε := by
                  gcongr
                  nlinarith [ht.2, hε]
              _ ≤ max C (A * Real.exp τ) * Real.exp ε := by
                  gcongr
                  exact le_max_left _ _
    · -- `0 < x + t ≤ 1`: the growth bound suffices since `e^{εx} ≥ e^{−ε}`
      have hx1 : -1 ≤ x := by linarith [ht.2]
      calc ‖g (x + t)‖ ≤ A * Real.exp (τ * ‖(x : ℂ) + t‖) := hgrow _
        _ ≤ A * Real.exp (τ * 1) := by
            gcongr
            rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxt]
            linarith [ht.2]
        _ = (A * Real.exp τ) * (Real.exp ε * Real.exp (ε * (-1))) := by
            rw [mul_one, ← Real.exp_add]
            simp
        _ ≤ max C (A * Real.exp τ) * (Real.exp ε * Real.exp (ε * x)) :=
            mul_le_mul (le_max_right _ _)
              (mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx1 hε.le)) (Real.exp_pos _).le)
              (by positivity) (le_max_of_le_left hC)
        _ = C' * Real.exp (ε * x) := by rw [hC', mul_assoc]
  have hF0 : F = 0 :=
    eq_zero_of_two_ray_exponential_decay hFd (by positivity) hτ hε hFgrow hplusF hminusF
  -- `F ≡ 0` forces `g(w+1) = g(w)`
  have hper : ∀ w : ℂ, g (w + 1) = g w := fun w => by
    have h1 : HasDerivAt F (g (w + 1) - g w) w := hasDerivAt_unitWindowAverage hg w
    rw [hF0] at h1
    have h2 : HasDerivAt (0 : ℂ → ℂ) 0 w := hasDerivAt_const w 0
    exact sub_eq_zero.mp (h1.unique h2)
  -- periodicity transports the negative-ray decay to every real point
  have hshift : ∀ (x : ℝ) (n : ℕ), g x = g ((x - n : ℝ) : ℂ) := by
    intro x n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcast : ((x - n : ℝ) : ℂ) = ((x - (n + 1 : ℕ) : ℝ) : ℂ) + 1 := by
        push_cast
        ring
      rw [ih, hcast, hper]
  have hreal : ∀ x : ℝ, g x = 0 := by
    intro x
    rw [← norm_eq_zero]
    refine le_antisymm (le_of_forall_pos_lt_add fun η hη => ?_) (norm_nonneg _)
    obtain ⟨n, hn⟩ := exists_nat_gt (max x (C * Real.exp (ε * x) / (η * ε)))
    have hnx : x < n := lt_of_le_of_lt (le_max_left _ _) hn
    have hnC : C * Real.exp (ε * x) / (η * ε) < n := lt_of_le_of_lt (le_max_right _ _) hn
    rw [div_lt_iff₀ (by positivity)] at hnC
    have hexp : η * ε * n ≤ η * Real.exp (ε * n) := by
      calc η * ε * n = η * (ε * n) := by ring
        _ ≤ η * (ε * n + 1) := by nlinarith
        _ ≤ η * Real.exp (ε * n) := by
            gcongr
            exact Real.add_one_le_exp _
    have hbound := hminus (x - n) (by linarith)
    rw [← hshift] at hbound
    calc ‖g x‖ ≤ C * Real.exp (ε * (x - n)) := hbound
      _ = C * Real.exp (ε * x) * Real.exp (-(ε * n)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
      _ < η * Real.exp (ε * n) * Real.exp (-(ε * n)) :=
          mul_lt_mul_of_pos_right (lt_of_lt_of_le (by linarith) hexp) (Real.exp_pos _)
      _ = η := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ = 0 + η := by ring
  exact eq_zero_of_forall_ofReal_eq_zero hg hreal

/-! ## Window largeness along the positive ray -/

/-- The unit-window integral of `Φ(w) e^{aw}` is at most `e^{a(x+1)}` times that of `Φ`. -/
theorem integral_norm_mul_exp_le {Φ : ℂ → ℂ} (hΦ : Continuous Φ) {a x : ℝ} (ha : 0 ≤ a) :
    ∫ t in (0 : ℝ)..1, ‖Φ (x + t) * Complex.exp ((a : ℂ) * (x + t))‖
      ≤ Real.exp (a * (x + 1)) * ∫ t in (0 : ℝ)..1, ‖Φ (x + t)‖ := by
  have hc : Continuous fun t : ℝ => Φ (x + t) := hΦ.comp (continuous_const.add continuous_ofReal)
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (μ := volume) (by norm_num) ?_ ?_ fun t ht => ?_
  · exact (hc.norm.mul (Complex.continuous_exp.comp
      (continuous_const.mul (continuous_const.add continuous_ofReal))).norm).intervalIntegrable 0 1
  · exact (hc.norm.const_mul _).intervalIntegrable 0 1
  · rw [norm_mul, Complex.norm_exp, mul_comm]
    gcongr
    rw [show ((a : ℂ) * ((x : ℂ) + t)).re = a * (x + t) by
      rw [← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re]]
    gcongr
    exact ht.2

/-- **Window largeness.**  An entire `Φ ≢ 0` of exponential type `ρ` has
`∫_0^1 ‖Φ(x+t)‖ dt ≥ e^{−(ρ+δ)} e^{−(ρ+δ)x}` at arbitrarily large real `x`: otherwise
`Φ(w) e^{(ρ+δ/2)w}` has two-ray window decay and vanishes. -/
theorem exists_window_integral_ge_of_exponentialType {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {C ρ : ℝ} (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖))
    (hne : Φ ≠ 0) {δ : ℝ} (hδ : 0 < δ) (X : ℝ) :
    ∃ x : ℝ, X ≤ x ∧
      Real.exp (-((ρ + δ) * x)) ≤ Real.exp (ρ + δ) * ∫ t in (0 : ℝ)..1, ‖Φ (x + t)‖ := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hC : 0 ≤ C := by
    have h := hgrow 0
    simp only [norm_zero, mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (norm_nonneg _) h
  set X' : ℝ := max X 0 with hX'
  have hX'0 : 0 ≤ X' := le_max_right _ _
  set a : ℝ := ρ + δ / 2 with ha
  have ha0 : 0 ≤ a := by positivity
  set τ : ℝ := 2 * ρ + δ / 2 with hτ
  have hτ0 : 0 ≤ τ := by positivity
  set g : ℂ → ℂ := fun w => Φ w * Complex.exp ((a : ℂ) * w) with hg
  have hgdiff : Differentiable ℂ g :=
    hΦ.mul (Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id))
  have hgnorm : ∀ w, ‖g w‖ = ‖Φ w‖ * Real.exp (a * w.re) := fun w => by
    rw [hg]
    simp only
    rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
  have hgrow' : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (τ * ‖z‖) := fun z => by
    rw [hgnorm]
    calc ‖Φ z‖ * Real.exp (a * z.re)
        ≤ (C * Real.exp (ρ * ‖z‖)) * Real.exp (a * ‖z‖) := by
          gcongr
          · exact hgrow z
          · exact Complex.re_le_norm z
      _ = C * Real.exp (τ * ‖z‖) := by
          rw [mul_assoc, ← Real.exp_add, ha, hτ]
          congr 2
          ring
  -- the constant for both rays
  set C₂ : ℝ := max 1 (C * Real.exp (τ * (X' + 1)) * Real.exp (δ / 2 * X')) with hC₂
  have hCC₂ : C ≤ C₂ := by
    refine le_trans ?_ (le_max_right _ _)
    calc C = C * 1 * 1 := by ring
      _ ≤ C * Real.exp (τ * (X' + 1)) * Real.exp (δ / 2 * X') := by
          gcongr
          · exact Real.one_le_exp (by positivity)
          · exact Real.one_le_exp (by positivity)
  -- the negative ray decays
  have hminus : ∀ x : ℝ, x ≤ 0 → ‖g x‖ ≤ C₂ * Real.exp (δ / 2 * x) := fun x hx => by
    rw [hgnorm, Complex.ofReal_re]
    calc ‖Φ x‖ * Real.exp (a * x)
        ≤ (C * Real.exp (ρ * ‖(x : ℂ)‖)) * Real.exp (a * x) := by
          gcongr
          exact hgrow x
      _ = C * Real.exp (δ / 2 * x) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hx, mul_assoc, ← Real.exp_add, ha]
          congr 2
          ring
      _ ≤ C₂ * Real.exp (δ / 2 * x) := by gcongr
  -- the positive-ray window integrals decay
  have hplus : ∀ x : ℝ, 0 ≤ x →
      ∫ t in (0 : ℝ)..1, ‖g (x + t)‖ ≤ C₂ * Real.exp (-(δ / 2 * x)) := fun x hx => by
    rcases le_or_gt X' x with hXx | hXx
    · -- the large-`x` range: the contradiction hypothesis
      have h1 := hcon x (le_trans (le_max_left _ _) hXx)
      have h2 := integral_norm_mul_exp_le hΦ.continuous (a := a) (x := x) ha0
      calc ∫ t in (0 : ℝ)..1, ‖g (x + t)‖
          = ∫ t in (0 : ℝ)..1, ‖Φ (x + t) * Complex.exp ((a : ℂ) * (x + t))‖ := rfl
        _ ≤ Real.exp (a * (x + 1)) * ∫ t in (0 : ℝ)..1, ‖Φ (x + t)‖ := h2
        _ ≤ Real.exp (a * (x + 1)) * (Real.exp (-((ρ + δ) * x)) / Real.exp (ρ + δ)) := by
            gcongr
            rw [le_div_iff₀ (Real.exp_pos _), mul_comm]
            exact h1.le
        _ = Real.exp (-(δ / 2)) * Real.exp (-(δ / 2 * x)) := by
            rw [← Real.exp_sub, ← Real.exp_add, ← Real.exp_add, ha]
            congr 1
            ring
        _ ≤ 1 * Real.exp (-(δ / 2 * x)) := by
            gcongr
            exact Real.exp_le_one_iff.mpr (by linarith)
        _ ≤ C₂ * Real.exp (-(δ / 2 * x)) := by
            gcongr
            exact le_max_left _ _
    · -- the bounded range `0 ≤ x < X'`: the growth bound
      have hgc : Continuous fun t : ℝ => ‖g (x + t)‖ :=
        (hgdiff.continuous.comp (continuous_const.add continuous_ofReal)).norm
      calc ∫ t in (0 : ℝ)..1, ‖g (x + t)‖
          ≤ ∫ t in (0 : ℝ)..1, C * Real.exp (τ * (X' + 1)) := by
            refine intervalIntegral.integral_mono_on zero_le_one (hgc.intervalIntegrable 0 1)
              intervalIntegrable_const fun t ht => ?_
            calc ‖g (x + t)‖ ≤ C * Real.exp (τ * ‖(x : ℂ) + t‖) := hgrow' _
              _ ≤ C * Real.exp (τ * (X' + 1)) := by
                  gcongr
                  rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
                    abs_of_nonneg (by linarith [ht.1])]
                  linarith [ht.2]
        _ = C * Real.exp (τ * (X' + 1)) := by simp
        _ = (C * Real.exp (τ * (X' + 1)) * Real.exp (δ / 2 * X')) * Real.exp (-(δ / 2 * X')) := by
            rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        _ ≤ C₂ * Real.exp (-(δ / 2 * x)) :=
            mul_le_mul (le_max_right _ _)
              (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hXx.le (by positivity))))
              (Real.exp_pos _).le (le_trans zero_le_one (le_max_left _ _))
  have hg0 : g = 0 := eq_zero_of_two_ray_window_integral_decay hgdiff hC hτ0
    (half_pos hδ) hgrow' hplus hminus
  apply hne
  funext w
  have h := congrFun hg0 w
  rw [hg] at h
  simp only [Pi.zero_apply, mul_eq_zero, Complex.exp_ne_zero, or_false] at h
  exact h

/-! ## Lipschitz propagation and the lower Riemann sum -/

/-- Lipschitz bound on `[x, x+2]`, `x ≥ 0`: `‖Φ v − Φ u‖ ≤ C e^{ρ(x+3)} (v − u)` by the Cauchy
estimate for the derivative. -/
theorem norm_sub_le_of_exponentialType {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖))
    {x u v : ℝ} (hx : 0 ≤ x) (hu : x ≤ u) (huv : u ≤ v) (hv : v ≤ x + 2) :
    ‖Φ v - Φ u‖ ≤ C * Real.exp (ρ * (x + 3)) * (v - u) := by
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s : ℝ => Φ s)
    (f' := fun s : ℝ => deriv Φ s) (a := u) (b := v) (C := C * Real.exp (ρ * (x + 3)))
    (fun s _ => ((hΦ (s : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt)
    (fun s hs => ?_) v ⟨huv, le_rfl⟩
  · exact hmvt
  · have hs0 : 0 ≤ s := by linarith [hs.1]
    calc ‖deriv Φ s‖ ≤ C * Real.exp (ρ * (s + 1)) :=
          norm_deriv_le_of_exponentialType hΦ hC hρ hgrow hs0
      _ ≤ C * Real.exp (ρ * (x + 3)) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hρ)) hC

/-- **Lower Riemann sum.**  For continuous `f` with `f v ≤ f u + D (v − u)` on `0 ≤ u ≤ v ≤ 1`
and `h = 1/N`: `∫_0^1 f ≤ Σ_{k<N} h f(kh) + hD`. -/
theorem integral_le_sum_window_values_add {f : ℝ → ℝ} (hf : Continuous f) {N : ℕ} (hN : 0 < N)
    {D : ℝ} (hD : 0 ≤ D)
    (hlip : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ 1 → f v ≤ f u + D * (v - u)) :
    ∫ t in (0 : ℝ)..1, f t
      ≤ (∑ k ∈ range N, (1 / N : ℝ) * f (k * (1 / N))) + (1 / N : ℝ) * D := by
  set h : ℝ := 1 / N with hh
  have hh0 : 0 < h := by positivity
  have hNh : (N : ℝ) * h = 1 := by rw [hh]; field_simp
  -- split the integral along the partition `k h`
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f)
    (a := fun k : ℕ => (k : ℝ) * h) (n := N) (fun k _ => hf.intervalIntegrable _ _)
  simp only [Nat.cast_zero, zero_mul, hNh] at hsplit
  rw [← hsplit]
  -- each window integral is at most `h (f(kh) + hD)`
  have hwin : ∀ k ∈ range N,
      ∫ t in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), f t ≤ h * f (k * h) + h * (h * D) := by
    intro k hk
    have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hkh : ((k + 1 : ℕ) : ℝ) * h = k * h + h := by push_cast; ring
    rw [hkh]
    calc ∫ t in ((k : ℝ) * h)..(k * h + h), f t
        ≤ ∫ t in ((k : ℝ) * h)..(k * h + h), (f (k * h) + h * D) := by
          refine intervalIntegral.integral_mono_on (μ := volume) (by linarith)
            (hf.intervalIntegrable _ _) intervalIntegrable_const fun t ht => ?_
          have ht1 : t ≤ 1 := by
            calc t ≤ k * h + h := ht.2
              _ = ((k : ℝ) + 1) * h := by ring
              _ ≤ N * h := by gcongr
              _ = 1 := hNh
          calc f t ≤ f (k * h) + D * (t - k * h) := hlip _ _ (by positivity) ht.1 ht1
            _ ≤ f (k * h) + D * h := by
                gcongr
                linarith [ht.2]
            _ = f (k * h) + h * D := by ring
      _ = h * f (k * h) + h * (h * D) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
  calc ∑ k ∈ range N, ∫ t in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), f t
      ≤ ∑ k ∈ range N, (h * f (k * h) + h * (h * D)) := sum_le_sum hwin
    _ = (∑ k ∈ range N, h * f (k * h)) + h * D := by
        rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_assoc, hNh, one_mul]

/-- Sums over consecutive windows `(b k, b (k+1)]` merge into the sum over `(b 0, b N]`. -/
theorem sum_range_sum_Ioc_eq_sum_Ioc {f : ℕ → ℝ} {b : ℕ → ℕ} (hb : Monotone b) (N : ℕ) :
    ∑ k ∈ range N, ∑ p ∈ Finset.Ioc (b k) (b (k + 1)), f p
      = ∑ p ∈ Finset.Ioc (b 0) (b N), f p := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih,
      Finset.sum_Ioc_consecutive f (hb (Nat.zero_le N)) (hb (Nat.le_succ N))]

/-! ## The prime sums are unbounded at the natural rate -/

/-- **The prime-sum lower bound at the natural rate.**  For `Φ ≢ 0` entire with
`‖Φ ξ‖ ≤ C e^{ρ‖ξ‖}`, `0 ≤ σ`, `ρ < 1 − σ` and `2ρ < 5/12`, the sums `Σ_{p<N} p^{−σ} ‖Φ(log p)‖`
are unbounded. -/
theorem exists_primeLogWeightedSum_gt_of_lt_one_sub {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {C ρ σ : ℝ} (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖)) (hne : Φ ≠ 0)
    (hσ : 0 ≤ σ) (hρσ : ρ < 1 - σ) (hρ5 : 2 * ρ < 5 / 12) (M : ℝ) :
    ∃ N : ℕ, M < primeLogWeightedSum Φ σ N := by
  -- the growth constant is positive, since `Φ ≢ 0`
  have hC : 0 < C := by
    by_contra hC
    simp only [not_lt] at hC
    apply hne
    funext ξ
    have h := hgrow ξ
    have h2 : C * Real.exp (ρ * ‖ξ‖) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (Real.exp_pos _).le
    exact norm_le_zero_iff.mp (le_trans h h2)
  have hC0 : C ≠ 0 := hC.ne'
  -- the exponents
  set δ : ℝ := min ((1 - σ - ρ) / 4) (min ((5 / 12 - 2 * ρ) / 4) (1 / 24)) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have hδ1 : δ ≤ (1 - σ - ρ) / 4 := min_le_left _ _
  have hδ2 : δ ≤ (5 / 12 - 2 * ρ) / 4 := (min_le_right _ _).trans (min_le_left _ _)
  clear_value δ
  set γ : ℝ := 2 * ρ + 2 * δ with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hγ5 : γ < 5 / 12 := by rw [hγ]; linarith
  clear_value γ
  set β : ℝ := 1 - γ with hβ
  have hβ7 : 7 / 12 < β := by rw [hβ]; linarith
  clear_value β
  set α : ℝ := (7 / 12 + β) / 2 with hα
  have hα7 : 7 / 12 < α := by rw [hα]; linarith
  have hαβ : α < β := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα, hβ]; linarith
  clear_value α
  set e : ℝ := 1 - σ - ρ - δ with he
  have he0 : 0 < e := by rw [he]; linarith
  clear_value e
  -- the prime-mass window theorem
  obtain ⟨X₁, hX₁1, hθ⟩ := exists_theta_window_lower_seven_twelfths hα7 hα1
  -- constants
  set c₁ : ℝ := Real.exp (-(4 * ρ + δ)) / (4 * C) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  clear_value c₁
  set m₀ : ℝ := Real.exp (-(ρ + δ)) with hm₀
  have hm₀0 : 0 < m₀ := Real.exp_pos _
  clear_value m₀
  set c₂ : ℝ := Real.exp (-σ) * m₀ / 8 with hc₂
  have hc₂0 : 0 < c₂ := by positivity
  clear_value c₂
  set c₃ : ℝ := c₂ * (e / 2) * Real.exp (-(e / 2)) with hc₃
  have hc₃0 : 0 < c₃ := by positivity
  clear_value c₃
  -- the thresholds in `y`
  have hev : ∀ᶠ y : ℝ in atTop, X₁ ≤ y ∧ 1 ≤ y ∧ c₁ ≤ y ^ γ ∧
      4 * Real.exp α / c₁ ≤ y ^ (β - α) ∧ (M + 1) / c₃ ≤ y ^ (e / 2) := by
    refine (eventually_ge_atTop X₁).and ((eventually_ge_atTop 1).and
      (((tendsto_rpow_atTop hγ0).eventually_ge_atTop c₁).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _).and
      ((tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _))))
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp hev
  -- a large window on which the integral of `‖Φ‖` is not small
  obtain ⟨x, hxY, hint⟩ :=
    exists_window_integral_ge_of_exponentialType hΦ hρ hgrow hne hδ0 (max Y₀ 0)
  have hx0 : 0 ≤ x := le_trans (le_max_right _ _) hxY
  set y : ℝ := Real.exp x with hy
  have hy0 : 0 < y := Real.exp_pos x
  have hxy : x + 1 ≤ y := by rw [hy]; exact Real.add_one_le_exp x
  have hyY : Y₀ ≤ y := by
    calc Y₀ ≤ max Y₀ 0 := le_max_left _ _
      _ ≤ x := hxY
      _ ≤ y := by linarith
  obtain ⟨hyX₁, hy1, hyc₁, hyαβ, hyM⟩ := hY₀ y hyY
  have hlogy : Real.log y = x := by rw [hy]; exact Real.log_exp x
  have hypow : ∀ s : ℝ, y ^ s = Real.exp (s * x) := fun s => by
    rw [Real.rpow_def_of_pos hy0, hlogy]
  clear_value y
  -- the window-integral lower bound `m`
  set f : ℝ → ℝ := fun t => ‖Φ (x + t)‖ with hf
  have hfc : Continuous f := (hΦ.continuous.comp (continuous_const.add continuous_ofReal)).norm
  set m : ℝ := m₀ * Real.exp (-((ρ + δ) * x)) with hm
  have hm0 : 0 < m := by positivity
  have hmint : m ≤ ∫ t in (0 : ℝ)..1, f t := by
    have h : Real.exp (-((ρ + δ) * x)) / Real.exp (ρ + δ) ≤ ∫ t in (0 : ℝ)..1, f t := by
      rw [div_le_iff₀ (Real.exp_pos _), mul_comm]
      exact hint
    rw [← Real.exp_sub] at h
    rw [hm, hm₀, ← Real.exp_add]
    convert h using 2
    ring
  clear_value m
  -- the window length `η` and the window count `N`
  set η : ℝ := c₁ * Real.exp (-(γ * x)) with hη
  have hη0 : 0 < η := by positivity
  have hexpγ : Real.exp (-(γ * x)) = (y ^ γ)⁻¹ := by rw [hypow, ← Real.exp_neg]
  have hη1 : η ≤ 1 := by
    rw [hη, hexpγ, mul_inv_le_iff₀ (by positivity), one_mul]
    exact hyc₁
  clear_value η
  set N : ℕ := ⌈1 / η⌉₊ with hN
  have hN0 : 0 < N := Nat.ceil_pos.mpr (by positivity)
  set h : ℝ := 1 / N with hh
  have hh0 : 0 < h := by positivity
  have hNh : (N : ℝ) * h = 1 := by rw [hh]; field_simp
  have hhη : h ≤ η := by
    rw [hh, div_le_iff₀ (by positivity)]
    have h1 := Nat.le_ceil (1 / η)
    rw [div_le_iff₀ hη0] at h1
    linarith
  have hηh : η / 2 ≤ h := by
    rw [hh, le_div_iff₀ (by positivity)]
    have h1 := Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / η)
    have h2 : (N : ℝ) ≤ 2 / η := by
      calc (N : ℝ) ≤ 1 / η + 1 := h1.le
        _ ≤ 1 / η + 1 / η := by
            gcongr
            rw [le_div_iff₀ hη0]
            linarith
        _ = 2 / η := by ring
    calc η / 2 * N ≤ η / 2 * (2 / η) := by gcongr
      _ = 1 := by field_simp
  clear_value N
  clear_value h
  -- the Lipschitz constant on `[x, x+2]` and the Riemann-sum error
  set D : ℝ := C * Real.exp (ρ * (x + 3)) with hD
  have hD0 : 0 ≤ D := by positivity
  have hhD : h * D ≤ m / 4 := by
    calc h * D ≤ η * D := by gcongr
      _ = Real.exp (-(4 * ρ + δ)) / (4 * C) * Real.exp (-(γ * x))
            * (C * Real.exp (ρ * (x + 3))) := by
          rw [hη, hD, hc₁]
      _ = m₀ / 4 * Real.exp (-((ρ + δ) * x)) * Real.exp (-(δ * x)) := by
          rw [hm₀, hγ]
          field_simp
          simp only [← Real.exp_add]
          ring_nf
      _ ≤ m₀ / 4 * Real.exp (-((ρ + δ) * x)) * 1 := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by nlinarith)
      _ = m / 4 := by rw [hm]; ring
  clear_value D
  -- the Lipschitz property of `f` on `[0, 1]`
  have hlip : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ 1 → f v ≤ f u + D * (v - u) := by
    intro u v hu huv hv1
    have hsub := norm_sub_le_of_exponentialType hΦ hC.le hρ hgrow (x := x) (u := x + u)
      (v := x + v) hx0 (by linarith) (by linarith) (by linarith)
    rw [Complex.ofReal_add, Complex.ofReal_add] at hsub
    rw [hD, hf]
    simp only
    calc ‖Φ (x + v)‖ ≤ ‖Φ (x + u)‖ + ‖Φ (x + v) - Φ (x + u)‖ := by
          have := norm_sub_norm_le (Φ (x + v)) (Φ (x + u))
          linarith
      _ ≤ ‖Φ (x + u)‖ + C * Real.exp (ρ * (x + 3)) * (x + v - (x + u)) := by gcongr
      _ = ‖Φ (x + u)‖ + C * Real.exp (ρ * (x + 3)) * (v - u) := by ring
  -- the lower Riemann sum
  have hriemann := integral_le_sum_window_values_add hfc hN0 hD0 hlip
  rw [← hh] at hriemann
  -- the per-window lower bounds `m_k` and their weighted sum
  set mk : ℕ → ℝ := fun k => max 0 (f (k * h) - h * D) with hmk
  have hmk0 : ∀ k, 0 ≤ mk k := fun k => le_max_left _ _
  have hmksum : m / 2 ≤ ∑ k ∈ range N, h * mk k := by
    have h1 : ∑ k ∈ range N, h * (f (k * h) - h * D) ≤ ∑ k ∈ range N, h * mk k :=
      sum_le_sum fun k _ => by
        gcongr
        exact le_max_right _ _
    have h2 : ∑ k ∈ range N, h * (f (k * h) - h * D)
        = (∑ k ∈ range N, h * f (k * h)) - h * D := by
      simp only [mul_sub, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      rw [← mul_assoc, ← mul_assoc, hNh, one_mul]
    linarith
  -- the prime windows `(Y k, Y (k+1)]`
  set Y : ℕ → ℝ := fun k => Real.exp (x + k * h) with hY
  have hYpos : ∀ k, 0 < Y k := fun k => Real.exp_pos _
  have hYmono : Monotone Y := fun i j hij => by
    rw [hY]
    simp only
    exact Real.exp_le_exp.mpr (by gcongr)
  have hY0 : Y 0 = y := by simp [hY, hy]
  have hYge : ∀ k, y ≤ Y k := fun k => hY0 ▸ hYmono (Nat.zero_le k)
  have hYle : ∀ k ∈ range (N + 1), Y k ≤ Real.exp (x + 1) := fun k hk => by
    rw [hY]
    simp only
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    refine Real.exp_le_exp.mpr ?_
    have : (k : ℝ) * h ≤ 1 := by
      calc (k : ℝ) * h ≤ N * h := by gcongr
        _ = 1 := hNh
    linarith
  have hYsucc : ∀ k, Y (k + 1) = Y k * Real.exp h := fun k => by
    rw [hY]
    simp only
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hLk : ∀ k, Y k * h ≤ Y (k + 1) - Y k := fun k => by
    rw [hYsucc]
    nlinarith [Real.add_one_le_exp h, hYpos k]
  have hlogY : ∀ k, Real.log (Y k) = x + k * h := fun k => by rw [hY]; exact Real.log_exp _
  -- the lower bound for each prime window
  have hwin : ∀ k ∈ range N,
      Real.exp (-(σ * (x + 1))) * mk k / (x + 1) * (y * h / 4)
        ≤ ∑ p ∈ Finset.Ioc ⌊Y k⌋₊ ⌊Y (k + 1)⌋₊,
            if p.Prime then (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ else 0 := by
    intro k hk
    have hkN : k + 1 ∈ range (N + 1) :=
      Finset.mem_range.mpr (Nat.succ_lt_succ (Finset.mem_range.mp hk))
    have hk1 : Y (k + 1) ≤ Real.exp (x + 1) := hYle _ hkN
    have hkh : (k : ℝ) * h + h ≤ 1 := by
      have : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Finset.mem_range.mp hk
      calc (k : ℝ) * h + h = ((k + 1 : ℕ) : ℝ) * h := by push_cast; ring
        _ ≤ N * h := by gcongr
        _ = 1 := hNh
    set L : ℝ := Y (k + 1) - Y k with hL
    have hyhL : y * h ≤ L :=
      le_trans (mul_le_mul_of_nonneg_right (hYge k) hh0.le) (hLk k)
    have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hyhL
    have hYL : Y k + L = Y (k + 1) := by rw [hL]; ring
    clear_value L
    -- the values of `Φ` at the primes of the window
    have hlow : ∀ p : ℕ, p.Prime → Y k < p → (p : ℝ) ≤ Y k + L → mk k ≤ ‖Φ (Real.log p)‖ := by
      intro p hp hp1 hp2
      rw [hYL] at hp2
      have hp0 : (0 : ℝ) < p := lt_trans (hYpos k) hp1
      have hlog1 : x + k * h ≤ Real.log p := by
        rw [← hlogY]
        exact (Real.log_lt_log (hYpos k) hp1).le
      have hlog2 : Real.log p ≤ x + k * h + h := by
        calc Real.log p ≤ Real.log (Y (k + 1)) := Real.log_le_log hp0 hp2
          _ = x + k * h + h := by rw [hlogY]; push_cast; ring
      have hsub := norm_sub_le_of_exponentialType hΦ hC.le hρ hgrow (x := x) (u := x + k * h)
        (v := Real.log p) hx0 (le_add_of_nonneg_right (by positivity)) hlog1 (by linarith)
      rw [← hD] at hsub
      show max 0 (f (k * h) - h * D) ≤ ‖Φ (Real.log p)‖
      refine max_le (norm_nonneg _) ?_
      have hval : f (k * h) = ‖Φ (((x + k * h : ℝ)) : ℂ)‖ := by
        rw [hf]
        simp only
        rw [Complex.ofReal_add]
      rw [hval]
      have h1 := norm_sub_norm_le (Φ ((x + k * h : ℝ) : ℂ)) (Φ (Real.log p))
      rw [norm_sub_rev] at h1
      have h2 : D * (Real.log p - (x + k * h)) ≤ D * h := by
        gcongr
        linarith
      linarith
    -- the Chebyshev mass of the window
    have hθwin : y * h / 4 ≤ Chebyshev.theta (Y k + L) - Chebyshev.theta (Y k) := by
      have h1 := hθ (Y k) L (le_trans hyX₁ (hYge k)) hL0.le
      have hk1' : Y (k + 1) ≤ Real.exp 1 * y := by
        calc Y (k + 1) ≤ Real.exp (x + 1) := hk1
          _ = Real.exp 1 * y := by rw [hy, ← Real.exp_add]; ring_nf
      have h2 : (Y k + L) ^ α ≤ L / 2 := by
        rw [hYL]
        calc Y (k + 1) ^ α ≤ (Real.exp 1 * y) ^ α :=
              Real.rpow_le_rpow (hYpos _).le hk1' (by linarith)
          _ = Real.exp α * y ^ α := by
              rw [Real.mul_rpow (Real.exp_pos 1).le hy0.le, ← Real.exp_mul, one_mul]
          _ ≤ c₁ / 4 * y ^ β := by
              have h3 : 4 * Real.exp α / c₁ * y ^ α ≤ y ^ (β - α) * y ^ α := by gcongr
              rw [← Real.rpow_add hy0, sub_add_cancel] at h3
              calc Real.exp α * y ^ α = (4 * Real.exp α / c₁ * y ^ α) * c₁ / 4 := by
                    field_simp
                _ ≤ y ^ β * c₁ / 4 := by gcongr
                _ = c₁ / 4 * y ^ β := by ring
          _ ≤ y * h / 2 := by
              have h4 : c₁ * y ^ β = η * y := by
                rw [hη, hβ, hexpγ, Real.rpow_sub hy0, Real.rpow_one, div_eq_mul_inv]
                ring
              calc c₁ / 4 * y ^ β = (c₁ * y ^ β) / 4 := by ring
                _ = η * y / 4 := by rw [h4]
                _ = (η / 2) * y / 2 := by ring
                _ ≤ h * y / 2 := by gcongr
                _ = y * h / 2 := by ring
          _ ≤ L / 2 := by linarith
      linarith
    -- assemble via the window lemma
    have hsum := window_sum_ge_theta_window Φ hσ
      (by rw [hYL]; exact Real.one_lt_exp_iff.mpr (by positivity)) hL0.le (hmk0 k) hlow
    rw [hYL] at hsum hθwin
    have hlogk : Real.log (Y (k + 1)) = x + k * h + h := by rw [hlogY]; push_cast; ring
    have hlogpos : 0 < Real.log (Y (k + 1)) := by rw [hlogk]; positivity
    have hlogle : Real.log (Y (k + 1)) ≤ x + 1 := by rw [hlogk]; linarith
    have hrp : Real.exp (-(σ * (x + 1))) ≤ Y (k + 1) ^ (-σ) := by
      calc Real.exp (-(σ * (x + 1))) = Real.exp (x + 1) ^ (-σ) := by
            rw [← Real.exp_mul]
            congr 1
            ring
        _ ≤ Y (k + 1) ^ (-σ) := Real.rpow_le_rpow_of_nonpos (hYpos _) hk1 (by linarith)
    have hnum : Real.exp (-(σ * (x + 1))) * mk k ≤ Y (k + 1) ^ (-σ) * mk k :=
      mul_le_mul_of_nonneg_right hrp (hmk0 k)
    have hnn : 0 ≤ Y (k + 1) ^ (-σ) * mk k :=
      mul_nonneg (Real.rpow_nonneg (hYpos _).le _) (hmk0 k)
    have hA : Real.exp (-(σ * (x + 1))) * mk k / (x + 1)
        ≤ Y (k + 1) ^ (-σ) * mk k / Real.log (Y (k + 1)) :=
      calc Real.exp (-(σ * (x + 1))) * mk k / (x + 1) ≤ Y (k + 1) ^ (-σ) * mk k / (x + 1) :=
            div_le_div_of_nonneg_right hnum (by linarith)
        _ ≤ Y (k + 1) ^ (-σ) * mk k / Real.log (Y (k + 1)) :=
            div_le_div_of_nonneg_left hnn hlogpos hlogle
    calc Real.exp (-(σ * (x + 1))) * mk k / (x + 1) * (y * h / 4)
        ≤ Y (k + 1) ^ (-σ) * mk k / Real.log (Y (k + 1)) * (y * h / 4) :=
          mul_le_mul_of_nonneg_right hA (by positivity)
      _ ≤ Y (k + 1) ^ (-σ) * mk k / Real.log (Y (k + 1))
            * (Chebyshev.theta (Y (k + 1)) - Chebyshev.theta (Y k)) :=
          mul_le_mul_of_nonneg_left hθwin (div_nonneg hnn hlogpos.le)
      _ ≤ _ := hsum
  -- the window sums merge into one prime sum
  have hmerge := sum_range_sum_Ioc_eq_sum_Ioc
    (f := fun p : ℕ => if p.Prime then (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ else 0)
    (b := fun k => ⌊Y k⌋₊) (fun i j hij => Nat.floor_le_floor (hYmono hij)) N
  have hchain : ∑ k ∈ range N, Real.exp (-(σ * (x + 1))) * mk k / (x + 1) * (y * h / 4)
      ≤ primeLogWeightedSum Φ σ (⌊Y N⌋₊ + 1) := by
    calc ∑ k ∈ range N, Real.exp (-(σ * (x + 1))) * mk k / (x + 1) * (y * h / 4)
        ≤ ∑ k ∈ range N, ∑ p ∈ Finset.Ioc ⌊Y k⌋₊ ⌊Y (k + 1)⌋₊,
            (if p.Prime then (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ else 0) := sum_le_sum hwin
      _ = ∑ p ∈ Finset.Ioc ⌊Y 0⌋₊ ⌊Y N⌋₊,
            (if p.Prime then (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ else 0) := hmerge
      _ ≤ primeLogWeightedSum Φ σ (⌊Y N⌋₊ + 1) := window_sum_le_primeLogWeightedSum Φ σ _ _
  refine ⟨⌊Y N⌋₊ + 1, lt_of_lt_of_le ?_ hchain⟩
  -- the explicit power lower bound
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hfactor : ∑ k ∈ range N, Real.exp (-(σ * (x + 1))) * mk k / (x + 1) * (y * h / 4)
      = Real.exp (-(σ * (x + 1))) * y / (4 * (x + 1)) * ∑ k ∈ range N, h * mk k := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    field_simp
    ring
  rw [hfactor]
  have hlog3 : x + 1 ≤ (Real.exp 1 * y) ^ (e / 2) / (e / 2) := by
    have := Real.log_le_rpow_div (by positivity : 0 ≤ Real.exp 1 * y) (by positivity : 0 < e / 2)
    rwa [Real.log_mul (Real.exp_pos 1).ne' hy0.ne', Real.log_exp, hlogy, add_comm] at this
  have hye : y ^ e = y ^ (e / 2) * y ^ (e / 2) := by
    rw [← Real.rpow_add hy0]
    congr 1
    ring
  calc M < M + 1 := by linarith
    _ ≤ c₃ * y ^ (e / 2) := by
        rw [mul_comm]
        exact (div_le_iff₀ hc₃0).mp hyM
    _ = c₂ * y ^ e / ((Real.exp 1 * y) ^ (e / 2) / (e / 2)) := by
        rw [hc₃, Real.mul_rpow (Real.exp_pos 1).le hy0.le, ← Real.exp_mul, one_mul, hye,
          Real.exp_neg]
        field_simp
    _ ≤ c₂ * y ^ e / (x + 1) := div_le_div_of_nonneg_left (by positivity) hx1 hlog3
    _ = Real.exp (-(σ * (x + 1))) * y / (4 * (x + 1)) * (m / 2) := by
        rw [hc₂, hm, hm₀, hypow, hy, he]
        field_simp
        simp only [← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(σ * (x + 1))) * y / (4 * (x + 1)) * ∑ k ∈ range N, h * mk k := by
        gcongr

end RHTower
