import GaloisForLFunctions.RHTower.XiSliceSaddleQuantitativeBounds

/-!
# Lower bounds for the slice derivatives at Euler points from `x₀ = 3/4`

Let `S(t, x) = |ξ(½+x+it)|²` on the real axis and `D_n(x) = Re S^{(n)}(t, x)/n!`.

**Theorem** (`exists_iteratedDeriv_xiSliceProduct_ge_euler_near_edge`).  There is `t₀` such that for
`t ≥ t₀`, real `x₀ ∈ [3/4, 2]` and `1 ≤ n ≤ log t`,

  `D_n(x₀) ≥ S(t, x₀) · L′ⁿ/n! · 1/(40π√(2 log t))`,   `L′ = log(t/2) − 2C_{1/8}`.

The cumulant regime needs `x₀ ≥ ½ + 2η` and the saddle regime `x₀ + R ≥ ½ + 2η` with `η = 1/8`, so
the Euler-point lower bound holds down to `x₀ = 3/4`, i.e. `Re s = 5/4`:

* orders `n ≤ c₁ log t`: the cumulant expansion (`iteratedDeriv_xiSliceProduct_ge_cumulant`) gives
  `S(x₀) h₁ⁿ/2` with `h₁ = L(x₀) ≥ L′`;
* orders `c₁ log t < n ≤ log t`: the saddle point at radius `R ∈ [c₁/2, 2]` about `x₀`
  (`iteratedDeriv_xiSliceProduct_ge_of_saddle_shift`) gives `S(x₀+R)/(πRⁿ) · Λ^{−1/2}/40`, and
  `S(x₀+R) ≥ S(x₀)e^{L′R}` with `e^{L′R}/Rⁿ ≥ (eL′/n)ⁿ ≥ L′ⁿ/n!`.
-/

open Complex Real Metric intervalIntegral
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- **Lower bound for the slice derivatives at Euler points `x₀ ∈ [½ + 2η, 2]`**, `0 < η ≤ 1/8`. -/
theorem exists_iteratedDeriv_xiSliceProduct_ge_euler_from {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ x₀ : ℝ, 1 / 2 + 2 * η ≤ x₀ → x₀ ≤ 2 → ∀ n : ℕ,
      1 ≤ n → (n : ℝ) ≤ Real.log t →
      xiSliceReal t x₀ * (Real.log (t / 2) - 2 * xiEulerConstant η) ^ n / n.factorial
          * (1 / (40 * Real.pi * Real.sqrt (2 * Real.log t)))
        ≤ (((n.factorial : ℂ))⁻¹ * iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ)).re := by
  obtain ⟨R₁, hR₁def⟩ : ∃ R₁ : ℝ, R₁ = 4 := ⟨_, rfl⟩
  have hR₁ : 1 ≤ R₁ := by rw [hR₁def]; norm_num
  have hR₁0 : 0 < R₁ := by linarith
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant η := ⟨_, rfl⟩
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos hη
  obtain ⟨M, hMdef⟩ : ∃ M, M = Real.log 4 + Real.pi + 4 * E := ⟨_, rfl⟩
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hM0 : 0 < M := by rw [hMdef]; positivity
  obtain ⟨K, hKdef⟩ : ∃ K, K = R₁ / (2 * η) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hKdef, le_div_iff₀ (by positivity)]; linarith
  obtain ⟨θ₁, hθ₁def⟩ : ∃ θ₁, θ₁ = 1 / (1000 * K) := ⟨_, rfl⟩
  have hθ₁0 : 0 < θ₁ := by rw [hθ₁def]; positivity
  have hθ₁1 : θ₁ ≤ 1 := by
    rw [hθ₁def, div_le_one (by positivity)]; linarith only [hK1]
  -- the cumulant regime `n ≤ c₁ log t` and the saddle regime `R ≥ c₁/2`
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = η / 2 := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have hρη : ρ < η := by rw [hρdef]; linarith
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁ : ℝ, c₁ = ρ / (4 * Real.exp (ρ * M / 2)) := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁def]; positivity
  have hc₁1 : c₁ ≤ 1 := by
    rw [hc₁def, div_le_one (by positivity)]
    have := Real.one_le_exp (by positivity : 0 ≤ ρ * M / 2)
    linarith
  obtain ⟨c, hcdef⟩ : ∃ c, c = c₁ / 2 * θ₁ ^ 2 / 5 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hθsq : θ₁ ^ 2 ≤ 1 := pow_le_one₀ hθ₁0.le hθ₁1
  have hc₁η : c₁ ≤ η := by
    rw [hc₁def, div_le_iff₀ (by positivity)]
    have h1 := Real.one_le_exp (by positivity : 0 ≤ ρ * M / 2)
    have h4 : η * 1 ≤ η * Real.exp (ρ * M / 2) := mul_le_mul_of_nonneg_left h1 hη.le
    linarith [hρdef]
  have hcη : c ≤ η := by
    rw [hcdef]
    have h1 := mul_le_mul_of_nonneg_left hθsq (by positivity : (0 : ℝ) ≤ c₁ / 2)
    nlinarith
  obtain ⟨A, hA0, htail⟩ := exists_shiftArc_tail_le (R₁ := R₁) hη (by linarith)
  have e1 := (tendsto_order.1 tendsto_rpow_half_mul_exp_neg_fifth_root).2 50 (by norm_num)
  have e3 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5))).2 θ₁ hθ₁0
  have e4 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5))).2
    (3 / (2 * (1 + 128 * K))) (by positivity)
  obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp (e1.and (e3.and e4))
  have e5 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) c hc0)).2
    (1 / (10 * Real.pi * (2 * A) * R₁ ^ (1 / 2 : ℝ))) (by positivity)
  obtain ⟨U₅, hU₅⟩ := Filter.eventually_atTop.mp e5
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hpi := Real.pi_pos
  have hRMη : 0 ≤ R₁ * M / η := by positivity
  have hEη : 0 ≤ E / η := by positivity
  have hΛ₀a := abs_nonneg Λ₀
  have hU₅a := abs_nonneg U₅
  have hΛη : 0 ≤ (|Λ₀| + 1) / (c₁ / 2) := by positivity
  obtain ⟨L, hLdef⟩ : ∃ L, L = 32 * R₁ + 16 + (|Λ₀| + 1) / (c₁ / 2)
      + 10 * (Real.log 2 + 2 * E + R₁ * M / η)
      + (Real.log (3 / 2) + Real.pi / 2 + 2 * E + R₁ * M / η) + E / η + |U₅| := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hLdef]; linarith
  refine ⟨Real.exp L, Real.one_le_exp hL0, ?_⟩
  intro t ht x₀ hx₀1 hx₀2 n hn1 hnhi
  have hx₀ : 0 ≤ x₀ := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos L) ht
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  rw [← hudef] at hnhi
  have hLu : L ≤ u := by
    rw [hudef, ← Real.log_exp L]; exact Real.log_le_log (Real.exp_pos L) ht
  have htu : u + 1 ≤ t := by
    have := Real.add_one_le_exp u
    rw [hudef, Real.exp_log ht0] at this; rw [hudef]; exact this
  rw [hLdef] at hLu
  have hu1 : 32 * R₁ + 16 ≤ u := by linarith only [hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0]
  have hu2 : (|Λ₀| + 1) / (c₁ / 2) ≤ u := by
    linarith only [hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu3 : 10 * (Real.log 2 + 2 * E + R₁ * M / η) ≤ u := by
    linarith only [hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu4 : Real.log (3 / 2) + Real.pi / 2 + 2 * E + R₁ * M / η ≤ u := by
    linarith only [hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu5 : E / η ≤ u := by
    linarith only [hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu6 : U₅ ≤ u := by
    have := le_abs_self U₅
    linarith only [this, hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu0 : 0 < u := by linarith only [hu1, hR₁0]
  have ht32 : 32 * R₁ + 16 ≤ t := by linarith only [hu1, htu]
  have ht8 : 8 ≤ t := by linarith only [ht32, hR₁0]
  have hR₁t : R₁ ≤ t / 2 := by linarith only [ht32, hR₁0]
  -- the cumulant regime
  have hEη8 : E = xiEulerConstant η := hEdef
  obtain ⟨him, hh₁lo, -⟩ := xiSliceLogDeriv_real_bounds_euler (t := t) (R := x₀) hη ht8
    (by linarith only [hx₀1, hη]) (by linarith only [hx₀2, hR₁t, hR₁def])
  rw [← hEdef] at hh₁lo
  rw [Real.log_div ht0.ne' (by norm_num), ← hudef] at hh₁lo
  have hh₁u : u / 2 ≤ (xiSliceLogDeriv t x₀).re := by linarith only [hh₁lo, hu3, hRMη, hl2, hE0]
  have hh₁pos : 0 < (xiSliceLogDeriv t x₀).re := by linarith only [hh₁u, hu0]
  by_cases hsmall : (n : ℝ) ≤ c₁ * u
  · have hcum := iteratedDeriv_xiSliceProduct_ge_cumulant (t := t) (η := η) (x := x₀) (ρ := ρ)
      hη (by linarith) ht8 (by linarith only [hx₀1, hη])
      (by linarith only [hx₀2, hR₁t, hR₁def]) hρ hρη hh₁pos n (by
        rw [← hEdef, ← hMdef]
        calc (n : ℝ) ≤ c₁ * u := hsmall
          _ = u / 2 * ρ / (2 * Real.exp (ρ * M / 2)) := by rw [hc₁def]; field_simp; ring
          _ ≤ (xiSliceLogDeriv t x₀).re * ρ / (2 * Real.exp (ρ * M / 2)) := by gcongr)
    have hfact : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hre : (((n.factorial : ℂ))⁻¹ * iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ)).re
        = (iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ)).re / n.factorial := by
      rw [show ((n.factorial : ℂ))⁻¹ = (((n.factorial : ℝ))⁻¹ : ℝ) by push_cast; rfl,
        Complex.re_ofReal_mul]
      ring
    rw [hre, ← hEη8]
    have hL'le : Real.log (t / 2) - 2 * E ≤ (xiSliceLogDeriv t x₀).re := by
      rw [Real.log_div ht0.ne' (by norm_num), ← hudef]; exact hh₁lo
    have hL'0 : 0 ≤ Real.log (t / 2) - 2 * E := by
      rw [Real.log_div ht0.ne' (by norm_num), ← hudef]
      linarith only [hu3, hRMη, hl2, hE0]
    have hpow : (Real.log (t / 2) - 2 * E) ^ n ≤ (xiSliceLogDeriv t x₀).re ^ n :=
      pow_le_pow_left₀ hL'0 hL'le n
    have hγ : 1 / (40 * Real.pi * Real.sqrt (2 * Real.log t)) ≤ 1 / 2 := by
      have h1 : 1 ≤ Real.sqrt (2 * Real.log t) := by
        rw [Real.one_le_sqrt]; rw [← hudef]; linarith only [hu1, hR₁0]
      have hpi3 := Real.pi_gt_three
      have h2 : 40 * Real.pi * 1 ≤ 40 * Real.pi * Real.sqrt (2 * Real.log t) :=
        mul_le_mul_of_nonneg_left h1 (by linarith only [hpi3])
      rw [div_le_div_iff₀ (by linarith only [h2, hpi3]) (by norm_num)]
      linarith only [h2, hpi3]
    have hS := xiSliceReal_nonneg t x₀
    calc xiSliceReal t x₀ * (Real.log (t / 2) - 2 * E) ^ n / n.factorial
          * (1 / (40 * Real.pi * Real.sqrt (2 * Real.log t)))
        ≤ xiSliceReal t x₀ * (xiSliceLogDeriv t x₀).re ^ n / n.factorial * (1 / 2) := by
          gcongr
      _ = xiSliceReal t x₀ * (xiSliceLogDeriv t x₀).re ^ n / 2 / n.factorial := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hcum hfact.le
  push Not at hsmall
  -- the saddle regime: radius in `[c₁/2, 2]`
  set a : ℝ := c₁ / 2 with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by rw [ha]; linarith only [hc₁1]
  have hlo : a * (Real.log t + 2 * xiEulerConstant η) ≤ n := by
    rw [← hudef, ← hEdef]
    have h1 : 8 * E ≤ u := by
      have := hu5
      rw [div_le_iff₀ hη] at this
      nlinarith only [this, hη8, hu0, hE0]
    have h2 : a * (2 * E) ≤ a * (u / 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [h1, hE0]) ha0.le
    have h3 : a * (u + 2 * E) = a * u + a * (2 * E) := by ring
    have h4 : a * u + a * (u / 2) ≤ c₁ * u := by
      have hcu := mul_nonneg hc₁0.le hu0.le
      have e : a * u + a * (u / 2) = 3 / 4 * (c₁ * u) := by rw [ha]; ring
      rw [e]
      linarith only [hcu]
    linarith only [h2, h3, h4, hsmall]
  have hhi : (n : ℝ) ≤ 2 * (Real.log (t / 2) - 2 * xiEulerConstant η) := by
    rw [Real.log_div ht0.ne' (by norm_num), ← hudef, ← hEdef]
    have h1 : 2 * (Real.log 2 + 2 * E) ≤ u := by linarith only [hu3, hRMη, hl2, hE0]
    linarith only [h1, hnhi]
  obtain ⟨R, ⟨hRa', hRb'⟩, hsad⟩ := exists_saddle_radius_shift (t := t) (n := n) hη ht8
    (by linarith only [hx₀1, ha0, hη] : 1 / 2 + η ≤ x₀ + a) ha0.le
    (by linarith only [ha1] : a ≤ 2)
    (by linarith only [hx₀2, hR₁t, hR₁def] : x₀ + 2 ≤ t / 2) hlo hhi
  have hR0 : 0 < R := by linarith only [hRa', ha0]
  have hRa : 1 / 2 + 2 * η ≤ x₀ + R := by linarith only [hx₀1, hR0]
  have hRb : x₀ + R ≤ R₁ := by linarith only [hRb', hx₀2, hR₁def]
  have hRt : x₀ + R ≤ t / 2 := le_trans hRb hR₁t
  have hRR₁ : R ≤ R₁ := by linarith only [hRb, hx₀]
  -- the slope
  obtain ⟨hF₁lo, hF₁hi⟩ := xiSliceShift_saddleSlope_bounds (t := t) (x₀ := x₀) (R := R) hη
    (by linarith only [hη8]) ht8 hR0 hRa hRt
  rw [← hEdef, ← hMdef] at hF₁lo hF₁hi
  have hRM : R * M / η ≤ R₁ * M / η :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRR₁ hM0.le) hη.le
  rw [Real.log_div ht0.ne' (by norm_num), ← hudef] at hF₁lo
  rw [← hudef] at hF₁hi
  have hF₁lo' : 9 / 10 * u ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re := by
    linarith only [hF₁lo, hRM, hu3]
  have hF₁hi' : (deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re ≤ 2 * u := by
    linarith only [hF₁hi, hRM, hu3, hl2, hRMη, hE0]
  -- the disc constant
  have hKd : xiSliceDiscConstantEuler η t R ≤ 2 * η * u := by
    unfold xiSliceDiscConstantEuler
    rw [← hEdef, ← hMdef]
    have e : Real.log (3 * t / 2) = Real.log (3 / 2) + u := by
      rw [show 3 * t / 2 = 3 / 2 * t by ring, Real.log_mul (by norm_num) ht0.ne', hudef]
    rw [e]
    have h1 : η * (R₁ * M / η) = R₁ * M := by field_simp
    have h2 := mul_le_mul_of_nonneg_left hu4 hη.le
    have h3 : R * M ≤ R₁ * M := mul_le_mul_of_nonneg_right hRR₁ hM0.le
    linarith only [h1, h2, h3]
  -- the tail on `[1/(1000K), π]`
  have htail' : ∀ θ : ℝ, 1 / (1000 * K) ≤ θ → θ ≤ Real.pi →
      ‖HTGeometry.saddleArc (xiSliceShift t x₀) R n θ‖ ≤ 2 * A * t ^ (-c) := by
    intro θ hθ hθπ
    rw [← hθ₁def] at hθ
    have hd := min_le_shift_decay (x₀ := x₀) hR0.le hθ₁0 hθ hθπ
    have h := htail t x₀ R θ _ n ht32 hx₀ hR0.le hRa hRb hd
    have hcd : c ≤ min (R * θ₁ ^ 2 / 5) (2 * x₀) := by
      refine le_min ?_ ?_
      · rw [hcdef]
        have h2R : a ≤ R := hRa'
        have := mul_le_mul_of_nonneg_right h2R (sq_nonneg θ₁)
        linarith only [this]
      · linarith only [hcη, hη, hx₀1]
    have h1 : t ^ (-min (R * θ₁ ^ 2 / 5) (2 * x₀)) ≤ t ^ (-c) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [ht8]) (by linarith only [hcd])
    have h2 : t ^ (-η) ≤ t ^ (-c) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [ht8]) (by linarith only [hcη])
    calc _ ≤ A * (t ^ (-η) + t ^ (-min (R * θ₁ ^ 2 / 5) (2 * x₀))) := h
      _ ≤ A * (t ^ (-c) + t ^ (-c)) :=
          mul_le_mul_of_nonneg_left (by linarith only [h1, h2]) hA0.le
      _ = 2 * A * t ^ (-c) := by ring
  -- the scale conditions
  have hΛlo : a * u ≤ R * u :=
    mul_le_mul_of_nonneg_right hRa' hu0.le
  have hΛhi : R * u ≤ R₁ * u := mul_le_mul_of_nonneg_right hRR₁ hu0.le
  have hηu : |Λ₀| + 1 ≤ a * u := by
    have := hu2
    rw [div_le_iff₀ (by positivity)] at this
    linarith only [this]
  have hΛbig : max Λ₀ 1 ≤ R * u :=
    max_le (by have := le_abs_self Λ₀; linarith only [this, hΛlo, hηu])
      (by linarith only [hΛlo, hηu, hΛ₀a])
  obtain ⟨hE1, hE3, hE4⟩ := hΛ₀ (R * u) (le_trans (le_max_left _ _) hΛbig)
  rw [hθ₁def] at hE3
  have hEt0 := tail_budget_le (A := 2 * A) (by positivity) hR₁0 ht0 hudef hu0
    (by linarith only [hΛbig, le_max_right Λ₀ 1]) hΛhi (hU₅ u hu6).le
  have hEt : Real.pi * (2 * A * t ^ (-c)) ≤ (R * u) ^ (-(1 / 2) : ℝ) / 10 := by
    calc Real.pi * (2 * A * t ^ (-c)) = Real.pi / 2 * (2 * (2 * A) * t ^ (-c)) := by ring
      _ ≤ _ := hEt0
  have hq := iteratedDeriv_xiSliceProduct_ge_of_saddle_shift hη hη8 hR₁ hKdef ht8 hu0 hx₀ hR0 hRa
    hRb hRt hsad hF₁lo' hF₁hi' hKd htail' (le_trans (le_max_right _ _) hΛbig) hE1 hE3 hE4 hEt
  -- convert `S(x₀+R)/Rⁿ` into `S(x₀) L'ⁿ/n!`
  set L' : ℝ := Real.log (t / 2) - 2 * E with hL'def
  have hL'pos : 0 < L' := by
    rw [hL'def, Real.log_div ht0.ne' (by norm_num), ← hudef]
    linarith only [hu3, hRMη, hl2, hE0]
  have hgrow := (xiSliceReal_growth_euler (t := t) hη ht8 (y₁ := x₀) (y₂ := x₀ + R)
    (by linarith only [hx₀1, hη]) (by linarith only [hR0]) hRt).1
  rw [← hEdef, show x₀ + R - x₀ = R by ring] at hgrow
  have hSx₀ : 0 ≤ xiSliceReal t x₀ := xiSliceReal_nonneg t x₀
  have hexpR := pow_mul_exp_le_exp (mul_nonneg hL'pos.le hR0.le) hn1
  have hnn : ((n : ℝ) ^ n) / n.factorial ≤ Real.exp n :=
    Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hfact : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hRn : 0 < R ^ n := pow_pos hR0 n
  have hkey : xiSliceReal t x₀ * L' ^ n / n.factorial ≤ xiSliceReal t (x₀ + R) / R ^ n := by
    have h1 : L' ^ n / n.factorial ≤ Real.exp (L' * R) / R ^ n := by
      have e1 : (Real.exp 1 * (L' * R) / n) ^ n = Real.exp n * L' ^ n * R ^ n / (n : ℝ) ^ n := by
        rw [div_pow, mul_pow, mul_pow, ← Real.exp_nat_mul, mul_one]
        ring
      rw [e1] at hexpR
      rw [le_div_iff₀ hRn]
      have h2 : L' ^ n / n.factorial * R ^ n ≤ Real.exp n * L' ^ n * R ^ n / (n : ℝ) ^ n := by
        have h3 : 1 / n.factorial ≤ Real.exp n / (n : ℝ) ^ n := by
          rw [div_le_div_iff₀ hfact (by positivity), one_mul]
          rw [div_le_iff₀ hfact] at hnn
          linarith
        have h4 : 0 ≤ L' ^ n * R ^ n := by positivity
        calc L' ^ n / n.factorial * R ^ n = (L' ^ n * R ^ n) * (1 / n.factorial) := by ring
          _ ≤ (L' ^ n * R ^ n) * (Real.exp n / (n : ℝ) ^ n) := mul_le_mul_of_nonneg_left h3 h4
          _ = Real.exp n * L' ^ n * R ^ n / (n : ℝ) ^ n := by ring
      linarith
    calc xiSliceReal t x₀ * L' ^ n / n.factorial
        = xiSliceReal t x₀ * (L' ^ n / n.factorial) := by ring
      _ ≤ xiSliceReal t x₀ * (Real.exp (L' * R) / R ^ n) := mul_le_mul_of_nonneg_left h1 hSx₀
      _ = xiSliceReal t x₀ * Real.exp (L' * R) / R ^ n := by ring
      _ ≤ xiSliceReal t (x₀ + R) / R ^ n := by
          apply div_le_div_of_nonneg_right _ hRn.le
          rw [hL'def]; linarith only [hgrow]
  have hΛ2 : 1 / Real.sqrt (2 * Real.log t) ≤ (R * u) ^ (-(1 / 2) : ℝ) := by
    rw [← hudef, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
    exact inv_anti₀ (Real.sqrt_pos.mpr (by positivity))
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hRb' hu0.le))
  have hL'eq : L' = Real.log (t / 2) - 2 * xiEulerConstant η := by
    rw [hL'def, hEdef]
  rw [← hL'eq]
  calc xiSliceReal t x₀ * L' ^ n / n.factorial * (1 / (40 * Real.pi * Real.sqrt (2 * Real.log t)))
      = xiSliceReal t x₀ * L' ^ n / n.factorial / Real.pi
        * ((1 / Real.sqrt (2 * Real.log t)) / 40) := by
        field_simp
    _ ≤ xiSliceReal t (x₀ + R) / R ^ n / Real.pi * ((R * u) ^ (-(1 / 2) : ℝ) / 40) := by
        have hSR := xiSliceReal_nonneg t (x₀ + R)
        have h0 : 0 ≤ xiSliceReal t (x₀ + R) / R ^ n / Real.pi := by positivity
        gcongr
    _ = xiSliceReal t (x₀ + R) / (Real.pi * R ^ n) * ((R * u) ^ (-(1 / 2) : ℝ) / 40) := by
        field_simp
    _ ≤ _ := hq

/-- **Lower bound for the slice derivatives at Euler points `x₀ ∈ [3/4, 2]`.** -/
theorem exists_iteratedDeriv_xiSliceProduct_ge_euler_near_edge :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ x₀ : ℝ, 3 / 4 ≤ x₀ → x₀ ≤ 2 → ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ≤ Real.log t →
      xiSliceReal t x₀ * (Real.log (t / 2) - 2 * xiEulerConstant (1 / 8)) ^ n / n.factorial
          * (1 / (40 * Real.pi * Real.sqrt (2 * Real.log t)))
        ≤ (((n.factorial : ℂ))⁻¹ * iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ)).re := by
  obtain ⟨t₀, ht₀, h⟩ := exists_iteratedDeriv_xiSliceProduct_ge_euler_from (η := 1 / 8)
    (by norm_num) le_rfl
  exact ⟨t₀, ht₀, fun t ht x₀ hx₀ hx₀2 n hn hnt => h t ht x₀ (by linarith) hx₀2 n hn hnt⟩

end

end RHTower
