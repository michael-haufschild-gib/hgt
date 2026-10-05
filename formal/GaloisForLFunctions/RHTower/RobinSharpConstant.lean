import GaloisForLFunctions.RHTower.RobinCriterionRiemann

/-!
# Robin's sharp constant

Under the Riemann hypothesis, with `D(n) = log(σ(n)/n) - γ - log log log n` and
`κ = a₁ + 2 - 2√2` (`a₁ = 2 + γ - log 4π` the sharp ceiling of the lag function),
`limsup_n D(n) √(log n) log log n = κ`.

At the extremal numbers `N_x` the exponents switch from `≥ 2` to `1` at `√(2x)`: below `c₁√x`
(`c₁ < √2`) every exponent is at least two and above `c₂√x` (`c₂ > √2`) it is one.  The scaled
Robin defect at `N_x` is then `Φ(log x) + 1 + 1 - (c₁ + 2/c₂) + o(1)` from above and
`Φ(log x) + 1 + 1 - (c₂ + 2/c₁) - o(1)` from below, where the two `1`s come from the prime
tails of the Euler product and from the prime squares in `ψ - θ`, `c` from `θ(c√x) ~ c√x` and
`2/c` from `Σ_{c√x<p≤x} p^{-2} ~ 2/(c√x log x)`.  General `n` reduce to `N_x` through the
Lagrangian bound, and the ceiling `a₁` is approached along primes.
-/

open MeasureTheory Set Filter Topology
open ArithmeticFunction (sigma)
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The Robin defect `log(σ(N_x)/N_x) - γ - log log log N_x` at the extremal number. -/
def robinExtremalDefect (x : ℝ) : ℝ :=
  Real.log ((sigma 1 (robinExtremalAt x) : ℝ) / (robinExtremalAt x : ℝ))
    - Real.eulerMascheroniConstant - Real.log (Real.log (Real.log (robinExtremalAt x : ℝ)))

/-- `c₁ = √2 - η` and `c₂ = √2 + η` give `c₁ + 2/c₂ ≥ 2√2 - 2η` and `c₂ + 2/c₁ ≤ 2√2 + 3η`. -/
theorem sqrt_two_split_bounds {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) :
    2 * Real.sqrt 2 - 2 * η ≤ (Real.sqrt 2 - η) + 2 / (Real.sqrt 2 + η)
      ∧ (Real.sqrt 2 + η) + 2 / (Real.sqrt 2 - η) ≤ 2 * Real.sqrt 2 + 3 * η := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor
  · have h1 : Real.sqrt 2 - η ≤ 2 / (Real.sqrt 2 + η) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    linarith
  · have h1 : 2 / (Real.sqrt 2 - η) ≤ Real.sqrt 2 + 2 * η := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith

/-- **The sharp upper bound at `N_x` under RH.**  For every `ε > 0`, eventually
`D(N_x) √x log x ≤ Φ(log x) + 2 - 2√2 + ε`. -/
theorem eventually_robinExtremalDefect_scaled_le (hRH : RiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, robinExtremalDefect x * (Real.sqrt x * Real.log x)
      ≤ weilLagFunctionReal (Real.log x) + 2 - 2 * Real.sqrt 2 + ε := by
  obtain ⟨K, hK, hθK⟩ := exists_abs_theta_sub_le_of_riemannHypothesis hRH
  set η := min (ε / 8) (1 / 4) with hηdef
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hη4 : η ≤ 1 / 4 := min_le_right _ _
  have hηε : η ≤ ε / 8 := min_le_left _ _
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs3 : 7 / 5 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  set c₁ := Real.sqrt 2 - η with hc₁
  set c₂ := Real.sqrt 2 + η with hc₂
  have hc₁1 : 1 ≤ c₁ := by rw [hc₁]; linarith
  have hc₁sq : c₁ ^ 2 < 2 := by rw [hc₁]; nlinarith
  have hc₂1 : 1 ≤ c₂ := by rw [hc₂]; linarith
  have hc₂sq : 2 < c₂ ^ 2 := by rw [hc₂]; nlinarith
  have hsplit := (sqrt_two_split_bounds hη0 hη4).1
  have E3 := (tendsto_order.1 (tendsto_mertensProductError_sub_scaled hRH)).2 (1 + ε / 8)
    (by linarith)
  have E4 := (tendsto_order.1 (tendsto_mertensErrorRemainder_scaled_sub_lag hRH)).2 (ε / 8)
    (by linarith)
  have E5 := (tendsto_order.1 (tendsto_psi_sub_theta_div_sqrt hRH)).2 (1 + ε / 8) (by linarith)
  have E6 := (tendsto_order.1 (tendsto_theta_mul_sqrt_div (c := c₁) (by linarith))).1
    (c₁ - ε / 8) (by linarith)
  have E7 := eventually_sum_prime_inv_sq_scaled_ge (c := c₂) (δ := ε / 8) hc₂1 (by positivity)
  have E8 := (tendsto_order.1 ((tendsto_log_pow_div_rpow_atTop 4 (r := 1 / 2)
    (by norm_num)).const_mul (35 / 4 * (K + 4) ^ 2))).2 (ε / 8) (by simpa using by positivity)
  have E9 : ∀ᶠ x : ℝ in atTop, 2 * x + 3 < c₂ ^ 2 * x := by
    filter_upwards [eventually_gt_atTop (3 / (c₂ ^ 2 - 2))] with x hx
    have h0 : 0 < c₂ ^ 2 - 2 := by linarith
    rw [div_lt_iff₀ h0] at hx
    nlinarith
  filter_upwards [eventually_two_le_robinExponent_mul hc₁1 hc₁sq, eventually_ge_atTop (10000 : ℝ),
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop c₁), E3, E4, E5, E6, E7, E8, E9,
    eventually_two_fifths_le_theta] with x h2 hx hsx e3 e4 e5 e6 e7 e8 e9 e10
  have hb := robinDefect_robinExtremalAt_scaled_le hx (by linarith) hsx hc₂1 e9 h2 e10
    (hθK x (by linarith))
  unfold robinExtremalDefect
  linarith only [hb, e3, e4, e5, e6, e7, e8, hsplit, hηε]


/-- The Robin defect `D(n) = log(σ(n)/n) - γ - log log log n`. -/
def robinDefectOf (n : ℕ) : ℝ :=
  Real.log ((sigma 1 n : ℝ) / (n : ℝ)) - Real.eulerMascheroniConstant
    - Real.log (Real.log (Real.log n))

/-- **Reduction to an extremal number.**  If `ℓ = log n > 1`, `x > 1`, `ε(x) = 1/(ℓ log ℓ)` and
`log N_x > 1`, then `D(n) ≤ D(N_x)`. -/
theorem robinDefectOf_le_robinExtremalDefect {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x)
    (hℓ : 1 < Real.log n)
    (hxε : robinParameter x = 1 / (Real.log n * Real.log (Real.log n)))
    (hN : 1 < Real.log (robinExtremalAt x : ℝ)) :
    robinDefectOf n ≤ robinExtremalDefect x := by
  set ℓ := Real.log n with hℓdef
  have hlℓ := Real.log_pos hℓ
  set ε := 1 / (ℓ * Real.log ℓ) with hεdef
  have hB : ∀ p : ℕ, p.Prime → ⌊x⌋₊ < p → robinExponent (robinParameter x) p = 0 :=
    fun p hp hpx => robinExponent_eq_zero_of_floor_lt hx hp hpx
  have hlag := log_sigma_div_sub_le_robinExtremal (robinParameter_pos hx) hB
    (show n ≠ 0 by omega)
  rw [← robinExtremalAt, hxε] at hlag
  have hmis := log_log_sub_log_log_le hℓ hN
  have e : (Real.log (robinExtremalAt x : ℝ) - ℓ) / (ℓ * Real.log ℓ)
      = ε * (Real.log (robinExtremalAt x : ℝ) - ℓ) := by rw [hεdef]; ring
  rw [e] at hmis
  unfold robinDefectOf robinExtremalDefect
  rw [← hℓdef]
  linarith

theorem kappa_neg : poleSharpConstant + 2 - 2 * Real.sqrt 2 < 0 := by
  have ha3 := poleSharpConstant_lt_three_tenths
  have hs3 : 7 / 5 < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

/-- **Robin's constant, upper half.**  Under RH, for every `ε > 0`, eventually
`D(n) √(log n) log log n ≤ a₁ + 2 - 2√2 + ε`. -/
theorem eventually_robinDefectOf_scaled_le (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, robinDefectOf n * (Real.sqrt (Real.log n) * Real.log (Real.log n))
      ≤ poleSharpConstant + 2 - 2 * Real.sqrt 2 + ε := by
  have hκ := kappa_neg
  set ε' := min ε ((-(poleSharpConstant + 2 - 2 * Real.sqrt 2)) / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by linarith)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'κ : poleSharpConstant + 2 - 2 * Real.sqrt 2 + ε' < 0 := by
    have := min_le_right ε ((-(poleSharpConstant + 2 - 2 * Real.sqrt 2)) / 2); linarith
  have hΦ : ∀ L : ℝ, weilLagFunctionReal L ≤ poleSharpConstant := fun L => by
    have := norm_weilLagFunction_le_of_riemannHypothesis hRH L
    rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp ((eventually_robinExtremalDefect_scaled_le hRH hε'0).and
    ((eventually_ge_atTop (100 : ℝ)).and eventually_two_fifths_le_theta))
  set X := max X₀ 100 with hX
  have hX1 : 1 < X := by linarith [le_max_right X₀ 100]
  have hεX := robinParameter_pos hX1
  have hℓ : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ => 1 / (Real.log n * Real.log (Real.log n))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hℓ.atTop_mul_atTop₀ (Real.tendsto_log_atTop.comp hℓ))
  filter_upwards [hsmall.eventually (ge_mem_nhds hεX), hℓ.eventually (eventually_ge_atTop X),
    eventually_ge_atTop 1] with n hn1 hn2 hn3
  set ℓ := Real.log n with hℓdef
  have hℓ1 : 1 < ℓ := by linarith [le_max_right X₀ 100]
  have hmem : 1 / (ℓ * Real.log ℓ) ∈ Icc (robinParameter ℓ) (robinParameter X) :=
    ⟨robinParameter_le hℓ1, hn1⟩
  obtain ⟨x, ⟨hXx, hxℓ⟩, hxε⟩ :=
    intermediate_value_Icc' hn2 (continuousOn_robinParameter hX1) hmem
  have hx1 : 1 < x := by linarith
  obtain ⟨hD, hx100, hx25⟩ := hX₀ x (le_trans (le_max_left _ _) hXx)
  have hu1 : 1 < Real.log (robinExtremalAt x : ℝ) := by
    have := theta_le_log_robinExtremalAt hx1; linarith
  have hred := robinDefectOf_le_robinExtremalDefect hn3 hx1 hℓ1 hxε hu1
  have hΦx := hΦ (Real.log x)
  have hDx : robinExtremalDefect x * (Real.sqrt x * Real.log x)
      ≤ poleSharpConstant + 2 - 2 * Real.sqrt 2 + ε' := by linarith
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hDneg : robinExtremalDefect x < 0 := by
    by_contra hc
    push Not at hc
    have : 0 ≤ robinExtremalDefect x * (Real.sqrt x * Real.log x) := by positivity
    linarith
  have hscale : Real.sqrt x * Real.log x ≤ Real.sqrt ℓ * Real.log ℓ :=
    mul_le_mul (Real.sqrt_le_sqrt hxℓ) (Real.log_le_log hx0 hxℓ) hlx.le (Real.sqrt_nonneg _)
  have hℓ0 : 0 ≤ Real.sqrt ℓ * Real.log ℓ := by
    have := Real.log_pos hℓ1; positivity
  calc robinDefectOf n * (Real.sqrt ℓ * Real.log ℓ)
      ≤ robinExtremalDefect x * (Real.sqrt ℓ * Real.log ℓ) :=
        mul_le_mul_of_nonneg_right hred hℓ0
    _ ≤ robinExtremalDefect x * (Real.sqrt x * Real.log x) :=
        mul_le_mul_of_nonpos_left hscale hDneg.le
    _ ≤ _ := by linarith


/-! ## The lower half at the extremal numbers -/

/-- `Q_p(ε(x)) ≤ 3x log x` for every prime `p`, `x ≥ 16`. -/
theorem robinThreshold_le_three_mul {x : ℝ} (hx : 16 ≤ x) {p : ℕ} (hp : p.Prime) :
    robinThreshold (robinParameter x) p ≤ 3 * x * Real.log x := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hε := robinParameter_pos hx1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlp := Real.log_pos hp1
  have hlx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  unfold robinThreshold
  set ε := robinParameter x
  have hd : ε * Real.log p ≤ (p : ℝ) ^ ε - 1 := by
    rw [Real.rpow_def_of_pos (by linarith), mul_comm (Real.log p) ε]
    have := Real.add_one_le_exp (ε * Real.log p); linarith
  have hd0 : 0 < ε * Real.log p := mul_pos hε hlp
  have h2 : (1 - 1 / (p : ℝ)) / ((p : ℝ) ^ ε - 1) ≤ 1 / (ε * Real.log p) := by
    rw [div_le_div_iff₀ (lt_of_lt_of_le hd0 hd) hd0]
    have : 0 ≤ 1 / (p : ℝ) := by positivity
    nlinarith
  have h3 : 1 / (ε * Real.log p) ≤ (x + 1) * Real.log x / Real.log 2 := by
    have hl2 : Real.log 2 ≤ Real.log p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
    have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hεl := le_robinParameter hx1
    rw [div_le_div_iff₀ hd0 hl20]
    have := mul_le_mul hεl hl2 hl20.le hε.le
    have e : 1 / ((x + 1) * Real.log x) * Real.log 2 * ((x + 1) * Real.log x) = Real.log 2 := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_right this (show 0 ≤ (x + 1) * Real.log x by positivity)]
  have h4 : (x + 1) * Real.log x / Real.log 2 ≤ 2 * (x + 1) * Real.log x := by
    have hl2 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ (x + 1) * Real.log x := by positivity
    nlinarith
  nlinarith

/-- **The size of `N_x` from above, sharply.**  If `a_p = 1` beyond `c√x ≤ x` (`2x + 3 < c²x`,
`c ≥ 1`) and `x ≥ 10000`, then `log N_x ≤ θ(x) + θ(c√x) + 2 log x (2x^{1/3} log x + 1)`. -/
theorem log_robinExtremalAt_le {x c : ℝ} (hx : 10000 ≤ x) (hc : 1 ≤ c)
    (hcx : 2 * x + 3 < c ^ 2 * x) (hyx : c * Real.sqrt x ≤ x) :
    Real.log (robinExtremalAt x : ℝ) ≤ Chebyshev.theta x + Chebyshev.theta (c * Real.sqrt x)
      + 2 * Real.log x * (2 * x ^ ((1 : ℝ) / 3) * Real.log x + 1) := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hε := robinParameter_pos hx1
  have hlx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  set z := 2 * x ^ ((1 : ℝ) / 3) * Real.log x with hz
  have hz0 : 0 ≤ z := by positivity
  set F := (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime with hF
  have hθx : Chebyshev.theta x = ∑ p ∈ F, Real.log p := Chebyshev.theta_eq_sum_Icc x
  have hθy := (sum_filter_le_log_eq_theta (by positivity : (0 : ℝ) ≤ c * Real.sqrt x) hyx).symm
  rw [Finset.sum_filter] at hθy
  have hcube : 3 * x * Real.log x ≤ z ^ 3 := by
    have h1 : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    have h2 : z ^ 3 = 8 * x * Real.log x ^ 3 := by rw [hz, mul_pow, mul_pow, h1]; ring
    rw [h2]
    have h3 : Real.log x ≤ Real.log x ^ 3 := by
      have : 1 ≤ Real.log x ^ 2 := by nlinarith
      calc Real.log x = Real.log x * 1 := by ring
        _ ≤ Real.log x * Real.log x ^ 2 := mul_le_mul_of_nonneg_left this (by linarith)
        _ = Real.log x ^ 3 := by ring
    have h4 : 0 ≤ x * Real.log x := by positivity
    calc 3 * x * Real.log x ≤ 8 * (x * Real.log x) := by linarith
      _ ≤ 8 * (x * Real.log x ^ 3) := by
          have := mul_le_mul_of_nonneg_left h3 hx0.le
          linarith
      _ = 8 * x * Real.log x ^ 3 := by ring
  have hterm : ∀ p ∈ F, ((robinExponent (robinParameter x) p : ℝ) - 1) * Real.log p
      ≤ (if (p : ℝ) ≤ c * Real.sqrt x then Real.log p else 0)
        + (if (p : ℝ) ≤ z then 2 * Real.log x else 0) := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hpx : (p : ℝ) ≤ x := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
      exact (Nat.le_floor_iff (by linarith)).mp this
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hlp := Real.log_pos hp1
    have h1 : 1 ≤ robinExponent (robinParameter x) p :=
      (one_le_robinExponent_iff_le hx1 hpp).mpr hpx
    have hnn1 : 0 ≤ (if (p : ℝ) ≤ c * Real.sqrt x then Real.log p else 0) := by
      split_ifs <;> linarith
    have hnn2 : 0 ≤ (if (p : ℝ) ≤ z then 2 * Real.log x else 0) := by
      split_ifs <;> linarith
    by_cases hbig : c * Real.sqrt x < p
    · have h3 := robinExponent_le_one_of_gt_mul hc hx1 hcx hpp hbig
      have : (robinExponent (robinParameter x) p : ℝ) = 1 := by
        have : robinExponent (robinParameter x) p = 1 := by omega
        exact_mod_cast this
      rw [this, sub_self, zero_mul]
      linarith
    · push Not at hbig
      rw [if_pos hbig]
      by_cases h3 : robinExponent (robinParameter x) p ≤ 2
      · have : (robinExponent (robinParameter x) p : ℝ) - 1 ≤ 1 := by
          have : (robinExponent (robinParameter x) p : ℝ) ≤ 2 := by exact_mod_cast h3
          linarith
        have := mul_le_mul_of_nonneg_right this hlp.le
        linarith
      · push Not at h3
        have hpow := (le_robinExponent_iff hε hpp _).mp
          (le_refl (robinExponent (robinParameter x) p))
        have hQ := robinThreshold_le_three_mul (x := x) (by linarith) hpp
        have hp3 : (p : ℝ) ^ 3 ≤ 3 * x * Real.log x := by
          have := (le_robinExponent_iff hε hpp 3).mp (by omega)
          linarith
        have hpz : (p : ℝ) ≤ z := by
          by_contra hc'
          push Not at hc'
          have := pow_lt_pow_left₀ hc' hz0 (by norm_num : (3 : ℕ) ≠ 0)
          linarith
        rw [if_pos hpz]
        have hlog : (robinExponent (robinParameter x) p : ℝ) * Real.log p ≤ 2 * Real.log x := by
          rw [← Real.log_pow]
          have h5 : (p : ℝ) ^ robinExponent (robinParameter x) p ≤ x ^ 2 := by
            refine hpow.trans (hQ.trans ?_)
            have : Real.log x ≤ x / 3 := by
              have := Real.log_le_sub_one_of_pos hx0
              have h6 := Real.add_one_le_exp (Real.log x / 2)
              nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < Real.sqrt x by positivity),
                Real.log_sqrt hx0.le, Real.mul_self_sqrt hx0.le, Real.sqrt_nonneg x]
            nlinarith
          calc Real.log ((p : ℝ) ^ robinExponent (robinParameter x) p) ≤ Real.log (x ^ 2) :=
                Real.log_le_log (by positivity) h5
            _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
        nlinarith
  have hdiff : Real.log (robinExtremalAt x : ℝ) - Chebyshev.theta x
      = ∑ p ∈ F, ((robinExponent (robinParameter x) p : ℝ) - 1) * Real.log p := by
    rw [robinExtremalAt, log_robinExtremal, hθx, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hcard : ((F.filter (fun p : ℕ => (p : ℝ) ≤ z)).card : ℝ) ≤ z + 1 := by
    have hsub : F.filter (fun p : ℕ => (p : ℝ) ≤ z) ⊆ Finset.Icc 0 ⌊z⌋₊ := by
      intro p hp
      simp only [Finset.mem_filter] at hp
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor hp.2⟩
    have h1 := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h1
    have h2 : ((⌊z⌋₊ + 1 - 0 : ℕ) : ℝ) ≤ z + 1 := by
      rw [Nat.sub_zero]; push_cast; linarith [Nat.floor_le hz0]
    have h3 : ((F.filter (fun p : ℕ => (p : ℝ) ≤ z)).card : ℝ)
        ≤ ((⌊z⌋₊ + 1 - 0 : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← hθy, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul] at hsum
  have h2 : ((F.filter (fun p : ℕ => (p : ℝ) ≤ z)).card : ℝ) * (2 * Real.log x)
      ≤ 2 * Real.log x * (z + 1) := by
    have := mul_le_mul_of_nonneg_left hcard (show 0 ≤ 2 * Real.log x by positivity)
    linarith
  linarith


/-- **The exponent deficit from above.**  If `a_p ≥ 2` for `p ≤ c√x` (`c ≥ 1`, `x ≥ 16`), then
`E_N ≤ (1 + 2/(c²x)) Σ_{c√x<p≤x} p^{-2} + 8(1 + log x)/(x^{1/3})²`. -/
theorem robinDeficit_le {x c : ℝ} (hx : 16 ≤ x) (hc : 1 ≤ c)
    (h2 : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ c * Real.sqrt x →
      2 ≤ robinExponent (robinParameter x) p) :
    ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime,
        -Real.log (1 - (1 / (p : ℝ)) ^ (robinExponent (robinParameter x) p + 1))
      ≤ (1 + 2 / (c ^ 2 * x)) * ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter
          (fun p : ℕ => c * Real.sqrt x < p), 1 / (p : ℝ) ^ 2
        + 8 / (x ^ ((1 : ℝ) / 3)) ^ 2 * (1 + Real.log x) := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hε := robinParameter_pos hx1
  have hc0 : 0 < c := by linarith
  set F := (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime with hF
  set t := x ^ ((1 : ℝ) / 3) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hx0 _
  have ht3 : t ^ 3 = x := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  rw [← Finset.sum_filter_add_sum_filter_not F (fun p : ℕ => c * Real.sqrt x < p)]
  -- large primes
  have hlarge : ∑ p ∈ F.filter (fun p : ℕ => c * Real.sqrt x < p),
        -Real.log (1 - (1 / (p : ℝ)) ^ (robinExponent (robinParameter x) p + 1))
      ≤ (1 + 2 / (c ^ 2 * x)) * ∑ p ∈ F.filter (fun p : ℕ => c * Real.sqrt x < p),
          1 / (p : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hpF, hps⟩ := Finset.mem_filter.mp hp
    have hpp := (Finset.mem_filter.mp hpF).2
    have hpx : (p : ℝ) ≤ x := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpF).1).2
      exact (Nat.le_floor_iff (by linarith)).mp this
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have ha1 := (one_le_robinExponent_iff_le hx1 hpp).mpr hpx
    set y := (1 / (p : ℝ)) ^ (robinExponent (robinParameter x) p + 1) with hy
    have hq : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; linarith
    have hy0 : 0 ≤ y := by positivity
    have hyp : y ≤ (1 / (p : ℝ)) ^ 2 :=
      pow_le_pow_of_le_one (by positivity) hq (by omega)
    have hp2' : (1 / (p : ℝ)) ^ 2 ≤ 1 / 4 := by
      rw [div_pow, one_pow]; exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    have h1 := (neg_log_one_sub_mem (show y ≤ 1 / 2 by linarith)).2
    have hpsq : c ^ 2 * x < (p : ℝ) ^ 2 := by
      have h := mul_lt_mul'' hps hps (by positivity) (by positivity)
      have e : c * Real.sqrt x * (c * Real.sqrt x) = c ^ 2 * x := by
        rw [show c * Real.sqrt x * (c * Real.sqrt x) = c ^ 2 * (Real.sqrt x * Real.sqrt x) by
          ring, Real.mul_self_sqrt hx0.le]
      nlinarith
    have hy2 : 2 * y ^ 2 ≤ 2 / (c ^ 2 * x) * (1 / (p : ℝ) ^ 2) := by
      have h3 : y ^ 2 ≤ ((1 / (p : ℝ)) ^ 2) ^ 2 := pow_le_pow_left₀ hy0 hyp 2
      have h4 : ((1 / (p : ℝ)) ^ 2) ^ 2 ≤ 1 / (c ^ 2 * x) * (1 / (p : ℝ) ^ 2) := by
        have e1 : ((1 / (p : ℝ)) ^ 2) ^ 2 = 1 / ((p : ℝ) ^ 2 * (p : ℝ) ^ 2) := by field_simp
        rw [e1, one_div_mul_one_div]
        exact one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_right hpsq.le (by positivity))
      calc 2 * y ^ 2 ≤ 2 * (1 / (c ^ 2 * x) * (1 / (p : ℝ) ^ 2)) := by linarith
        _ = 2 / (c ^ 2 * x) * (1 / (p : ℝ) ^ 2) := by ring
    have hy1 : y ≤ 1 / (p : ℝ) ^ 2 := by rwa [div_pow, one_pow] at hyp
    calc -Real.log (1 - y) ≤ y + 2 * y ^ 2 := h1
      _ ≤ 1 / (p : ℝ) ^ 2 + 2 / (c ^ 2 * x) * (1 / (p : ℝ) ^ 2) := by linarith
      _ = (1 + 2 / (c ^ 2 * x)) * (1 / (p : ℝ) ^ 2) := by ring
  -- small primes
  have hsmall : ∑ p ∈ F.filter (fun p : ℕ => ¬ c * Real.sqrt x < p),
        -Real.log (1 - (1 / (p : ℝ)) ^ (robinExponent (robinParameter x) p + 1))
      ≤ 8 / t ^ 2 * (1 + Real.log x) := by
    have hterm : ∀ p ∈ F.filter (fun p : ℕ => ¬ c * Real.sqrt x < p),
        -Real.log (1 - (1 / (p : ℝ)) ^ (robinExponent (robinParameter x) p + 1))
          ≤ 8 / t ^ 2 * (1 / (p : ℝ)) := by
      intro p hp
      obtain ⟨hpF, hps⟩ := Finset.mem_filter.mp hp
      push Not at hps
      have hpp := (Finset.mem_filter.mp hpF).2
      have hpx : (p : ℝ) ≤ x := by
        have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpF).1).2
        exact (Nat.le_floor_iff (by linarith)).mp this
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      have hp0 : (0 : ℝ) < p := by linarith
      have ha2 := h2 p hpp hps
      set a := robinExponent (robinParameter x) p with ha
      have hY1 : x / 4 < (p : ℝ) ^ (a + 1) :=
        lt_of_le_of_lt (robinThreshold_ge hx hpp hpx) (robinThreshold_lt_pow hε hpp)
      have hY2 : (p : ℝ) ^ 3 ≤ (p : ℝ) ^ (a + 1) := pow_le_pow_right₀ hp1.le (by omega)
      have hYt : t ^ 2 / 4 * p ≤ (p : ℝ) ^ (a + 1) := by
        by_cases hpt : (p : ℝ) ≤ t / 2
        · calc t ^ 2 / 4 * p ≤ t ^ 2 / 4 * (t / 2) :=
                mul_le_mul_of_nonneg_left hpt (by positivity)
            _ = x / 8 := by rw [← ht3]; ring
            _ ≤ _ := by linarith
        · push Not at hpt
          have h3 : t ^ 2 / 4 ≤ (p : ℝ) ^ 2 := by nlinarith
          calc t ^ 2 / 4 * p ≤ (p : ℝ) ^ 2 * p := mul_le_mul_of_nonneg_right h3 hp0.le
            _ = (p : ℝ) ^ 3 := by ring
            _ ≤ _ := hY2
      set y := (1 / (p : ℝ)) ^ (a + 1) with hy
      have hy0 : 0 ≤ y := by positivity
      have hyY : y = 1 / (p : ℝ) ^ (a + 1) := by rw [hy, one_div_pow]
      have hyle : y ≤ 4 / t ^ 2 * (1 / (p : ℝ)) := by
        rw [hyY, show 4 / t ^ 2 * (1 / (p : ℝ)) = 1 / (t ^ 2 / 4 * p) by field_simp]
        exact one_div_le_one_div_of_le (by positivity) hYt
      have hq : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; linarith
      have hy12 : y ≤ 1 / 2 := by
        have : y ≤ (1 / (p : ℝ)) ^ 2 := pow_le_pow_of_le_one (by positivity) hq (by omega)
        have h4 : (1 / (p : ℝ)) ^ 2 ≤ 1 / 4 := by
          rw [div_pow, one_pow]
          exact one_div_le_one_div_of_le (by norm_num)
            (by have : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
                nlinarith)
        linarith
      have h1 := (neg_log_one_sub_mem hy12).2
      have h5 : y + 2 * y ^ 2 ≤ 2 * y := by nlinarith
      calc -Real.log (1 - y) ≤ 2 * y := h1.trans h5
        _ ≤ 2 * (4 / t ^ 2 * (1 / (p : ℝ))) := by linarith
        _ = 8 / t ^ 2 * (1 / (p : ℝ)) := by ring
    have hH : ∑ p ∈ F.filter (fun p : ℕ => ¬ c * Real.sqrt x < p), 1 / (p : ℝ)
        ≤ 1 + Real.log x := by
      have hsub : F.filter (fun p : ℕ => ¬ c * Real.sqrt x < p) ⊆ Finset.Icc 1 ⌊x⌋₊ := by
        intro p hp
        simp only [hF, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
        exact ⟨hp.1.2.one_lt.le, hp.1.1.2⟩
      have h1 := harmonic_le_one_add_log ⌊x⌋₊
      rw [harmonic_eq_sum_Icc] at h1
      have h2' : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
        Real.log_le_log (by exact_mod_cast Nat.floor_pos.mpr (by linarith)) (Nat.floor_le hx0.le)
      have h3 : ∑ p ∈ F.filter (fun p : ℕ => ¬ c * Real.sqrt x < p), 1 / (p : ℝ)
          ≤ ∑ i ∈ Finset.Icc 1 ⌊x⌋₊, 1 / (i : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
      linarith
    calc _ ≤ ∑ p ∈ F.filter (fun p : ℕ => ¬ c * Real.sqrt x < p), 8 / t ^ 2 * (1 / (p : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = 8 / t ^ 2 * ∑ p ∈ F.filter (fun p : ℕ => ¬ c * Real.sqrt x < p), 1 / (p : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ 8 / t ^ 2 * (1 + Real.log x) := mul_le_mul_of_nonneg_left hH (by positivity)
  linarith


/-- **The scaled Robin defect at `N_x`, deterministic lower bound.** -/
theorem robinExtremalDefect_scaled_ge {x c₁ c₂ : ℝ} (hx : 10000 ≤ x) (hc₁ : 1 ≤ c₁)
    (h2 : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ c₁ * Real.sqrt x →
      2 ≤ robinExponent (robinParameter x) p)
    (hc₂ : 1 ≤ c₂) (hc₂x : 2 * x + 3 < c₂ ^ 2 * x) (hyx : c₂ * Real.sqrt x ≤ x)
    (h25 : 2 / 5 * x ≤ Chebyshev.theta x) :
    (mertensProductError x - mertensError x) * (Real.sqrt x * Real.log x)
        + mertensErrorRemainder (Real.log x) * (Real.sqrt x * Real.log x)
        + (Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x
        - Chebyshev.theta (c₂ * Real.sqrt x) / Real.sqrt x
        - 2 * Real.log x * (2 * x ^ ((1 : ℝ) / 3) * Real.log x + 1) / Real.sqrt x
        - ((1 + 2 / (c₁ ^ 2 * x)) * (∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter
            (fun p : ℕ => c₁ * Real.sqrt x < p), 1 / (p : ℝ) ^ 2) * (Real.sqrt x * Real.log x)
          + 8 / (x ^ ((1 : ℝ) / 3)) ^ 2 * (1 + Real.log x) * (Real.sqrt x * Real.log x))
      ≤ robinExtremalDefect x * (Real.sqrt x * Real.log x) := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hL0 : 0 < Real.log x := Real.log_pos hx1
  have hD0 : 0 < Real.sqrt x * Real.log x := mul_pos hsx0 hL0
  have hdec := log_sigma_div_robinExtremalAt_eq hx1
  have hE := robinDeficit_le (by linarith) hc₁ h2
  have hu := log_robinExtremalAt_le hx hc₂ hc₂x hyx
  have hθN := theta_le_log_robinExtremalAt hx1
  set u := Real.log (robinExtremalAt x : ℝ) with hudef
  have hu1 : 1 < u := by linarith
  have hll := log_log_le_add_div hx1 hu1
  set E := ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime,
    -Real.log (1 - (1 / (p : ℝ)) ^ (robinExponent (robinParameter x) p + 1)) with hEdef
  set S := ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter
    (fun p : ℕ => c₁ * Real.sqrt x < p), 1 / (p : ℝ) ^ 2 with hSdef
  set R := 2 * Real.log x * (2 * x ^ ((1 : ℝ) / 3) * Real.log x + 1) with hR
  set M := 8 / (x ^ ((1 : ℝ) / 3)) ^ 2 * (1 + Real.log x) with hM
  have hpre : (mertensProductError x - mertensError x) + mertensErrorRemainder (Real.log x)
        + (Chebyshev.psi x - u) / (x * Real.log x) - E ≤ robinExtremalDefect x := by
    unfold robinExtremalDefect
    rw [← hudef, hdec]
    have e : (Chebyshev.psi x - u) / (x * Real.log x)
        = (Chebyshev.psi x - x) / (x * Real.log x) - (u - x) / (x * Real.log x) := by
      rw [← sub_div]; ring_nf
    rw [e]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hpre hD0.le
  have f1 : (Chebyshev.psi x - u) / (x * Real.log x) * (Real.sqrt x * Real.log x)
      = (Chebyshev.psi x - u) / Real.sqrt x := by
    calc (Chebyshev.psi x - u) / (x * Real.log x) * (Real.sqrt x * Real.log x)
        = (Chebyshev.psi x - u) * Real.sqrt x / (Real.sqrt x * Real.sqrt x) := by
          rw [hxx]; field_simp
      _ = _ := by field_simp
  have hψu : (Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x
        - Chebyshev.theta (c₂ * Real.sqrt x) / Real.sqrt x - R / Real.sqrt x
      ≤ (Chebyshev.psi x - u) / Real.sqrt x := by
    rw [← sub_div, ← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) hsx0.le
  have hED : E * (Real.sqrt x * Real.log x)
      ≤ (1 + 2 / (c₁ ^ 2 * x)) * S * (Real.sqrt x * Real.log x)
        + M * (Real.sqrt x * Real.log x) := by
    have := mul_le_mul_of_nonneg_right hE hD0.le
    linarith
  have hexp : ((mertensProductError x - mertensError x) + mertensErrorRemainder (Real.log x)
        + (Chebyshev.psi x - u) / (x * Real.log x) - E) * (Real.sqrt x * Real.log x)
      = (mertensProductError x - mertensError x) * (Real.sqrt x * Real.log x)
        + mertensErrorRemainder (Real.log x) * (Real.sqrt x * Real.log x)
        + (Chebyshev.psi x - u) / (x * Real.log x) * (Real.sqrt x * Real.log x)
        - E * (Real.sqrt x * Real.log x) := by ring
  rw [hexp, f1] at hmul
  have e2 : R / Real.sqrt x = 2 * Real.log x * (2 * x ^ ((1 : ℝ) / 3) * Real.log x + 1)
      / Real.sqrt x := by rw [hR]
  linarith only [hmul, hψu, hED, e2]


theorem tendsto_two_log_mul_cube_root_div_sqrt :
    Tendsto (fun x : ℝ => 2 * Real.log x * (2 * x ^ ((1 : ℝ) / 3) * Real.log x + 1)
      / Real.sqrt x) atTop (𝓝 0) := by
  have h1 := (tendsto_log_pow_div_rpow_atTop 2 (r := 1 / 6) (by norm_num)).const_mul 4
  have h2 := (tendsto_log_pow_div_rpow_atTop 1 (r := 1 / 2) (by norm_num)).const_mul 2
  have h := h1.add h2
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hs : Real.sqrt x = x ^ ((1 : ℝ) / 3) * x ^ ((1 : ℝ) / 6) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]; norm_num
  have hs2 : Real.sqrt x = x ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow x
  have h3 : 0 < x ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hx _
  have h6 : 0 < x ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hx _
  have e : 2 * Real.log x * (2 * x ^ ((1 : ℝ) / 3) * Real.log x + 1) / Real.sqrt x
      = 4 * Real.log x ^ 2 * (x ^ ((1 : ℝ) / 3) / Real.sqrt x)
        + 2 * (Real.log x / Real.sqrt x) := by
    field_simp; ring
  rw [e, show x ^ ((1 : ℝ) / 3) / Real.sqrt x = 1 / x ^ ((1 : ℝ) / 6) by
    rw [hs]; field_simp, hs2]
  ring

theorem tendsto_eight_div_cube_root_sq_mul :
    Tendsto (fun x : ℝ => 8 / (x ^ ((1 : ℝ) / 3)) ^ 2 * (1 + Real.log x)
      * (Real.sqrt x * Real.log x)) atTop (𝓝 0) := by
  have h1 := (tendsto_log_pow_div_rpow_atTop 1 (r := 1 / 6) (by norm_num)).const_mul 8
  have h2 := (tendsto_log_pow_div_rpow_atTop 2 (r := 1 / 6) (by norm_num)).const_mul 8
  have h := h1.add h2
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have h6 := sqrt_mul_rpow_sixth hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h60 : 0 < x ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hx _
  rw [← h6]
  field_simp

/-- `(1 + a) b ≤ 2/c + 4δ` from `0 ≤ a ≤ δ ≤ 1`, `0 ≤ b ≤ 2/c + δ`, `c ≥ 1`. -/
theorem one_add_mul_le_of_le {a b c δ : ℝ} (hb0 : 0 ≤ b) (ha : a ≤ δ) (hb : b ≤ 2 / c + δ)
    (hc : 1 ≤ c) (hδ1 : δ ≤ 1) (ha0 : 0 ≤ a) : (1 + a) * b ≤ 2 / c + 4 * δ := by
  have hc0 : 0 < c := by linarith
  have hc2 : 2 / c ≤ 2 := by rw [div_le_iff₀ hc0]; linarith
  have hc2' : 0 ≤ 2 / c := by positivity
  have hδ0 : 0 ≤ δ := le_trans ha0 ha
  have h1 : (1 + a) * b ≤ (1 + δ) * (2 / c + δ) :=
    mul_le_mul (by linarith) hb hb0 (by linarith)
  have h4 : δ * δ ≤ δ := by nlinarith
  have h5 : δ * (2 / c) ≤ 2 * δ := by nlinarith
  nlinarith

/-- **The sharp lower bound at `N_x` under RH.**  For every `ε > 0`, eventually
`D(N_x) √x log x ≥ Φ(log x) + 2 - 2√2 - ε`. -/
theorem eventually_robinExtremalDefect_scaled_ge (hRH : RiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, weilLagFunctionReal (Real.log x) + 2 - 2 * Real.sqrt 2 - ε
      ≤ robinExtremalDefect x * (Real.sqrt x * Real.log x) := by
  set η := min (ε / 24) (1 / 4) with hηdef
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hη4 : η ≤ 1 / 4 := min_le_right _ _
  have hηε : η ≤ ε / 24 := min_le_left _ _
  have hs1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs3 : 7 / 5 < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  set c₁ := Real.sqrt 2 - η with hc₁
  set c₂ := Real.sqrt 2 + η with hc₂
  have hc₁1 : 1 ≤ c₁ := by rw [hc₁]; linarith
  have hc₁sq : c₁ ^ 2 < 2 := by rw [hc₁]; nlinarith
  have hc₂1 : 1 ≤ c₂ := by rw [hc₂]; linarith
  have hc₂sq : 2 < c₂ ^ 2 := by rw [hc₂]; nlinarith
  have hsplit := (sqrt_two_split_bounds hη0 hη4).2
  set δ := min (ε / 32) 1 with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) one_pos
  have hδε : δ ≤ ε / 32 := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have E3 := (tendsto_order.1 (tendsto_mertensProductError_sub_scaled hRH)).1 (1 - ε / 8)
    (by linarith)
  have E4 := (tendsto_order.1 (tendsto_mertensErrorRemainder_scaled_sub_lag hRH)).1 (-(ε / 8))
    (by linarith)
  have E5 := (tendsto_order.1 (tendsto_psi_sub_theta_div_sqrt hRH)).1 (1 - ε / 8) (by linarith)
  have E6 := (tendsto_order.1 (tendsto_theta_mul_sqrt_div (c := c₂) (by linarith))).2
    (c₂ + ε / 8) (by linarith)
  have E7 := (tendsto_order.1 tendsto_two_log_mul_cube_root_div_sqrt).2 (ε / 8) (by positivity)
  have E8 := eventually_sum_prime_inv_sq_scaled_le (c := c₁) (δ := δ) hc₁1 hδ0
  have E9 := (tendsto_order.1 tendsto_eight_div_cube_root_sq_mul).2 (ε / 8) (by positivity)
  have E10 : ∀ᶠ x : ℝ in atTop, 2 / (c₁ ^ 2 * x) ≤ δ := by
    have : Tendsto (fun x : ℝ => 2 / (c₁ ^ 2 * x)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by positivity))
    exact this.eventually (ge_mem_nhds hδ0)
  have E11 : ∀ᶠ x : ℝ in atTop, 2 * x + 3 < c₂ ^ 2 * x := by
    filter_upwards [eventually_gt_atTop (3 / (c₂ ^ 2 - 2))] with x hx
    have h0 : 0 < c₂ ^ 2 - 2 := by linarith
    rw [div_lt_iff₀ h0] at hx
    nlinarith
  filter_upwards [eventually_two_le_robinExponent_mul hc₁1 hc₁sq, eventually_ge_atTop (10000 : ℝ),
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop c₂), E3, E4, E5, E6, E7, E8, E9,
    E10, E11, eventually_two_fifths_le_theta] with x h2 hx hsx e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  have hx0 : 0 < x := by linarith
  have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hyx : c₂ * Real.sqrt x ≤ x :=
    calc c₂ * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_right hsx hsx0.le
      _ = x := Real.mul_self_sqrt hx0.le
  have hb := robinExtremalDefect_scaled_ge hx hc₁1 h2 hc₂1 e11 hyx e12
  set S := ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter
    (fun p : ℕ => c₁ * Real.sqrt x < p), 1 / (p : ℝ) ^ 2 with hS
  have hSD0 : 0 ≤ S * (Real.sqrt x * Real.log x) := by
    have : 0 ≤ S := Finset.sum_nonneg fun p _ => by positivity
    have : 0 < Real.log x := Real.log_pos (by linarith)
    positivity
  have hprod : (1 + 2 / (c₁ ^ 2 * x)) * S * (Real.sqrt x * Real.log x) ≤ 2 / c₁ + ε / 8 := by
    have h1 : (1 + 2 / (c₁ ^ 2 * x)) * S * (Real.sqrt x * Real.log x)
        = (1 + 2 / (c₁ ^ 2 * x)) * (S * (Real.sqrt x * Real.log x)) := by ring
    have hpos : 0 ≤ 2 / (c₁ ^ 2 * x) := by positivity
    have h2' := one_add_mul_le_of_le hSD0 e10 e8 hc₁1 hδ1 hpos
    rw [h1]
    linarith
  linarith only [hb, e3, e4, e5, e6, e7, hprod, e9, hsplit, hηε]


/-- `log N_x / x → 1`. -/
theorem tendsto_log_robinExtremalAt_div :
    Tendsto (fun x : ℝ => Real.log (robinExtremalAt x : ℝ) / x) atTop (𝓝 1) := by
  have hs1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  set c := (3 : ℝ) / 2 with hc
  have hθ := tendsto_theta_div_self
  have hinv : Tendsto (fun x : ℝ => 1 / Real.sqrt x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have h1 := (tendsto_theta_mul_sqrt_div (c := c) (by norm_num)).mul hinv
  have h2 := tendsto_two_log_mul_cube_root_div_sqrt.mul hinv
  have hup := (hθ.add h1).add h2
  simp only [mul_zero, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hθ hup ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_le_div_of_nonneg_right (theta_le_log_robinExtremalAt hx) (by linarith)
  · filter_upwards [eventually_ge_atTop (10000 : ℝ),
      Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop c)] with x hx hsx
    have hx0 : 0 < x := by linarith
    have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hyx : c * Real.sqrt x ≤ x :=
      calc c * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_right hsx hsx0.le
        _ = x := hxx
    have hu := log_robinExtremalAt_le hx (by norm_num : (1 : ℝ) ≤ c) (by rw [hc]; nlinarith) hyx
    have e : (Chebyshev.theta x + Chebyshev.theta (c * Real.sqrt x)
          + 2 * Real.log x * (2 * x ^ ((1 : ℝ) / 3) * Real.log x + 1)) / x
        = Chebyshev.theta x / x + Chebyshev.theta (c * Real.sqrt x) / Real.sqrt x
            * (1 / Real.sqrt x)
          + 2 * Real.log x * (2 * x ^ ((1 : ℝ) / 3) * Real.log x + 1) / Real.sqrt x
            * (1 / Real.sqrt x) := by
      have k : ∀ a : ℝ, a / Real.sqrt x * (1 / Real.sqrt x) = a / x := fun a => by
        rw [div_mul_div_comm, mul_one, hxx]
      rw [k, k, add_div, add_div]
    calc Real.log (robinExtremalAt x : ℝ) / x
        ≤ (Chebyshev.theta x + Chebyshev.theta (c * Real.sqrt x)
          + 2 * Real.log x * (2 * x ^ ((1 : ℝ) / 3) * Real.log x + 1)) / x :=
          div_le_div_of_nonneg_right hu hx0.le
      _ = _ := e


/-- The scale ratio `√(log N_x) log log N_x / (√x log x) → 1`. -/
theorem tendsto_robinExtremal_scale_ratio :
    Tendsto (fun x : ℝ => Real.sqrt (Real.log (robinExtremalAt x : ℝ))
        * Real.log (Real.log (robinExtremalAt x : ℝ)) / (Real.sqrt x * Real.log x))
      atTop (𝓝 1) := by
  have hq := tendsto_log_robinExtremalAt_div
  have hsq : Tendsto (fun x : ℝ => Real.sqrt (Real.log (robinExtremalAt x : ℝ) / x)) atTop
      (𝓝 1) := by
    have := (Real.continuous_sqrt.tendsto 1).comp hq
    rw [Real.sqrt_one] at this
    exact this
  have hlogq : Tendsto (fun x : ℝ => Real.log (Real.log (robinExtremalAt x : ℝ) / x)) atTop
      (𝓝 0) := by
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp hq
    rw [Real.log_one] at this
    exact this
  have hl : Tendsto (fun x : ℝ => 1 + Real.log (Real.log (robinExtremalAt x : ℝ) / x)
      / Real.log x) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (hlogq.div_atTop Real.tendsto_log_atTop)
  rw [add_zero] at hl
  have h := hsq.mul hl
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hu := theta_le_log_robinExtremalAt hx
  have hθ0 := Chebyshev.theta_nonneg x
  have hlx : 0 < Real.log x := Real.log_pos hx
  set u := Real.log (robinExtremalAt x : ℝ) with hudef
  by_cases hu0 : u ≤ 0
  · -- degenerate case does not occur for large `x`, but the identity still holds formally
    have hu' : u = 0 := by
      have : 0 ≤ u := le_trans hθ0 hu
      linarith
    simp [hu']
  · push Not at hu0
    rw [Real.sqrt_div' _ hx0.le, Real.log_div hu0.ne' hx0.ne']
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    field_simp
    ring

/-- **Robin's constant, attained.**  Under RH, for every `ε > 0`,
`D(n) √(log n) log log n ≥ a₁ + 2 - 2√2 - ε` for infinitely many `n`. -/
theorem frequently_robinDefectOf_scaled_ge (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop, poleSharpConstant + 2 - 2 * Real.sqrt 2 - ε
      ≤ robinDefectOf n * (Real.sqrt (Real.log n) * Real.log (Real.log n)) := by
  have hκ := kappa_neg
  have ha0 := poleSharpConstant_pos
  have hs2 : Real.sqrt 2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  set ε₁ := min (ε / 4) (1 / 8) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by positivity) (by norm_num)
  have hε₁ε : ε₁ ≤ ε / 4 := min_le_left _ _
  have hε₁8 : ε₁ ≤ 1 / 8 := min_le_right _ _
  set η := ε / 4 with hη
  have hlow := eventually_robinExtremalDefect_scaled_ge hRH hε₁0
  have hratio := (tendsto_order.1 tendsto_robinExtremal_scale_ratio).2 (1 + η) (by linarith)
  have hev : ∀ᶠ x : ℝ in atTop, weilLagFunctionReal (Real.log x) + 2 - 2 * Real.sqrt 2 - ε₁
        ≤ robinExtremalDefect x * (Real.sqrt x * Real.log x)
      ∧ Real.sqrt (Real.log (robinExtremalAt x : ℝ)) * Real.log (Real.log (robinExtremalAt x : ℝ))
          / (Real.sqrt x * Real.log x) < 1 + η
      ∧ 16 ≤ x ∧ 2 / 5 * x ≤ Chebyshev.theta x :=
    hlow.and (hratio.and ((eventually_ge_atTop 16).and eventually_two_fifths_le_theta))
  have hnat := tendsto_natCast_atTop_atTop.eventually hev
  have hfreq := (frequently_prime_integerLag_gt hε₁0).and_eventually hnat
  -- `N_p → ∞`
  have hN : Tendsto (fun p : ℕ => robinExtremalAt (p : ℝ)) atTop atTop := by
    rw [← tendsto_natCast_atTop_iff (R := ℝ)]
    refine tendsto_atTop_mono' atTop ?_ (tendsto_natCast_atTop_atTop.atTop_mul_const
      (show (0 : ℝ) < 2 / 5 by norm_num))
    filter_upwards [tendsto_natCast_atTop_atTop.eventually
      ((eventually_ge_atTop (16 : ℝ)).and eventually_two_fifths_le_theta)] with p ⟨hp16, hθp⟩
    have h1 := theta_le_log_robinExtremalAt (x := (p : ℝ)) (by linarith)
    have hNpos : (0 : ℝ) < robinExtremalAt (p : ℝ) := by exact_mod_cast robinExtremal_pos _ _
    have h2 := Real.log_le_sub_one_of_pos hNpos
    linarith
  refine hN.frequently (hfreq.mono fun p ⟨⟨_, hlag⟩, hD, hr, hp16, hθp⟩ => ?_)
  unfold integerLag at hlag
  have hx1 : (1 : ℝ) < p := by linarith
  have hlx : 0 < Real.log (p : ℝ) := Real.log_pos hx1
  have hsx : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hD0 : 0 < Real.sqrt (p : ℝ) * Real.log p := mul_pos hsx hlx
  have hu := theta_le_log_robinExtremalAt hx1
  have hu1 : 1 < Real.log (robinExtremalAt (p : ℝ) : ℝ) := by linarith
  have hlu : 0 < Real.log (Real.log (robinExtremalAt (p : ℝ) : ℝ)) := Real.log_pos hu1
  set r := Real.sqrt (Real.log (robinExtremalAt (p : ℝ) : ℝ))
    * Real.log (Real.log (robinExtremalAt (p : ℝ) : ℝ)) / (Real.sqrt p * Real.log p) with hrdef
  have hr0 : 0 ≤ r := by
    rw [hrdef]
    have := Real.sqrt_nonneg (Real.log (robinExtremalAt (p : ℝ) : ℝ))
    positivity
  set A := robinExtremalDefect p * (Real.sqrt p * Real.log p) with hA
  have hAK : poleSharpConstant + 2 - 2 * Real.sqrt 2 - 2 * ε₁ ≤ A := by linarith
  have hK0 : poleSharpConstant + 2 - 2 * Real.sqrt 2 - 2 * ε₁ < 0 := by linarith
  have hkey : robinDefectOf (robinExtremalAt (p : ℝ))
      * (Real.sqrt (Real.log (robinExtremalAt (p : ℝ) : ℝ))
        * Real.log (Real.log (robinExtremalAt (p : ℝ) : ℝ))) = A * r := by
    rw [hA, hrdef]
    unfold robinDefectOf robinExtremalDefect
    field_simp
  have hAr : (poleSharpConstant + 2 - 2 * Real.sqrt 2 - 2 * ε₁) * r ≤ A * r :=
    mul_le_mul_of_nonneg_right hAK hr0
  have hKr : (poleSharpConstant + 2 - 2 * Real.sqrt 2 - 2 * ε₁) * (1 + η)
      ≤ (poleSharpConstant + 2 - 2 * Real.sqrt 2 - 2 * ε₁) * r :=
    mul_le_mul_of_nonpos_left hr.le hK0.le
  have hfin : poleSharpConstant + 2 - 2 * Real.sqrt 2 - ε
      ≤ (poleSharpConstant + 2 - 2 * Real.sqrt 2 - 2 * ε₁) * (1 + η) := by
    have hs3 : 7 / 5 < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hlow1 : -2 ≤ poleSharpConstant + 2 - 2 * Real.sqrt 2 - 2 * ε₁ := by linarith
    have hη0 : 0 ≤ η := by positivity
    nlinarith
  rw [hkey]
  linarith

/-- **Robin's sharp constant.**  Under RH, with `κ = a₁ + 2 - 2√2` and
`D(n) = log(σ(n)/n) - γ - log log log n`: for every `ε > 0`,
`D(n) √(log n) log log n ≤ κ + ε` for all large `n`, and `≥ κ - ε` for infinitely many `n`. -/
theorem robinDefectOf_sharp_constant (hRH : RiemannHypothesis) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      robinDefectOf n * (Real.sqrt (Real.log n) * Real.log (Real.log n))
        ≤ poleSharpConstant + 2 - 2 * Real.sqrt 2 + ε)
      ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, poleSharpConstant + 2 - 2 * Real.sqrt 2 - ε
        ≤ robinDefectOf n * (Real.sqrt (Real.log n) * Real.log (Real.log n)) :=
  ⟨fun _ hε => eventually_robinDefectOf_scaled_le hRH hε,
    fun _ hε => frequently_robinDefectOf_scaled_ge hRH hε⟩

end

end RHTower
