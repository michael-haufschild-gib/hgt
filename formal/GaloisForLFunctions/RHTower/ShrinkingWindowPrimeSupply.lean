import GaloisForLFunctions.RHTower.ChebyshevThetaPowerLog
import GaloisForLFunctions.RHTower.PsiWindowUpperBound

/-!
# Primes in shrinking multiplicative windows

The power-log `θ`-estimate forces a prime in every window
`[e^y, e^{y+η}]` as soon as `η ≥ K·e^{-c₂·y^{1/10}}` — the window may
shrink at a stretched-exponential rate, far faster than the `1/log`
shrinkage needed for growing-order oversampling node families.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction

set_option maxHeartbeats 1600000 in
/-- **Primes in shrinking windows**: for explicit `c₂, K` and all
`y` past a threshold, any `η ∈ [K·e^{-c₂y^{1/10}}, 1]` window
`[e^y, e^{y+η}]` contains a prime. -/
theorem exists_prime_log_in_shrinking_window :
    ∃ c₂ K y₀ : ℝ, 0 < c₂ ∧ 0 < K ∧ 3 ≤ y₀ ∧
      ∀ y η : ℝ, y₀ ≤ y → 0 < η → η ≤ 1 →
        K * Real.exp (-(c₂ * y ^ ((1 : ℝ) / 10))) ≤ η →
        ∃ p : ℕ, p.Prime ∧ y ≤ Real.log p ∧ Real.log p ≤ y + η := by
  obtain ⟨c, C, x₀, hc, hC, hx₀3, hθ⟩ := exists_chebyshev_theta_power_log
  refine ⟨c / 2, 40 * (C + 1) * Real.exp 1 + 4,
    max 3 (max (Real.log (2 * x₀ + 2)) (c ^ ((10 : ℝ) / 9))),
    by positivity, by positivity, le_max_left _ _, ?_⟩
  intro y η hy hη0 hη1 hηK
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hK4 : (4 : ℝ) ≤ 40 * (C + 1) * Real.exp 1 + 4 := by nlinarith
  have hy3 : (3 : ℝ) ≤ y := le_trans (le_max_left _ _) hy
  have hyx₀ : Real.log (2 * x₀ + 2) ≤ y :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hyc : c ^ ((10 : ℝ) / 9) ≤ y :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  have hy0 : (0 : ℝ) < y := by linarith
  have hey0 : (0 : ℝ) < Real.exp y := Real.exp_pos y
  -- `e^y ≥ 2x₀ + 2`
  have heyx₀ : 2 * x₀ + 2 ≤ Real.exp y := by
    have h1 := Real.exp_le_exp.2 hyx₀
    rwa [Real.exp_log (by positivity)] at h1
  have hx₀0 : (0 : ℝ) < x₀ := by linarith
  -- `c·y^{1/10} ≤ y`, hence the mass condition `e^y·η ≥ 4`
  have hcy : c * y ^ ((1 : ℝ) / 10) ≤ y := by
    have h910 : c ≤ y ^ ((9 : ℝ) / 10) := by
      have h1 : (c ^ ((10 : ℝ) / 9)) ^ ((9 : ℝ) / 10)
          ≤ y ^ ((9 : ℝ) / 10) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hc.le _) hyc (by norm_num)
      rwa [← Real.rpow_mul hc.le,
        show (10 : ℝ) / 9 * (9 / 10) = 1 from by norm_num,
        Real.rpow_one] at h1
    have h1 : c * y ^ ((1 : ℝ) / 10)
        ≤ y ^ ((9 : ℝ) / 10) * y ^ ((1 : ℝ) / 10) :=
      mul_le_mul_of_nonneg_right h910 (Real.rpow_nonneg hy0.le _)
    rwa [← Real.rpow_add hy0,
      show (9 : ℝ) / 10 + 1 / 10 = 1 from by norm_num,
      Real.rpow_one] at h1
  have heyη4 : (4 : ℝ) ≤ Real.exp y * η := by
    have h1 : Real.exp (y / 2)
        ≤ Real.exp (y - c / 2 * y ^ ((1 : ℝ) / 10)) := by
      apply Real.exp_le_exp.2
      nlinarith [hcy]
    have h2 : (1 : ℝ) ≤ Real.exp (y / 2) :=
      Real.one_le_exp (by linarith)
    have h4 := mul_le_mul_of_nonneg_left hηK hey0.le
    have h5 : Real.exp y * Real.exp (-(c / 2 * y ^ ((1 : ℝ) / 10)))
        = Real.exp (y - c / 2 * y ^ ((1 : ℝ) / 10)) := by
      rw [← Real.exp_add]
      congr 1
    have h6 : (4 : ℝ)
        ≤ (40 * (C + 1) * Real.exp 1 + 4)
          * (Real.exp y
            * Real.exp (-(c / 2 * y ^ ((1 : ℝ) / 10)))) := by
      rw [h5]
      nlinarith [h1, h2, hK4, hC, he1]
    nlinarith [h4, h6]
  -- the decay at all evaluation points
  have hEy : ∀ t : ℝ, Real.exp y / 2 ≤ t →
      Real.exp (-(c * Real.log t ^ ((1 : ℝ) / 10)))
        ≤ Real.exp (-(c / 2 * y ^ ((1 : ℝ) / 10))) := by
    intro t ht
    apply Real.exp_le_exp.2
    have ht0 : (0 : ℝ) < t := by
      have : (0 : ℝ) < Real.exp y / 2 := by positivity
      linarith
    have hlogt : y / 2 ≤ Real.log t := by
      have h1 : Real.log (Real.exp y / 2) ≤ Real.log t :=
        Real.log_le_log (by positivity) ht
      rw [Real.log_div (Real.exp_ne_zero y) (by norm_num),
        Real.log_exp] at h1
      have h2 : Real.log 2 ≤ 1 := by
        have h3 := Real.add_one_le_exp (1 : ℝ)
        have h4 : (2 : ℝ) ≤ Real.exp 1 := by linarith
        have h5 := Real.log_le_log (by norm_num) h4
        rwa [Real.log_exp] at h5
      linarith
    have h6 : (y / 2) ^ ((1 : ℝ) / 10)
        ≤ Real.log t ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow (by positivity) hlogt (by norm_num)
    have h7 : y ^ ((1 : ℝ) / 10) / 2 ≤ (y / 2) ^ ((1 : ℝ) / 10) := by
      rw [Real.div_rpow hy0.le (by norm_num)]
      have h8 : (2 : ℝ) ^ ((1 : ℝ) / 10) ≤ 2 := by
        calc (2 : ℝ) ^ ((1 : ℝ) / 10)
            ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num)
                (by norm_num)
          _ = 2 := Real.rpow_one 2
      exact div_le_div_of_nonneg_left
        (Real.rpow_nonneg hy0.le _) (by positivity) h8
    nlinarith [mul_le_mul_of_nonneg_left (le_trans h7 h6) hc.le]
  -- window endpoints
  have hexpη1 : 1 + η ≤ Real.exp η := by
    linarith [Real.add_one_le_exp η]
  have hD0 : (0 : ℝ) < Real.exp η - 1 := by linarith
  have hDη : η ≤ Real.exp η - 1 := by linarith
  have ha1 : 1 ≤ ⌈Real.exp y⌉₊ := Nat.ceil_pos.2 hey0
  have haR : Real.exp y ≤ (⌈Real.exp y⌉₊ : ℝ) := Nat.le_ceil _
  have haR' : (⌈Real.exp y⌉₊ : ℝ) < Real.exp y + 1 :=
    Nat.ceil_lt_add_one hey0.le
  have hbR : (⌊Real.exp (y + η)⌋₊ : ℝ) ≤ Real.exp (y + η) :=
    Nat.floor_le (by positivity)
  have hbR' : Real.exp (y + η) < (⌊Real.exp (y + η)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hexpadd : Real.exp (y + η) = Real.exp y * Real.exp η :=
    Real.exp_add y η
  have hcastm : ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ)
      = (⌈Real.exp y⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub ha1, Nat.cast_one]
  have heyD4 : (4 : ℝ) ≤ Real.exp y * (Real.exp η - 1) := by
    have h1 : Real.exp y * η ≤ Real.exp y * (Real.exp η - 1) :=
      mul_le_mul_of_nonneg_left hDη hey0.le
    linarith
  have hmb : ⌈Real.exp y⌉₊ - 1 < ⌊Real.exp (y + η)⌋₊ := by
    have h1 : ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ) < Real.exp y := by
      rw [hcastm]
      linarith
    have h2 : Real.exp y + 1 ≤ (⌊Real.exp (y + η)⌋₊ : ℝ) + 1 := by
      nlinarith [hbR', heyD4, hexpadd]
    have h3 : ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ)
        < (⌊Real.exp (y + η)⌋₊ : ℝ) := by
      linarith
    exact_mod_cast h3
  -- the evaluation points are large
  have hmhalf : Real.exp y / 2 ≤ ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ) := by
    rw [hcastm]
    have h1 : (2 : ℝ) ≤ Real.exp y := by linarith
    linarith [haR]
  have hbhalf : Real.exp y / 2 ≤ (⌊Real.exp (y + η)⌋₊ : ℝ) := by
    have h1 := le_of_lt hmb
    have h2 : ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ)
        ≤ (⌊Real.exp (y + η)⌋₊ : ℝ) := by exact_mod_cast h1
    linarith [hmhalf]
  have hmx₀ : x₀ ≤ ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ) := by
    have h1 : x₀ ≤ Real.exp y / 2 := by linarith
    linarith [hmhalf]
  have hbx₀ : x₀ ≤ (⌊Real.exp (y + η)⌋₊ : ℝ) := by
    have h1 : x₀ ≤ Real.exp y / 2 := by linarith
    linarith [hbhalf]
  -- quantitative θ-bounds at the endpoints
  have hθm := abs_le.1 (hθ _ hmx₀)
  have hθb := abs_le.1 (hθ _ hbx₀)
  have hEm := hEy _ hmhalf
  have hEb := hEy _ hbhalf
  -- window mass
  have hbm : Real.exp y * (Real.exp η - 1) / 2
      ≤ (⌊Real.exp (y + η)⌋₊ : ℝ)
        - ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ) := by
    rw [hcastm]
    nlinarith [hbR', haR', heyD4, hexpadd]
  have hbm2 : (⌊Real.exp (y + η)⌋₊ : ℝ)
        + ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ)
      ≤ 2 * Real.exp y * Real.exp 1 := by
    rw [hcastm]
    have h1 : Real.exp η ≤ Real.exp 1 := Real.exp_le_exp.2 hη1
    have h2 : Real.exp y ≤ Real.exp y * Real.exp η := by
      nlinarith [hey0, hexpη1, hη0]
    nlinarith [haR', hbR, hexpadd, h1, h2, hey0]
  -- positive θ-mass in the window
  have hpos : 0 < Chebyshev.theta ↑⌊Real.exp (y + η)⌋₊
      - Chebyshev.theta ↑(⌈Real.exp y⌉₊ - 1) := by
    have h1 := hθb.1
    have h2 := hθm.2
    set Ey : ℝ := Real.exp (-(c / 2 * y ^ ((1 : ℝ) / 10))) with hEydef
    have hEy0 : 0 < Ey := Real.exp_pos _
    -- error mass ≤ C·Ey·(b + m) ≤ 2e·C·e^y·Ey
    have h3 : C * ((⌊Real.exp (y + η)⌋₊ : ℝ))
          * Real.exp (-(c * Real.log ↑⌊Real.exp (y + η)⌋₊
            ^ ((1 : ℝ) / 10)))
        ≤ C * (2 * Real.exp y * Real.exp 1) * Ey := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ hC
        have := hbm2
        have h4 : (0 : ℝ) ≤ ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ) := by
          positivity
        linarith
      · exact hEb
      · positivity
      · positivity
    have h5 : C * ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ)
          * Real.exp (-(c * Real.log ↑(⌈Real.exp y⌉₊ - 1)
            ^ ((1 : ℝ) / 10)))
        ≤ C * (2 * Real.exp y * Real.exp 1) * Ey := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ hC
        have h4 : (0 : ℝ) ≤ (⌊Real.exp (y + η)⌋₊ : ℝ) := by
          positivity
        linarith [hbm2]
      · exact hEm
      · positivity
      · positivity
    -- the mass beats the error
    have h6 : (40 * (C + 1) * Real.exp 1 + 4) * Ey ≤ η := hηK
    have k1 : Chebyshev.theta ↑⌊Real.exp (y + η)⌋₊
        - Chebyshev.theta ↑(⌈Real.exp y⌉₊ - 1)
        ≥ ((⌊Real.exp (y + η)⌋₊ : ℝ)
            - ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ))
          - (C * (2 * Real.exp y * Real.exp 1) * Ey
            + C * (2 * Real.exp y * Real.exp 1) * Ey) := by
      linarith [h1, h2, h3, h5]
    have k2 : Real.exp y * η / 2
        ≤ (⌊Real.exp (y + η)⌋₊ : ℝ)
          - ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ) := by
      have k2a := mul_le_mul_of_nonneg_left hDη hey0.le
      linarith [hbm]
    have k4 : 8 * C * Real.exp 1 * Ey
        < (40 * (C + 1) * Real.exp 1 + 4) * Ey := by
      apply mul_lt_mul_of_pos_right _ hEy0
      nlinarith [he1, hC]
    have k5 : 8 * C * Real.exp 1 * Ey < η := lt_of_lt_of_le k4 h6
    have k6 := mul_lt_mul_of_pos_left k5
      (show (0 : ℝ) < Real.exp y / 2 from by positivity)
    nlinarith [k1, k2, k6]
  have hwin := theta_window_eq (le_of_lt hmb)
  rw [hwin] at hpos
  have hne : ((Finset.Ioc (⌈Real.exp y⌉₊ - 1)
      ⌊Real.exp (y + η)⌋₊).filter Nat.Prime).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨p, hp⟩ := hne
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  refine ⟨p, hp.2, ?_, ?_⟩
  · have hpa : ⌈Real.exp y⌉₊ ≤ p := by omega
    have h1 : Real.exp y ≤ (p : ℝ) :=
      le_trans haR (by exact_mod_cast hpa)
    have h2 := Real.log_le_log hey0 h1
    rwa [Real.log_exp] at h2
  · have h1 : (p : ℝ) ≤ Real.exp (y + η) :=
      le_trans (by exact_mod_cast hp.1.2) hbR
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
    have h2 := Real.log_le_log hp0 h1
    rwa [Real.log_exp] at h2

end RHTower
