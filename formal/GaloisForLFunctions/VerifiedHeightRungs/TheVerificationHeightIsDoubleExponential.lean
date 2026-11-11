import GaloisForLFunctions.VerifiedHeightRungs.LocalSamplingFromVerifiedZeros

/-!
# The verification height is double exponential

**Theorem** (`exists_doubleExp_windowPositive`). There is `C` such that for every `a ≥ 1`, RH verified through
`exp(exp(C a))` makes the Weil form of `ζ` nonnegative on every `C²` test supported in `[−a, a]`.

With `Λ = exp(C₃ a)`: the width is `Y = 36·48⁴ κ a`, the floor `t_* = e^{O(a)}`, and `log T₁, log D₀ = O(e^a)`
(`T₁ = 4 exp(10 + 68e^{a+2} + 2π)`), so the number of nodes is `m ≤ Λ`, the Lagrange constant `K ≤ e^{72Λ}`, the
radius `R ≤ e^{612Λ}`, `1/b ≤ e^{1985Λ}`, and `spreadHeight a = max(R + e^Y + 1, C_a b^{−8}) ≤ e^{e^{10}Λ}`.
-/

open Real

namespace GaloisForLFunctions.VerifiedHeightRungs

open _root_.RHTower Zeta23

noncomputable section

theorem rpow27_le_exp (k : ℕ) : (27 / 10 : ℝ) ^ k ≤ Real.exp k := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) (by have := Real.exp_one_gt_d9; linarith only [this]) k

theorem winE_le {a : ℝ} (ha : 1 ≤ a) : winE a ≤ 600 * Real.exp a := by
  have h1 : Real.sqrt (Real.exp (2 * (a + 2))) = Real.exp 2 * Real.exp a := by
    rw [show 2 * (a + 2) = (a + 2) + (a + 2) by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le,
      ← Real.exp_add, add_comm]
  have h2 : Real.exp 2 ≤ 8 := by
    have := Real.exp_one_lt_d9
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith only [this, Real.exp_pos 1]
  have h3 : 1 ≤ Real.exp a := Real.one_le_exp (by linarith only [ha])
  unfold winE horizonExponent
  rw [h1]
  nlinarith only [h2, h3, Real.exp_pos a, Real.exp_pos 2]

theorem winT₁_le {a : ℝ} (ha : 1 ≤ a) : winT₁ a ≤ Real.exp (610 * Real.exp a) := by
  have h3 : 1 ≤ Real.exp a := Real.one_le_exp (by linarith only [ha])
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (1 : ℝ)
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith only [this]
  unfold winT₁
  calc 4 * Real.exp (winE a + 2 * π) ≤ Real.exp 2 * Real.exp (winE a + 2 * π) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = Real.exp (winE a + 2 * π + 2) := by rw [← Real.exp_add]; ring_nf
    _ ≤ _ := by
      refine Real.exp_le_exp.2 ?_
      have := winE_le ha
      have := Real.pi_lt_d2
      nlinarith only [this, winE_le ha, h3]

theorem winD₀_le {a : ℝ} (ha : 1 ≤ a) : winD₀ a ≤ Real.exp (1300 * Real.exp a) := by
  have h3 : 1 ≤ Real.exp a := Real.one_le_exp (by linarith only [ha])
  have hE := winE_le ha
  have hE0 : 0 < winE a := horizonExponent_pos _
  have hT := winT₁_le ha
  have hT1 := one_le_winT₁ a
  have hπ := Real.pi_gt_three
  -- `D₀ ≤ 3 T₁² E`.
  have h1 : winD₀ a ≤ 3 * winT₁ a ^ 2 * winE a := by
    unfold winD₀
    have hE10 : 10 ≤ winE a := by
      unfold winE horizonExponent
      have := Real.sqrt_nonneg (Real.exp (2 * (a + 2)))
      linarith only [this]
    have h5 : winE a / (2 * π) ≤ winE a := div_le_self hE0.le (by linarith only [hπ])
    have hT2 : 1 ≤ winT₁ a ^ 2 := one_le_pow₀ hT1
    have h6 : (1 + winT₁ a ^ 2) * (winE a / (2 * π)) ≤ (2 * winT₁ a ^ 2) * winE a :=
      mul_le_mul (by linarith only [hT2]) h5 (by positivity) (by positivity)
    nlinarith only [h6, hT2, hE10]
  have hT2 : winT₁ a ^ 2 ≤ Real.exp (1220 * Real.exp a) := by
    calc winT₁ a ^ 2 ≤ Real.exp (610 * Real.exp a) ^ 2 := pow_le_pow_left₀ (by linarith only [hT1]) hT 2
      _ = _ := by rw [← Real.exp_nat_mul]; ring_nf
  have h7 : 3 * winE a ≤ Real.exp (80 * Real.exp a) := by
    have h8 : 3 * winE a ≤ 1800 * Real.exp a := by linarith only [hE]
    have h9 : (1800 : ℝ) ≤ Real.exp 8 := by
      have h := rpow27_le_exp 8
      norm_num at h ⊢
      linarith only [h]
    have h10 : Real.exp a ≤ Real.exp (Real.exp a) := Real.exp_le_exp.2 (by
      have := Real.add_one_le_exp a
      linarith only [this])
    calc 3 * winE a ≤ 1800 * Real.exp a := h8
      _ ≤ Real.exp 8 * Real.exp (Real.exp a) := mul_le_mul h9 h10 (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (8 + Real.exp a) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.2 (by linarith only [h3])
  calc winD₀ a ≤ 3 * winT₁ a ^ 2 * winE a := h1
    _ = winT₁ a ^ 2 * (3 * winE a) := by ring
    _ ≤ Real.exp (1220 * Real.exp a) * Real.exp (80 * Real.exp a) :=
        mul_le_mul hT2 h7 (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; ring_nf

theorem log_term_le {a : ℝ} (ha : 1 ≤ a) :
    8000 * a * winT₁ a * winD₀ a ≤ Real.exp (2000 * Real.exp a) := by
  have h3 : 1 ≤ Real.exp a := Real.one_le_exp (by linarith only [ha])
  have ha0 : 0 < a := by linarith only [ha]
  have h8000 : (8000 : ℝ) ≤ Real.exp 10 := by
    have h := rpow27_le_exp 10
    norm_num at h ⊢
    linarith only [h]
  have ha' : a ≤ Real.exp a := by have := Real.add_one_le_exp a; linarith only [this]
  have hT1 := one_le_winT₁ a
  calc 8000 * a * winT₁ a * winD₀ a ≤ Real.exp 10 * Real.exp a * Real.exp (610 * Real.exp a) *
        Real.exp (1300 * Real.exp a) := by
        have hD := winD₀_le ha
        have hT := winT₁_le ha
        have hD0 : 0 ≤ winD₀ a := by linarith only [one_le_winD₀ a]
        gcongr
    _ = Real.exp (10 + a + 610 * Real.exp a + 1300 * Real.exp a) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith only [h3, ha', ha])

/-- **The size of the height of local sampling.** -/
theorem spreadHeight_le : ∃ C : ℝ, ∀ a : ℝ, 1 ≤ a →
    spreadHeight a ≤ Real.exp (Real.exp (C * a)) := by
  obtain ⟨κY, hκY⟩ : ∃ κY : ℝ, κY = 36 * 48 ^ 4 * spreadKappa := ⟨_, rfl⟩
  have hκ1 : 1 ≤ κY := by rw [hκY]; nlinarith only [one_le_spreadKappa]
  have hCf : 0 ≤ spreadFloorC := le_trans spreadFloorC_ge.2.2 spreadFloorC_ge.2.1
  obtain ⟨C₁, hC₁⟩ : ∃ C₁, C₁ = spreadFloorC * κY + 2 * κY + 2 := ⟨_, rfl⟩
  have hCκ : 0 ≤ spreadFloorC * κY := mul_nonneg hCf (zero_le_one.trans hκ1)
  have hC₁0 : 2 ≤ C₁ := by rw [hC₁]; linarith only [hCκ, hκ1]
  refine ⟨C₁ + 31, fun a ha => ?_⟩
  have ha0 : 0 < a := by linarith only [ha]
  obtain ⟨u, hu⟩ : ∃ u, u = a := ⟨_, rfl⟩
  have hau : a ≤ u := hu.ge
  have hu1 : 1 ≤ u := ha.trans hau
  have hY : spreadY a = κY * u := by rw [spreadY_eq ha0, hκY, hu]
  have h4e : (4 : ℝ) ≤ Real.exp 2 := by
    have h := rpow27_le_exp 2
    norm_num at h ⊢
    linarith only [h]
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = Real.exp ((C₁ + 21) * u) := ⟨_, rfl⟩
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; exact Real.one_le_exp (by nlinarith only [hC₁0, hu1])
  have hΛ0 : 0 < Λ := by linarith only [hΛ1]
  -- `e^a ≤ Λ` and `(C₁ + 21) u ≤ Λ`.
  have heaΛ : Real.exp a ≤ Λ := by
    rw [hΛ]
    exact Real.exp_le_exp.2 (by nlinarith only [hau, hC₁0, hu1])
  have hea1 : 1 ≤ Real.exp a := Real.one_le_exp ha0.le
  -- The node count.
  have hm : (spreadM a : ℝ) ≤ Λ := by
    have hσinv : 1 / nodeStep a = 9 * 48 ^ 4 * a := by rw [nodeStep]; field_simp
    have hfl : spreadFloor a + Real.exp (2 * spreadY a) ≤ 2 * Real.exp (C₁ * u) := by
      unfold spreadFloor
      rw [hY]
      have hCu : spreadFloorC * (κY * u) + 2 ≤ C₁ * u := by
        have e : C₁ * u = spreadFloorC * (κY * u) + 2 * κY * u + 2 * u := by rw [hC₁]; ring
        rw [e]
        nlinarith only [hκ1, hu1]
      have h1 : 4 * Real.exp (spreadFloorC * (κY * u)) ≤ Real.exp (C₁ * u) := by
        calc 4 * Real.exp (spreadFloorC * (κY * u)) ≤ Real.exp 2 * Real.exp (spreadFloorC * (κY * u)) :=
              mul_le_mul_of_nonneg_right h4e (Real.exp_pos _).le
          _ = Real.exp (spreadFloorC * (κY * u) + 2) := by rw [← Real.exp_add]; ring_nf
          _ ≤ _ := Real.exp_le_exp.2 hCu
      have h2 : Real.exp (2 * (κY * u)) ≤ Real.exp (C₁ * u) := by
        refine Real.exp_le_exp.2 ?_
        have e : C₁ * u = spreadFloorC * (κY * u) + 2 * (κY * u) + 2 * u := by rw [hC₁]; ring
        rw [e]
        have := mul_nonneg hCf (mul_nonneg (zero_le_one.trans hκ1) (zero_le_one.trans hu1))
        linarith only [this, hu1]
      linarith only [h1, h2]
    have hc : (9 : ℝ) * 48 ^ 4 * 2 ≤ Real.exp 19 := by
      have h := rpow27_le_exp 19
      norm_num at h ⊢
      linarith only [h]
    have h1 : (spreadFloor a + Real.exp (2 * spreadY a)) / nodeStep a ≤ Real.exp ((C₁ + 20) * u) := by
      rw [div_eq_mul_one_div, hσinv]
      have ha' : a ≤ Real.exp a := by have := Real.add_one_le_exp a; linarith only [this]
      calc (spreadFloor a + Real.exp (2 * spreadY a)) * (9 * 48 ^ 4 * a)
          ≤ 2 * Real.exp (C₁ * u) * (9 * 48 ^ 4 * Real.exp a) :=
            mul_le_mul hfl (by nlinarith only [ha']) (by positivity) (by positivity)
        _ = (9 * 48 ^ 4 * 2) * (Real.exp (C₁ * u) * Real.exp a) := by ring
        _ ≤ Real.exp 19 * (Real.exp (C₁ * u) * Real.exp a) := mul_le_mul_of_nonneg_right hc (by positivity)
        _ = Real.exp (19 + C₁ * u + a) := by rw [Real.exp_add, Real.exp_add]; ring
        _ ≤ _ := Real.exp_le_exp.2 (by nlinarith only [hau, hu1])
    have h2 : Real.log (8000 * a * winT₁ a * winD₀ a) ≤ 2000 * Real.exp a := by
      have hpos : 0 < 8000 * a * winT₁ a * winD₀ a := by
        have := one_le_winT₁ a
        have := one_le_winD₀ a
        positivity
      rw [Real.log_le_iff_le_exp hpos]
      exact log_term_le ha
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ (spreadFloor a + Real.exp (2 * spreadY a)) / nodeStep a +
      Real.log (8000 * a * winT₁ a * winD₀ a) by
        have := spreadM_bounds ha
        have hσ := nodeStep_pos ha0
        have hlog : 0 ≤ Real.log (8000 * a * winT₁ a * winD₀ a) := by
          refine Real.log_nonneg ?_
          have h1 := one_le_winT₁ a
          have h2 := one_le_winD₀ a
          have h3 : 1 ≤ a * winT₁ a := one_le_mul_of_one_le_of_one_le ha h1
          have h4 : 1 ≤ a * winT₁ a * winD₀ a := one_le_mul_of_one_le_of_one_le h3 h2
          nlinarith only [h4]
        have : 0 ≤ (spreadFloor a + Real.exp (2 * spreadY a)) / nodeStep a := by
          unfold spreadFloor; positivity
        linarith only [this, hlog])
    rw [← spreadM] at hceil
    have h3 : 2000 * Real.exp a + 1 ≤ Real.exp ((C₁ + 20) * u) := by
      have h4 : 2001 * Real.exp a ≤ Real.exp 8 * Real.exp a := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        have h := rpow27_le_exp 8
        norm_num at h ⊢
        linarith only [h]
      rw [← Real.exp_add] at h4
      have h5 : Real.exp (8 + a) ≤ Real.exp ((C₁ + 20) * u) := Real.exp_le_exp.2 (by nlinarith only [hau, hu1, hC₁0])
      linarith only [h4, h5, hea1]
    have h6 : 2 * Real.exp ((C₁ + 20) * u) ≤ Λ := by
      rw [hΛ]
      have h7 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith only [this]
      calc 2 * Real.exp ((C₁ + 20) * u) ≤ Real.exp 1 * Real.exp ((C₁ + 20) * u) :=
            mul_le_mul_of_nonneg_right h7 (Real.exp_pos _).le
        _ = Real.exp (1 + (C₁ + 20) * u) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.2 (by nlinarith only [hu1])
    linarith only [hceil, h1, h2, h3, h6]
  have hm0 : (0 : ℝ) ≤ spreadM a := Nat.cast_nonneg _
  -- The Lagrange constant.
  have hn : (spreadN a : ℝ) = 4 * spreadM a + 3 := by rw [spreadN]; push_cast; ring
  have hK : spreadK a ≤ Real.exp (72 * Λ) := by
    have h48 : (48 : ℝ) ≤ Real.exp 4 := by
      have h := rpow27_le_exp 4
      norm_num at h ⊢
      linarith only [h]
    have hp : ((48 : ℝ) ^ spreadN a) ^ 2 ≤ Real.exp (8 * spreadN a) := by
      rw [← pow_mul]
      calc (48 : ℝ) ^ (spreadN a * 2) ≤ Real.exp 4 ^ (spreadN a * 2) := pow_le_pow_left₀ (by norm_num) h48 _
        _ = Real.exp (8 * spreadN a) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have hlin : 2 * ((spreadN a : ℝ) + 1) ≤ Real.exp (16 * Λ) := by
      rw [hn]
      have := Real.add_one_le_exp (16 * Λ)
      linarith only [this, hm, hΛ1]
    unfold spreadK
    calc 2 * ((spreadN a : ℝ) + 1) * ((48 : ℝ) ^ spreadN a) ^ 2 ≤ Real.exp (16 * Λ) * Real.exp (8 * spreadN a) :=
          mul_le_mul hlin hp (by positivity) (Real.exp_pos _).le
      _ = Real.exp (16 * Λ + 8 * spreadN a) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.2 (by rw [hn]; linarith only [hm, hΛ1])
  -- The radius.
  have hσ1 : nodeStep a ≤ 1 := by
    rw [nodeStep, div_le_one (by positivity)]
    nlinarith only [ha]
  have hσ0 := nodeStep_pos ha0
  have hL : spreadL a ≤ 20 * Λ := by
    unfold spreadL
    have : 10 * ((spreadM a : ℝ) + 1) * nodeStep a ≤ 10 * ((spreadM a : ℝ) + 1) :=
      mul_le_of_le_one_right (by positivity) hσ1
    linarith only [this, hm, hΛ1]
  have hfloor : spreadFloor a ≤ Real.exp Λ := by
    unfold spreadFloor
    rw [hY]
    have h1 : spreadFloorC * (κY * u) + 2 ≤ (C₁ + 21) * u := by
      have e : (C₁ + 21) * u = spreadFloorC * (κY * u) + 2 * κY * u + 23 * u := by rw [hC₁]; ring
      rw [e]
      nlinarith only [hκ1, hu1]
    have h2 : (C₁ + 21) * u ≤ Λ := by rw [hΛ]; have := Real.add_one_le_exp ((C₁ + 21) * u); linarith only [this]
    calc 4 * Real.exp (spreadFloorC * (κY * u)) ≤ Real.exp 2 * Real.exp (spreadFloorC * (κY * u)) :=
          mul_le_mul_of_nonneg_right h4e (Real.exp_pos _).le
      _ = Real.exp (spreadFloorC * (κY * u) + 2) := by rw [← Real.exp_add]; ring_nf
      _ ≤ _ := Real.exp_le_exp.2 (by linarith only [h1, h2])
  have hT₁ : winT₁ a ≤ Real.exp (610 * Λ) :=
    (winT₁_le ha).trans (Real.exp_le_exp.2 (by nlinarith only [heaΛ]))
  have hD₀ : winD₀ a ≤ Real.exp (1300 * Λ) :=
    (winD₀_le ha).trans (Real.exp_le_exp.2 (by nlinarith only [heaΛ]))
  have hR : spreadR a ≤ Real.exp (612 * Λ) := by
    unfold spreadR
    have h1 : Real.exp Λ ≤ Real.exp (610 * Λ) := Real.exp_le_exp.2 (by linarith only [hΛ0])
    have h2 : 20 * Λ ≤ Real.exp (610 * Λ) := by
      have := Real.add_one_le_exp (610 * Λ)
      linarith only [this, hΛ0]
    have h3 : 3 * Real.exp (610 * Λ) ≤ Real.exp (612 * Λ) := by
      have h4 : (3 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (2 : ℝ)
        linarith only [this]
      calc 3 * Real.exp (610 * Λ) ≤ Real.exp 2 * Real.exp (610 * Λ) := mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
        _ = Real.exp (2 + 610 * Λ) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.2 (by linarith only [hΛ1])
    linarith only [hT₁, hfloor, hL, h1, h2, h3]
  -- The width.
  have hT₁1 := one_le_winT₁ a
  have hD₀1 := one_le_winD₀ a
  have hK0 : 0 ≤ spreadK a := by unfold spreadK; positivity
  have hR0 : 0 ≤ spreadR a := by
    unfold spreadR spreadL spreadFloor
    positivity
  obtain ⟨den, hden⟩ : ∃ den, den = 8 * winT₁ a * winD₀ a * spreadK a + 2 * spreadR a + 1 := ⟨_, rfl⟩
  have hden1 : 1 ≤ den := by
    rw [hden]
    have : 0 ≤ 8 * winT₁ a * winD₀ a * spreadK a := by positivity
    linarith only [this, hR0]
  have hdenle : den ≤ Real.exp (1985 * Λ) := by
    have h1 : 8 * winT₁ a * winD₀ a * spreadK a ≤ 8 * Real.exp (1982 * Λ) := by
      have := mul_le_mul (mul_le_mul hT₁ hD₀ (by linarith only [hD₀1]) (Real.exp_pos _).le) hK hK0 (by positivity)
      have e : Real.exp (610 * Λ) * Real.exp (1300 * Λ) * Real.exp (72 * Λ) = Real.exp (1982 * Λ) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      rw [e] at this
      calc 8 * winT₁ a * winD₀ a * spreadK a = 8 * (winT₁ a * winD₀ a * spreadK a) := by ring
        _ ≤ 8 * Real.exp (1982 * Λ) := mul_le_mul_of_nonneg_left this (by norm_num)
    have h2 : Real.exp (612 * Λ) ≤ Real.exp (1982 * Λ) := Real.exp_le_exp.2 (by linarith only [hΛ0])
    have h3 : (1 : ℝ) ≤ Real.exp (1982 * Λ) := Real.one_le_exp (by linarith only [hΛ0])
    have h4 : (11 : ℝ) ≤ Real.exp 3 := by
      have h := rpow27_le_exp 3
      norm_num at h ⊢
      linarith only [h]
    calc den ≤ 11 * Real.exp (1982 * Λ) := by rw [hden]; linarith only [h1, hR, h2, h3]
      _ ≤ Real.exp 3 * Real.exp (1982 * Λ) := mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
      _ = Real.exp (3 + 1982 * Λ) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.2 (by linarith only [hΛ1])
  -- The constant of the tail.
  have hC : winC a ≤ Real.exp (33 * Λ) := by
    have hlog3 : Real.log 3 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.add_one_le_exp (2 : ℝ)
      linarith only [this]
    have he1 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith only [this]
    have hc : (2 : ℝ) * (3 * 400 ^ 2) * (24 * 240 * 2) * 1000 ≤ Real.exp 31 := by
      have h := rpow27_le_exp 31
      norm_num at h ⊢
      linarith only [h]
    have ha' : a ≤ Real.exp a := by have := Real.add_one_le_exp a; linarith only [this]
    have hlog30 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    unfold winC
    calc 2 * a * Real.exp a * (Real.exp 1 * 400 ^ 2) * (24 * 240 * Real.log 3) * 1000
        ≤ 2 * Real.exp a * Real.exp a * (3 * 400 ^ 2) * (24 * 240 * 2) * 1000 := by gcongr
      _ = (2 * (3 * 400 ^ 2) * (24 * 240 * 2) * 1000) * (Real.exp a * Real.exp a) := by ring
      _ ≤ Real.exp 31 * (Real.exp a * Real.exp a) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = Real.exp (31 + a + a) := by rw [Real.exp_add, Real.exp_add]; ring
      _ ≤ _ := Real.exp_le_exp.2 (by
          have : a ≤ Λ := ha'.trans heaΛ
          linarith only [this, hΛ1])
  -- The height.
  have hb8 : winC a / spreadB a ^ 8 = winC a * den ^ 8 := by
    rw [spreadB, ← hden, one_div, inv_pow, div_inv_eq_mul]
  have hH2 : winC a / spreadB a ^ 8 ≤ Real.exp (15913 * Λ) := by
    rw [hb8]
    have h1 : den ^ 8 ≤ Real.exp (1985 * Λ) ^ 8 := pow_le_pow_left₀ (by linarith only [hden1]) hdenle 8
    rw [← Real.exp_nat_mul] at h1
    have hC0 : 0 ≤ winC a := by unfold winC; positivity
    calc winC a * den ^ 8 ≤ Real.exp (33 * Λ) * Real.exp ((8 : ℕ) * (1985 * Λ)) :=
          mul_le_mul hC h1 (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; push_cast; ring_nf
  have hH1 : spreadR a + Real.exp (spreadY a) + 1 ≤ Real.exp (15913 * Λ) := by
    have h1 : Real.exp (spreadY a) ≤ Real.exp (612 * Λ) := by
      refine Real.exp_le_exp.2 ?_
      rw [hY]
      have h2 : κY * u ≤ (C₁ + 21) * u := by
        have h4 : κY ≤ C₁ + 21 := by
          rw [hC₁]
          linarith only [hCκ, hκ1]
        exact mul_le_mul_of_nonneg_right h4 (zero_le_one.trans hu1)
      have h3 : (C₁ + 21) * u ≤ Λ := by
        rw [hΛ]; have := Real.add_one_le_exp ((C₁ + 21) * u); linarith only [this]
      linarith only [h2, h3, hΛ0]
    have h2 : (1 : ℝ) ≤ Real.exp (612 * Λ) := Real.one_le_exp (by linarith only [hΛ0])
    have h4 : 3 * Real.exp (612 * Λ) ≤ Real.exp (15913 * Λ) := by
      have h5 : (3 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (2 : ℝ)
        linarith only [this]
      calc 3 * Real.exp (612 * Λ) ≤ Real.exp 2 * Real.exp (612 * Λ) := mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
        _ = Real.exp (2 + 612 * Λ) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.2 (by linarith only [hΛ1])
    linarith only [hR, h1, h2, h4]
  have hH : spreadHeight a ≤ Real.exp (15913 * Λ) := max_le hH1 hH2
  refine hH.trans (Real.exp_le_exp.2 ?_)
  -- `15913 Λ ≤ e^{10} Λ = e^{10 + (C₁ + 21) u} ≤ e^{(C₁ + 31) u}`.
  have h1 : (15913 : ℝ) ≤ Real.exp 10 := by
    have h := rpow27_le_exp 10
    norm_num at h ⊢
    linarith only [h]
  calc 15913 * Λ ≤ Real.exp 10 * Λ := mul_le_mul_of_nonneg_right h1 hΛ0.le
    _ = Real.exp (10 + (C₁ + 21) * u) := by rw [hΛ, Real.exp_add]
    _ ≤ Real.exp ((C₁ + 31) * a) := Real.exp_le_exp.2 (by rw [← hu]; nlinarith only [hu1])

/-- RH verified through a height is verified through every lower height. -/
theorem rhVerifiedThrough_mono {T T' : ℝ} (h : RHVerifiedThrough T') (hT : T ≤ T') : RHVerifiedThrough T :=
  fun _ hxi h0 h1 hpos hle => h hxi h0 h1 hpos (hle.trans hT)

/-- **A double-exponential verification height.** There is `C` such that RH verified through
`exp(exp(C a))` makes the Weil form of `ζ` nonnegative on every `C²` test supported in `[−a, a]`, `a ≥ 1`:
`log log H(a) = O(a)`. -/
theorem exists_doubleExp_windowPositive : ∃ C : ℝ, ∀ a : ℝ, 1 ≤ a →
    RHVerifiedThrough (Real.exp (Real.exp (C * a))) →
      WindowVisibilityLaw.WindowPositiveAt zetaZeroConfig a := by
  obtain ⟨C, hC⟩ := spreadHeight_le
  exact ⟨C, fun a ha hRH f hf hfs => re_W_nonneg_of_rhVerifiedThrough_spread ha le_rfl
    (rhVerifiedThrough_mono hRH (hC a ha)) hf hfs⟩

end

end GaloisForLFunctions.VerifiedHeightRungs
