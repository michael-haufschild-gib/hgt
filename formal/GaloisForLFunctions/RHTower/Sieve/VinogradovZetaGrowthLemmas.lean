import GaloisForLFunctions.RHTower.Sieve.VinogradovDyadicBlock

/-!
# Parameter lemmas for the Vinogradov–Korobov growth bound

With `L = log τ` and a dyadic block `[Y, 2Y]`, `L^{2/3} ≤ log Y ≤ L/22`, the order
`R = ⌈2L/log Y⌉ + 1` satisfies `22 ≤ R ≤ 3L/log Y`, and for `L` large

`δ_R/4 ≥ (log Y)² / (746496 L² (log L)²)`   (`vinogradovDyadicSaving_div_four_ge`),
`P₀(R) ≤ Y^{1/4}/3`                          (`vinogradovWeylThreshold_le_root`).

With the width `θ = L^{-2/3}(log L)^{-2/3}/100`, the elementary inequality
`θℓ - ℓ³/A ≤ θ^{3/2}√A` (`mul_sub_cube_div_le`) bounds the block exponent
`log Y · (θ - δ_R/4)` by `864/1000`.
-/

namespace RHTower.Sieve

noncomputable section

/-- `θℓ - ℓ³/A ≤ θ^{3/2}√A`. -/
theorem mul_sub_cube_div_le {θ ℓ A : ℝ} (hθ : 0 ≤ θ) (hℓ : 0 ≤ ℓ) (hA : 0 < A) :
    θ * ℓ - ℓ ^ 3 / A ≤ θ * Real.sqrt θ * Real.sqrt A := by
  have hsθ := Real.sqrt_nonneg θ
  have hsA := Real.sqrt_nonneg A
  by_cases h : ℓ ^ 2 ≤ A * θ
  · have hℓs : ℓ ≤ Real.sqrt (A * θ) := Real.le_sqrt_of_sq_le h
    rw [Real.sqrt_mul hA.le] at hℓs
    have h3 : 0 ≤ ℓ ^ 3 / A := by positivity
    calc θ * ℓ - ℓ ^ 3 / A ≤ θ * ℓ := by linarith
      _ ≤ θ * (Real.sqrt A * Real.sqrt θ) := mul_le_mul_of_nonneg_left hℓs hθ
      _ = θ * Real.sqrt θ * Real.sqrt A := by ring
  · push Not at h
    have h3 : θ * ℓ ≤ ℓ ^ 3 / A := by
      rw [le_div_iff₀ hA]
      have : ℓ ^ 3 = ℓ * ℓ ^ 2 := by ring
      rw [this]
      nlinarith
    have : 0 ≤ θ * Real.sqrt θ * Real.sqrt A := by positivity
    linarith

/-- `⌊log₂ n⌋ ≤ log n / log 2`. -/
theorem natLog_two_le_log_div {n : ℕ} (hn : n ≠ 0) :
    (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
  have h := Nat.pow_log_le_self 2 hn
  have hR : (2 : ℝ) ^ (Nat.log 2 n) ≤ n := by exact_mod_cast h
  have hlog := Real.log_le_log (by positivity) hR
  rw [Real.log_pow] at hlog
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]
  exact hlog

/-- The order for a middle block. -/
def vinogradovBlockOrder (L ℓ : ℝ) : ℕ := ⌈2 * L / ℓ⌉₊ + 1

theorem vinogradovBlockOrder_ge {L ℓ : ℝ} (hℓ : 0 < ℓ) (hℓL : 22 * ℓ ≤ L) :
    22 ≤ vinogradovBlockOrder L ℓ := by
  unfold vinogradovBlockOrder
  have h : (44 : ℝ) ≤ 2 * L / ℓ := by rw [le_div_iff₀ hℓ]; linarith
  have : (44 : ℝ) ≤ ⌈2 * L / ℓ⌉₊ := h.trans (Nat.le_ceil _)
  have : 44 ≤ ⌈2 * L / ℓ⌉₊ := by exact_mod_cast this
  omega

theorem vinogradovBlockOrder_le {L ℓ : ℝ} (hℓ : 0 < ℓ) (hℓL : 22 * ℓ ≤ L) :
    (vinogradovBlockOrder L ℓ : ℝ) ≤ 3 * L / ℓ := by
  unfold vinogradovBlockOrder
  have hL0 : 0 ≤ L := by linarith
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * L / ℓ by positivity)
  have h22 : (22 : ℝ) ≤ L / ℓ := by rw [le_div_iff₀ hℓ]; linarith
  push_cast
  have e : 3 * L / ℓ = 2 * L / ℓ + L / ℓ := by ring
  rw [e]
  linarith

theorem two_mul_div_le_vinogradovBlockOrder (L ℓ : ℝ) :
    2 * L / ℓ ≤ (vinogradovBlockOrder L ℓ : ℝ) := by
  unfold vinogradovBlockOrder
  push_cast
  linarith [Nat.le_ceil (2 * L / ℓ)]

/-- `m_R = ⌊log₂(9R²)⌋ + 1 ≤ 2 log L` once `R ≤ 3L^{1/3}` and `L ≥ e^{30}`. -/
theorem vinogradovLogFactor_le {R : ℕ} {L : ℝ} (hR1 : 1 ≤ R) (hRL : (R : ℝ) ≤ 3 * L ^ ((1 : ℝ) / 3))
    (hL : Real.exp 30 ≤ L) :
    ((Nat.log 2 (9 * R ^ 2) + 1 : ℕ) : ℝ) ≤ 2 * Real.log L := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hlogL : 30 ≤ Real.log L := by
    rw [← Real.log_exp 30]; exact Real.log_le_log (Real.exp_pos _) hL
  have hn : 9 * R ^ 2 ≠ 0 := by positivity
  have h1 := natLog_two_le_log_div hn
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR1
  have h9 : ((9 * R ^ 2 : ℕ) : ℝ) ≤ 81 * L ^ ((2 : ℝ) / 3) := by
    push_cast
    have : (R : ℝ) ^ 2 ≤ (3 * L ^ ((1 : ℝ) / 3)) ^ 2 := pow_le_pow_left₀ hR0.le hRL 2
    have e : (3 * L ^ ((1 : ℝ) / 3)) ^ 2 = 9 * L ^ ((2 : ℝ) / 3) := by
      rw [mul_pow, ← Real.rpow_natCast (L ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul hL0.le]; norm_num
    rw [e] at this
    linarith
  have hlog9 : Real.log ((9 * R ^ 2 : ℕ) : ℝ) ≤ Real.log 81 + (2 / 3) * Real.log L := by
    calc Real.log ((9 * R ^ 2 : ℕ) : ℝ) ≤ Real.log (81 * L ^ ((2 : ℝ) / 3)) :=
          Real.log_le_log (by positivity) h9
      _ = Real.log 81 + (2 / 3) * Real.log L := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hL0]
  have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl81 : Real.log 81 ≤ 5 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.add_one_le_exp (5 : ℝ)
    have h2 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have : (2.7 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) he 5
    rw [h2]; norm_num at this ⊢; linarith
  have hdiv : Real.log ((9 * R ^ 2 : ℕ) : ℝ) / Real.log 2 ≤ (5 + (2 / 3) * Real.log L) / 0.69 := by
    rw [div_le_div_iff₀ (Real.log_pos (by norm_num)) (by norm_num)]
    have hl0 : 0 ≤ Real.log ((9 * R ^ 2 : ℕ) : ℝ) := Real.log_nonneg (by
      have : 1 ≤ 9 * R ^ 2 := Nat.one_le_iff_ne_zero.mpr hn
      exact_mod_cast this)
    nlinarith
  have hc : ((Nat.log 2 (9 * R ^ 2) + 1 : ℕ) : ℝ) = (Nat.log 2 (9 * R ^ 2) : ℝ) + 1 := by
    push_cast; ring
  have : (5 + (2 / 3) * Real.log L) / 0.69 + 1 ≤ 2 * Real.log L := by
    rw [div_add_one (by norm_num), div_le_iff₀ (by norm_num)]
    linarith
  rw [hc]
  linarith

/-- **The saving on a middle block.** -/
theorem vinogradovDyadicSaving_div_four_ge {L ℓ : ℝ} (hL : Real.exp 30 ≤ L)
    (hℓ : L ^ ((2 : ℝ) / 3) ≤ ℓ)
    (hℓL : 22 * ℓ ≤ L) :
    ℓ ^ 2 / (746496 * L ^ 2 * Real.log L ^ 2) ≤
      vinogradovDyadicSaving (vinogradovBlockOrder L ℓ) / 4 := by
  set R := vinogradovBlockOrder L ℓ with hRdef
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (Real.rpow_pos_of_pos hL0 _) hℓ
  have hR22 := vinogradovBlockOrder_ge hℓ0 hℓL
  have hRle := vinogradovBlockOrder_le hℓ0 hℓL
  rw [← hRdef] at hR22 hRle
  have hRL : (R : ℝ) ≤ 3 * L ^ ((1 : ℝ) / 3) := by
    have hLℓ : L / ℓ ≤ L ^ ((1 : ℝ) / 3) := by
      rw [div_le_iff₀ hℓ0]
      calc L = L ^ ((1 : ℝ) / 3) * L ^ ((2 : ℝ) / 3) := by
            rw [← Real.rpow_add hL0]; norm_num
        _ ≤ L ^ ((1 : ℝ) / 3) * ℓ := by gcongr
    calc (R : ℝ) ≤ 3 * L / ℓ := hRle
      _ = 3 * (L / ℓ) := by ring
      _ ≤ 3 * L ^ ((1 : ℝ) / 3) := by linarith
  have hm := vinogradovLogFactor_le (by omega) hRL hL
  have hlogL : 30 ≤ Real.log L := by
    rw [← Real.log_exp 30]; exact Real.log_le_log (Real.exp_pos _) hL
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hm0 : (1 : ℝ) ≤ ((Nat.log 2 (9 * R ^ 2) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_add_left 1 _)
  unfold vinogradovDyadicSaving
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hR2 : (R : ℝ) ^ 2 * ℓ ^ 2 ≤ 9 * L ^ 2 := by
    have h1 : (R : ℝ) * ℓ ≤ 3 * L := by
      have := hRle; rw [le_div_iff₀ hℓ0] at this; linarith
    have h0 : 0 ≤ (R : ℝ) * ℓ := by positivity
    nlinarith
  have hm2 : ((Nat.log 2 (9 * R ^ 2) + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * Real.log L ^ 2 := by
    have : ((Nat.log 2 (9 * R ^ 2) + 1 : ℕ) : ℝ) ^ 2 ≤ (2 * Real.log L) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hm 2
    linarith
  calc ℓ ^ 2 * (5184 * (R : ℝ) ^ 2 * ((Nat.log 2 (9 * R ^ 2) + 1 : ℕ) : ℝ) ^ 2 * 4)
      = 20736 * ((R : ℝ) ^ 2 * ℓ ^ 2) * ((Nat.log 2 (9 * R ^ 2) + 1 : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ 20736 * (9 * L ^ 2) * (4 * Real.log L ^ 2) := by gcongr
    _ = 1 * (746496 * L ^ 2 * Real.log L ^ 2) := by ring

/-- `P₀(R) ≤ 2⁵⁴ R¹⁸`. -/
theorem vinogradovWeylThreshold_le_pow (R : ℕ) (hR : 1 ≤ R) :
    vinogradovWeylThreshold R ≤ 2 ^ 54 * R ^ 18 := by
  set k := vinogradovWeylDegree R with hk
  have hk4 : k ≤ 4 * R := by rw [hk]; unfold vinogradovWeylDegree; omega
  have hk1 : 1 ≤ k := by rw [hk]; unfold vinogradovWeylDegree; omega
  have hb : vinogradovWeylMoment R ≤ k ^ 4 := by
    unfold vinogradovWeylMoment
    rw [← hk]
    have hK : vinogradovWeylK R ≤ k ^ 2 := by
      unfold vinogradovWeylK; rw [← hk]
      have : k * (k + 1) ≤ 2 * k ^ 2 := by nlinarith [Nat.zero_le k, hk1]
      omega
    have hlog : Nat.log 2 (vinogradovWeylK R) + 1 ≤ k ^ 2 := by
      have := Nat.log_lt_self 2 (show vinogradovWeylK R ≠ 0 by
        unfold vinogradovWeylK; rw [← hk]
        have : 2 ≤ k * (k + 1) := by nlinarith [hk1]
        omega)
      omega
    calc k ^ 2 * (Nat.log 2 (vinogradovWeylK R) + 1) ≤ k ^ 2 * k ^ 2 := Nat.mul_le_mul_left _ hlog
      _ = k ^ 4 := by ring
  unfold vinogradovWeylThreshold
  rw [← hk]
  apply max_le
  · have : 1 ≤ R ^ 18 := Nat.one_le_pow _ _ (by omega)
    calc 2 ^ 48 ≤ 2 ^ 54 * 1 := by norm_num
      _ ≤ 2 ^ 54 * R ^ 18 := Nat.mul_le_mul_left _ this
  · calc (384 * vinogradovWeylMoment R ^ 2 * k) ^ 2 ≤ (384 * (k ^ 4) ^ 2 * k) ^ 2 := by
          gcongr
      _ = 384 ^ 2 * k ^ 18 := by ring
      _ ≤ 384 ^ 2 * (4 * R) ^ 18 := by gcongr
      _ = 384 ^ 2 * 4 ^ 18 * R ^ 18 := by ring
      _ ≤ 2 ^ 54 * R ^ 18 := by gcongr; norm_num

end

end RHTower.Sieve
