import GaloisForLFunctions.SurfaceOfSpecZ.HeightsAtTheZerosOfTheSplineAreInPhase

/-!
# Zero configurations need an attained top at two Frobenii

`TwoFrobeniiSuffice`: a lower bound on the spline traces at the degrees `pᵃqᵇ` puts every zero of a
tempered configuration on the line, provided the maximal real part is attained. The attainment cannot
be dropped (`exists_zeroConfig_twoPrimes_bddBelow_nonattained`): for all primes `p, q` and
`0 < Θ ≤ ½` there is a tempered configuration without real zeros, with `sup Re ρ = ½ + Θ` not
attained, whose traces satisfy `2 Re S(a log p + b log q) ≥ −5` for all `a, b ∈ ℕ`.

**Construction.** Level `k` is the pair `½ ± x_k + 2πiM_k`, `x_k = Θ(1 − 2^{−k−1})`, its height at a
zero of `B̂`. Its coefficient `c_k = sinc(2πM_k − ix_k)⁸` is in phase (`re_sincPow_mul_exp_ge`) and
`2 Re S(λ) = Σ_k (e^{x_kλ} a_k + e^{−x_kλ} b_k)`, `a_k = 2 Re(c_k e^{2πiM_kλ})`, `|a_k|, |b_k| ≤ 2|c_k|`
(`two_re_lagStructure_config`). The windows are `U_0 = 0`, `U_k = V^{2^k}`. The height
`M_k ∈ [A_k, 2A_k + (2A_kQ_k)²]` is resonant to precision `1/Q_k`, `Q_k ≥ 8πU_{k+1}/log 2`, so
`e^{2πiM_kλ}` is within `¼` of `1` at every degree `λ ≤ U_{k+1}` (`norm_exp_height_sub_one_le`); and
`A_k ≥ 2^{k+1}e^{ΘU_{k−1}}` gives `2|c_k| ≤ 2^{−k}e^{−ΘU_{k−1}}`. Since `M_k = e^{O(√U_k)}`, the weight
`2|c_k| ≥ 2x_k⁸/(7M_k)⁸` takes over from the earlier levels within the window once
`V ≥ 8(306 + 8 log(1/Θ))/Θ` (`eight_le_wt_mul_exp`), and the dominance lemma applies on every window.
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

namespace SplineTower

variable (Θ V : ℝ)

/-- The depths `x_k = Θ(1 − 2^{−k−1})`. -/
def depth (k : ℕ) : ℝ := Θ * (1 - (1 / 2) ^ (k + 1))

/-- The windows `U_0 = 0`, `U_k = V^{2^k}`. -/
def win : ℕ → ℝ
  | 0 => 0
  | k + 1 => V ^ 2 ^ (k + 1)

/-- The weight ceilings `1` and `2^{−k} e^{−ΘU_{k−1}}`. -/
def hiW : ℕ → ℝ
  | 0 => 1
  | k + 1 => (1 / 2) ^ (k + 1) * Real.exp (-(Θ * win V k))

/-- The least height `⌈2/hi_k⌉ + k + 6`. -/
def lowH (k : ℕ) : ℕ := ⌈2 / hiW Θ V k⌉₊ + k + 6

/-- The precision `⌈8πU_{k+1}/log 2⌉ + 1`. -/
def prec (k : ℕ) : ℕ := ⌈8 * Real.pi * win V (k + 1) / Real.log 2⌉₊ + 1

variable (p q : ℕ)

theorem exists_height (k : ℕ) : ∃ M : ℕ, lowH Θ V k ≤ M ∧
    M ≤ 2 * lowH Θ V k + (2 * lowH Θ V k * prec V k) ^ 2 ∧
    ∀ i, ∃ r : ℤ, |(M : ℝ) * ![Real.log p, Real.log q] i - r| ≤ 1 / (prec V k : ℝ) :=
  exists_resonant_ge _ (by unfold lowH; omega) (by unfold prec; omega)

/-- The heights `M_k`, resonant with `log p` and `log q`. -/
def height (k : ℕ) : ℕ := Classical.choose (exists_height Θ V p q k)

theorem height_spec (k : ℕ) : lowH Θ V k ≤ height Θ V p q k ∧
    height Θ V p q k ≤ 2 * lowH Θ V k + (2 * lowH Θ V k * prec V k) ^ 2 ∧
    ∀ i, ∃ r : ℤ, |(height Θ V p q k : ℝ) * ![Real.log p, Real.log q] i - r| ≤
      1 / (prec V k : ℝ) :=
  Classical.choose_spec (exists_height Θ V p q k)

/-- The coefficient `c_k = sinc(2πM_k − ix_k)⁸`. -/
def coef (k : ℕ) : ℂ := sincC (splinePoint (height Θ V p q k) (depth Θ k)) ^ 8

/-- The weight `2|c_k|`. -/
def wt (k : ℕ) : ℝ := 2 * ‖coef Θ V p q k‖

/-- The points `½ ± x_k + 2πiM_k`. -/
def pt : ℕ × Bool → ℂ
  | (k, true) => (1 / 2 : ℂ) + (depth Θ k : ℂ) + ((2 * Real.pi * height Θ V p q k : ℝ) : ℂ) * I
  | (k, false) => (1 / 2 : ℂ) - (depth Θ k : ℂ) + ((2 * Real.pi * height Θ V p q k : ℝ) : ℂ) * I

/-! ### The depths and windows -/

variable {Θ V}

theorem depth_nonneg (hΘ : 0 < Θ) (k : ℕ) : 0 ≤ depth Θ k := by
  unfold depth
  have : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

theorem depth_lt (hΘ : 0 < Θ) (k : ℕ) : depth Θ k < Θ := by
  unfold depth
  have : (0 : ℝ) < (1 / 2) ^ (k + 1) := by positivity
  nlinarith

theorem half_le_depth (hΘ : 0 < Θ) (k : ℕ) : Θ / 2 ≤ depth Θ k := by
  unfold depth
  have : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (by omega)
      _ = 1 / 2 := by norm_num
  nlinarith

theorem strictMono_depth (hΘ : 0 < Θ) : StrictMono (depth Θ) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  unfold depth
  have : (1 / 2 : ℝ) ^ (k + 1 + 1) < (1 / 2) ^ (k + 1) :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
  nlinarith

theorem depth_succ_sub (k : ℕ) : depth Θ (k + 1) - depth Θ k = Θ * (1 / 2) ^ (k + 2) := by
  unfold depth; ring

theorem exists_depth_gt (hΘ : 0 < Θ) {β : ℝ} (hβ : β < Θ) : ∃ k, β < depth Θ k := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < (Θ - β) / Θ by
    exact div_pos (by linarith) hΘ) (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨k, ?_⟩
  unfold depth
  have h1 : (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2) ^ k := pow_le_pow_of_le_one (by norm_num) (by norm_num)
    (by omega)
  rw [lt_div_iff₀ hΘ] at hk
  nlinarith

theorem win_zero : win V 0 = 0 := rfl

theorem win_succ (k : ℕ) : win V (k + 1) = V ^ 2 ^ (k + 1) := rfl

theorem one_le_win_succ (hV : 1 ≤ V) (k : ℕ) : 1 ≤ win V (k + 1) := one_le_pow₀ hV

theorem monotone_win (hV : 1 ≤ V) : Monotone (win V) := by
  refine monotone_nat_of_le_succ fun k => ?_
  rcases k with _ | k
  · rw [win_zero]; exact (zero_le_one).trans (one_le_win_succ hV 0)
  · rw [win_succ, win_succ]
    exact pow_le_pow_right₀ hV (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem win_succ_succ (k : ℕ) : win V (k + 2) = win V (k + 1) ^ 2 := by
  rw [win_succ, win_succ, ← pow_mul, ← pow_succ]

theorem exists_le_win (hV : 2 ≤ V) (lam : ℝ) : ∃ n, lam ≤ win V n := by
  obtain ⟨n, hn⟩ := exists_nat_gt lam
  refine ⟨n + 1, hn.le.trans ?_⟩
  rw [win_succ]
  have h1 : (n : ℝ) ≤ 2 ^ n := by
    have := Nat.lt_two_pow_self (n := n)
    exact_mod_cast this.le
  have h2 : (2 : ℝ) ^ n ≤ 2 ^ 2 ^ (n + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.lt_two_pow_self).le |>.trans
      (pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega)))
  exact h1.trans (h2.trans (pow_le_pow_left₀ (by norm_num) hV _))

/-! ### Heights and weights -/

theorem lowH_le_height (k : ℕ) : lowH Θ V k ≤ height Θ V p q k := (height_spec Θ V p q k).1

theorem six_le_height (k : ℕ) : 6 ≤ height Θ V p q k :=
  le_trans (by unfold lowH; omega) (lowH_le_height p q k)

theorem k_le_height (k : ℕ) : k ≤ height Θ V p q k :=
  le_trans (by unfold lowH; omega) (lowH_le_height p q k)

theorem hiW_pos (k : ℕ) : 0 < hiW Θ V k := by
  rcases k with _ | k
  · simp [hiW]
  · simp only [hiW]; positivity

theorem wt_le_hiW (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (k : ℕ) : wt Θ V p q k ≤ hiW Θ V k := by
  have hM := six_le_height (Θ := Θ) (V := V) p q k
  have hM1 : 1 ≤ height Θ V p q k := by omega
  have hx0 := depth_nonneg hΘ k
  have hx1 : depth Θ k ≤ 1 / 2 := (depth_lt hΘ k).le.trans hΘ2
  have h1 := norm_sincPow_le hM1 hx0 hx1
  have hMr : (1 : ℝ) ≤ height Θ V p q k := by exact_mod_cast hM1
  have hceil : 2 / hiW Θ V k ≤ height Θ V p q k := by
    have h2 : (2 / hiW Θ V k) ≤ (lowH Θ V k : ℝ) := by
      unfold lowH; push_cast
      linarith [Nat.le_ceil (2 / hiW Θ V k)]
    exact h2.trans (by exact_mod_cast lowH_le_height p q k)
  have hpow : (height Θ V p q k : ℝ) ≤ (height Θ V p q k : ℝ) ^ 8 :=
    le_self_pow₀ hMr (by norm_num)
  have hhi := hiW_pos (Θ := Θ) (V := V) k
  unfold wt coef
  calc 2 * ‖sincC (splinePoint (height Θ V p q k) (depth Θ k)) ^ 8‖
      ≤ 2 * (1 / (height Θ V p q k : ℝ) ^ 8) := by linarith
    _ ≤ 2 * (1 / (height Θ V p q k : ℝ)) := by
        gcongr
    _ ≤ hiW Θ V k := by
        rw [div_le_iff₀ hhi] at hceil
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        linarith

theorem wt_nonneg (k : ℕ) : 0 ≤ wt Θ V p q k := by unfold wt; positivity

/-! ### Resonance -/

theorem norm_exp_I_sub_one_le (t : ℝ) : ‖cexp ((t : ℂ) * I) - 1‖ ≤ |t| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t)
  rw [mul_comm] at h
  simpa [Real.norm_eq_abs] using h

/-- **Resonance on the window.** At every degree `λ = a log p + b log q ≤ U_{k+1}`, the phase
`e^{2πiM_kλ}` is within `¼` of `1`. -/
theorem norm_exp_height_sub_one_le (hp : p.Prime) (hq : q.Prime) (hV : 1 ≤ V) (k a b : ℕ)
    (hlam : a * Real.log p + b * Real.log q ≤ win V (k + 1)) :
    ‖cexp (((2 * Real.pi * height Θ V p q k * (a * Real.log p + b * Real.log q) : ℝ) : ℂ) * I) -
      1‖ ≤ 1 / 4 := by
  obtain ⟨-, -, hres⟩ := height_spec Θ V p q k
  obtain ⟨r₁, hr₁⟩ := hres 0
  obtain ⟨r₂, hr₂⟩ := hres 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hr₁ hr₂
  set M : ℝ := (height Θ V p q k : ℝ)
  set Q : ℝ := (prec V k : ℝ)
  set U : ℝ := win V (k + 1)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have hlq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) (by exact_mod_cast hq.two_le)
  have hU1 : 1 ≤ U := one_le_win_succ hV k
  have hQ : 8 * Real.pi * U / Real.log 2 ≤ Q := by
    simp only [Q, prec]; push_cast
    linarith [Nat.le_ceil (8 * Real.pi * U / Real.log 2)]
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  set ε₁ := M * Real.log p - r₁
  set ε₂ := M * Real.log q - r₂
  have hsplit : 2 * Real.pi * M * (a * Real.log p + b * Real.log q) =
      2 * Real.pi * (a * ε₁ + b * ε₂) + ((a * r₁ + b * r₂ : ℤ) : ℝ) * (2 * Real.pi) := by
    simp only [ε₁, ε₂]; push_cast; ring
  rw [hsplit]
  have hexp : cexp (((2 * Real.pi * (a * ε₁ + b * ε₂) + ((a * r₁ + b * r₂ : ℤ) : ℝ) *
      (2 * Real.pi) : ℝ) : ℂ) * I) = cexp (((2 * Real.pi * (a * ε₁ + b * ε₂) : ℝ) : ℂ) * I) := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    have : (((((a * r₁ + b * r₂ : ℤ) : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * I) =
        ((a * r₁ + b * r₂ : ℤ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hexp]
  refine (norm_exp_I_sub_one_le _).trans ?_
  -- `2π(a + b)/Q ≤ ¼`
  have hab : ((a : ℝ) + b) * Real.log 2 ≤ U := by
    have : ((a : ℝ) + b) * Real.log 2 ≤ a * Real.log p + b * Real.log q := by
      have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
      nlinarith
    linarith
  have he : |a * ε₁ + b * ε₂| ≤ (a + b) * (1 / Q) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) a),
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) b)]
    nlinarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  calc 2 * Real.pi * |a * ε₁ + b * ε₂| ≤ 2 * Real.pi * ((a + b) * (1 / Q)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ 1 / 4 := by
        rw [mul_one_div, ← mul_div_assoc, div_le_iff₀ hQ0]
        rw [div_le_iff₀ hl2] at hQ
        nlinarith [Real.pi_pos]

/-! ### The takeover inequality -/

theorem ceil_le_add_one {y : ℝ} (hy : 0 ≤ y) : (⌈y⌉₊ : ℝ) ≤ y + 1 := (Nat.ceil_lt_add_one hy).le

/-- The windows grow: `V^{2^n} ≥ 2^{n+2} W` for `V ≥ 8W ≥ 8`. -/
theorem two_pow_mul_le_pow {W : ℝ} (hW1 : 1 ≤ W) (hV : 8 * W ≤ V) (n : ℕ) :
    2 ^ (n + 2) * W ≤ V ^ 2 ^ n := by
  have hV1 : 1 ≤ V := by linarith
  have h1 : V ^ (n + 1) ≤ V ^ 2 ^ n :=
    pow_le_pow_right₀ hV1 (Nat.succ_le_of_lt Nat.lt_two_pow_self)
  have h2 : (8 : ℝ) ^ (n + 1) * W ≤ V ^ (n + 1) :=
    calc (8 : ℝ) ^ (n + 1) * W ≤ (8 * W) ^ (n + 1) := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left (le_self_pow₀ hW1 (by omega)) (by positivity)
      _ ≤ V ^ (n + 1) := pow_le_pow_left₀ (by positivity) hV _
  have h3 : (2 : ℝ) ^ (n + 2) ≤ 8 ^ (n + 1) := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc 2 ^ (n + 2) * W ≤ 8 ^ (n + 1) * W := mul_le_mul_of_nonneg_right h3 (by linarith)
    _ ≤ V ^ (n + 1) := h2
    _ ≤ _ := h1

/-- **The exponential comparison.** If `Θ ≤ ½`, `1 ≤ s`, `n ≤ s` and
`2^{n+2}(306 + 8 log(1/Θ)) ≤ Θs`, then `8 (2^{2n+26} e^{2Θs} s⁸)⁸ ≤ 2(Θ/2)⁸ e^{Θs²/2^{n+2}}`:
the exponent `16n + 218 + 8 log(1/Θ) + 16Θs + 64s` is at most `(306 + 8 log(1/Θ))s ≤ Θs²/2^{n+2}`. -/
theorem key_ineq {Θ s : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (n : ℕ) (hs1 : 1 ≤ s)
    (hns : (n : ℝ) ≤ s) (hsW : 2 ^ (n + 2) * (306 + 8 * Real.log (1 / Θ)) ≤ Θ * s) :
    8 * (2 ^ (2 * n + 26) * (Real.exp (Θ * s) ^ 2 * s ^ 8)) ^ 8 ≤
      2 * (Θ / 2) ^ 8 * Real.exp (Θ * s ^ 2 / 2 ^ (n + 2)) := by
  set L := Real.log (1 / Θ) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hΘ]; linarith)
  have hexpo : 16 * n + 218 + 8 * L + 16 * (Θ * s) + 64 * s ≤ Θ * s ^ 2 / 2 ^ (n + 2) := by
    have h1 : (306 + 8 * L) * s ≤ Θ * s ^ 2 / 2 ^ (n + 2) := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right hsW (by linarith : (0 : ℝ) ≤ s)
      nlinarith
    have h2 : 16 * (Θ * s) ≤ 8 * s := by nlinarith
    have h3 : 8 * L ≤ 8 * L * s := by nlinarith
    nlinarith
  have e2 : (2 : ℝ) ^ (16 * n + 218) ≤ Real.exp (16 * n + 218) := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    calc (2 : ℝ) ^ (16 * n + 218) ≤ Real.exp 1 ^ (16 * n + 218) :=
          pow_le_pow_left₀ (by norm_num) he _
      _ = Real.exp (16 * n + 218) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have eΘ : (1 / Θ) ^ 8 = Real.exp (8 * L) := by
    rw [show 8 * L = ((8 : ℕ) : ℝ) * L by norm_num, Real.exp_nat_mul, hL,
      Real.exp_log (by positivity)]
  have eE : Real.exp (Θ * s) ^ 16 = Real.exp (16 * (Θ * s)) := by
    rw [← Real.exp_nat_mul]; norm_num
  have es : s ^ 64 ≤ Real.exp (64 * s) := by
    have h := Real.add_one_le_exp s
    calc s ^ 64 ≤ Real.exp s ^ 64 := pow_le_pow_left₀ (by linarith) (by linarith) 64
      _ = Real.exp (64 * s) := by rw [← Real.exp_nat_mul]; norm_num
  have hfin : 2 ^ (16 * n + 218) * (1 / Θ) ^ 8 * Real.exp (Θ * s) ^ 16 * s ^ 64 ≤
      Real.exp (Θ * s ^ 2 / 2 ^ (n + 2)) := by
    rw [eΘ, eE]
    calc 2 ^ (16 * n + 218) * Real.exp (8 * L) * Real.exp (16 * (Θ * s)) * s ^ 64
        ≤ Real.exp (16 * n + 218) * Real.exp (8 * L) * Real.exp (16 * (Θ * s)) *
            Real.exp (64 * s) := by gcongr
      _ = Real.exp (16 * n + 218 + 8 * L + 16 * (Θ * s) + 64 * s) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr hexpo
  have hid : 8 * (2 ^ (2 * n + 26) * (Real.exp (Θ * s) ^ 2 * s ^ 8)) ^ 8 =
      2 * (Θ / 2) ^ 8 * (2 ^ (16 * n + 218) * (1 / Θ) ^ 8 * Real.exp (Θ * s) ^ 16 * s ^ 64) := by
    field_simp
    ring
  rw [hid]
  exact mul_le_mul_of_nonneg_left hfin (by positivity)

theorem win_le_base (n : ℕ) : win V n ≤ V ^ 2 ^ n := by
  rcases n with _ | m
  · rw [win_zero]; positivity
  · rw [win_succ]

/-- The least height at level `n + 1`: `A ≤ 2^{n+5} e^{Θ V^{2^n}}`. -/
theorem lowH_succ_le (hΘ : 0 < Θ) (hV1 : 1 ≤ V) (n : ℕ) :
    (lowH Θ V (n + 1) : ℝ) ≤ 2 ^ (n + 5) * Real.exp (Θ * V ^ 2 ^ n) := by
  set s := V ^ 2 ^ n
  have hs0 : 0 ≤ s := by positivity
  have hy : 2 / hiW Θ V (n + 1) = 2 ^ (n + 2) * Real.exp (Θ * win V n) := by
    rw [div_eq_iff (hiW_pos (n + 1)).ne']
    simp only [hiW]
    have h1 : (2 : ℝ) ^ (n + 2) * (1 / 2) ^ (n + 1) = 2 := by
      rw [show n + 2 = (n + 1) + 1 by ring, pow_succ, mul_comm (2 ^ (n + 1)) 2, mul_assoc,
        ← mul_pow]
      norm_num
    have h2 : Real.exp (Θ * win V n) * Real.exp (-(Θ * win V n)) = 1 := by
      rw [← Real.exp_add]; simp
    calc (2 : ℝ) = 2 ^ (n + 2) * (1 / 2) ^ (n + 1) *
          (Real.exp (Θ * win V n) * Real.exp (-(Θ * win V n))) := by rw [h1, h2, mul_one]
      _ = _ := by ring
  have hexp : Real.exp (Θ * win V n) ≤ Real.exp (Θ * s) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (win_le_base n) hΘ.le)
  have hexp1 : 1 ≤ Real.exp (Θ * s) := Real.one_le_exp (by positivity)
  have hceil := ceil_le_add_one (le_of_lt (div_pos (by norm_num : (0 : ℝ) < 2) (hiW_pos (n + 1))))
  rw [hy] at hceil
  have hn : (n : ℝ) + 8 ≤ 2 ^ (n + 4) := by
    have h : n + 8 ≤ 2 ^ (n + 4) := by
      have h16 : 16 * 2 ^ n ≤ 2 ^ (n + 4) := by rw [pow_add]; omega
      have := Nat.lt_two_pow_self (n := n)
      omega
    exact_mod_cast h
  have h5 : (0 : ℝ) < 2 ^ (n + 2) := by positivity
  have e5 : (2 : ℝ) ^ (n + 5) = 2 ^ (n + 2) * 8 := by
    rw [show n + 5 = (n + 2) + 3 by ring, pow_add]; norm_num
  have e4 : (2 : ℝ) ^ (n + 4) = 2 ^ (n + 2) * 4 := by
    rw [show n + 4 = (n + 2) + 2 by ring, pow_add]; norm_num
  unfold lowH; push_cast
  have h6 := mul_le_mul_of_nonneg_left hexp h5.le
  have h7 := mul_le_mul_of_nonneg_left hexp1 h5.le
  nlinarith

/-- The precision at level `n + 1`: `Q ≤ 39 (V^{2^n})⁴`. -/
theorem prec_succ_le (hV1 : 1 ≤ V) (n : ℕ) : (prec V (n + 1) : ℝ) ≤ 39 * (V ^ 2 ^ n) ^ 4 := by
  set s := V ^ 2 ^ n
  have hs1 : 1 ≤ s := one_le_pow₀ hV1
  have hw : win V (n + 1 + 1) = s ^ 4 := by
    rw [win_succ, ← pow_mul]; congr 1; ring
  unfold prec; push_cast
  rw [hw]
  have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hs4 : 1 ≤ s ^ 4 := one_le_pow₀ hs1
  have h1 := ceil_le_add_one (show 0 ≤ 8 * Real.pi * s ^ 4 / Real.log 2 by positivity)
  have h2 : 8 * Real.pi * s ^ 4 / Real.log 2 ≤ 37 * s ^ 4 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Real.pi_lt_d2]
  linarith

/-- The height: `M ≤ 6A²Q²`. -/
theorem height_le (k : ℕ) : (height Θ V p q k : ℝ) ≤
    6 * (lowH Θ V k : ℝ) ^ 2 * (prec V k : ℝ) ^ 2 := by
  have h := (height_spec Θ V p q k).2.1
  have hA : (1 : ℝ) ≤ lowH Θ V k := by exact_mod_cast (by unfold lowH; omega : 1 ≤ lowH Θ V k)
  have hQ : (1 : ℝ) ≤ prec V k := by exact_mod_cast (by unfold prec; omega : 1 ≤ prec V k)
  have h' : (height Θ V p q k : ℝ) ≤ 2 * lowH Θ V k + (2 * lowH Θ V k * prec V k) ^ 2 := by
    exact_mod_cast h
  nlinarith [mul_le_mul hA hQ zero_le_one (by linarith)]

/-- The weight from below: `2|c_k| ≥ 2(Θ/2)⁸/(7M_k)⁸`. -/
theorem wt_ge (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (k : ℕ) :
    2 * (Θ / 2) ^ 8 / (7 * (height Θ V p q k : ℝ)) ^ 8 ≤ wt Θ V p q k := by
  have hM1 : 1 ≤ height Θ V p q k := by have := six_le_height (Θ := Θ) (V := V) p q k; omega
  have h1 := le_norm_sincPow hM1 (depth_nonneg hΘ k) ((depth_lt hΘ k).le.trans hΘ2)
  have h2 : (Θ / 2) ^ 8 / (7 * (height Θ V p q k : ℝ)) ^ 8 ≤
      depth Θ k ^ 8 / (7 * (height Θ V p q k : ℝ)) ^ 8 :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) (half_le_depth hΘ k) 8)
      (by positivity)
  unfold wt coef
  rw [mul_div_assoc]
  linarith

/-- **The takeover.** For `V ≥ 8(306 + 8 log(1/Θ))/Θ`, the weight of level `n + 1` exceeds the earlier
ones from the start of its window: `2|c_{n+1}| e^{(x_{n+1} − x_n)U_{n+1}} ≥ 8`. -/
theorem eight_le_wt_mul_exp (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2)
    (hV : 8 * ((306 + 8 * Real.log (1 / Θ)) / Θ) ≤ V) (n : ℕ) :
    8 ≤ wt Θ V p q (n + 1) * Real.exp ((depth Θ (n + 1) - depth Θ n) * win V (n + 1)) := by
  have hL0 : 0 ≤ Real.log (1 / Θ) := Real.log_nonneg (by rw [le_div_iff₀ hΘ]; linarith)
  have hW1 : 1 ≤ (306 + 8 * Real.log (1 / Θ)) / Θ := by rw [le_div_iff₀ hΘ]; linarith
  have hV1 : 1 ≤ V := by linarith
  set s := V ^ 2 ^ n with hs
  have hsW := two_pow_mul_le_pow hW1 hV n
  rw [← hs] at hsW
  have hsW' : 2 ^ (n + 2) * (306 + 8 * Real.log (1 / Θ)) ≤ Θ * s := by
    have := mul_le_mul_of_nonneg_left hsW hΘ.le
    rw [show Θ * (2 ^ (n + 2) * ((306 + 8 * Real.log (1 / Θ)) / Θ)) =
      2 ^ (n + 2) * (306 + 8 * Real.log (1 / Θ)) by field_simp] at this
    exact this
  have h2n : (1 : ℝ) ≤ 2 ^ (n + 2) := one_le_pow₀ (by norm_num)
  have hs1 : 1 ≤ s := le_trans (by nlinarith) hsW
  have hns : (n : ℝ) ≤ s := by
    have h : (n : ℝ) ≤ 2 ^ (n + 2) := by
      have : n ≤ 2 ^ (n + 2) := (Nat.lt_two_pow_self (n := n + 2)).le.trans' (by omega)
      exact_mod_cast this
    nlinarith
  have hkey := key_ineq hΘ hΘ2 n hs1 hns hsW'
  have hA := lowH_succ_le (Θ := Θ) hΘ hV1 n
  have hQ := prec_succ_le hV1 n
  have hM := height_le (Θ := Θ) (V := V) p q (n + 1)
  have hwt := wt_ge (V := V) p q hΘ hΘ2 (n + 1)
  rw [← hs] at hA hQ
  set A : ℝ := (lowH Θ V (n + 1) : ℝ)
  set Q : ℝ := (prec V (n + 1) : ℝ)
  set M : ℝ := (height Θ V p q (n + 1) : ℝ)
  have hA1 : 1 ≤ A := by exact_mod_cast (by unfold lowH; omega : 1 ≤ lowH Θ V (n + 1))
  have hQ1 : 1 ≤ Q := by exact_mod_cast (by unfold prec; omega : 1 ≤ prec V (n + 1))
  have hM1 : 1 ≤ M := by
    exact_mod_cast (by have := six_le_height (Θ := Θ) (V := V) p q (n + 1); omega :
      1 ≤ height Θ V p q (n + 1))
  -- `7M ≤ 42A²Q² ≤ 2^{2n+26} e^{2Θs} s⁸`
  have hbase : 7 * M ≤ 2 ^ (2 * n + 26) * (Real.exp (Θ * s) ^ 2 * s ^ 8) := by
    have h1 : A ^ 2 ≤ (2 ^ (n + 5) * Real.exp (Θ * s)) ^ 2 := pow_le_pow_left₀ (by linarith) hA 2
    have h2 : Q ^ 2 ≤ (39 * s ^ 4) ^ 2 := pow_le_pow_left₀ (by linarith) hQ 2
    have h3 : A ^ 2 * Q ^ 2 ≤ (2 ^ (n + 5) * Real.exp (Θ * s)) ^ 2 * (39 * s ^ 4) ^ 2 :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have e : 42 * ((2 ^ (n + 5) * Real.exp (Θ * s)) ^ 2 * (39 * s ^ 4) ^ 2) =
        63882 * 2 ^ (2 * n + 10) * (Real.exp (Θ * s) ^ 2 * s ^ 8) := by
      rw [show 2 * n + 10 = 2 * (n + 5) by ring, pow_mul]; ring
    have e2 : (2 : ℝ) ^ (2 * n + 26) = 2 ^ (2 * n + 10) * 65536 := by
      rw [show 2 * n + 26 = (2 * n + 10) + 16 by ring, pow_add]; norm_num
    have hpos : 0 ≤ 2 ^ (2 * n + 10) * (Real.exp (Θ * s) ^ 2 * s ^ 8) := by positivity
    nlinarith
  have hdelta : (depth Θ (n + 1) - depth Θ n) * win V (n + 1) = Θ * s ^ 2 / 2 ^ (n + 2) := by
    rw [depth_succ_sub, win_succ, hs, ← pow_mul, ← pow_succ, one_div_pow]; ring
  rw [hdelta]
  set B := 2 ^ (2 * n + 26) * (Real.exp (Θ * s) ^ 2 * s ^ 8)
  have hB : 0 < B := by positivity
  have hwt' : 2 * (Θ / 2) ^ 8 / B ^ 8 ≤ wt Θ V p q (n + 1) :=
    le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ (by positivity) hbase 8)) hwt
  have hE : 0 < Real.exp (Θ * s ^ 2 / 2 ^ (n + 2)) := Real.exp_pos _
  calc (8 : ℝ) = 8 * B ^ 8 / B ^ 8 := by field_simp
    _ ≤ 2 * (Θ / 2) ^ 8 * Real.exp (Θ * s ^ 2 / 2 ^ (n + 2)) / B ^ 8 :=
        div_le_div_of_nonneg_right hkey (by positivity)
    _ = 2 * (Θ / 2) ^ 8 / B ^ 8 * Real.exp (Θ * s ^ 2 / 2 ^ (n + 2)) := by ring
    _ ≤ wt Θ V p q (n + 1) * Real.exp (Θ * s ^ 2 / 2 ^ (n + 2)) :=
        mul_le_mul_of_nonneg_right hwt' hE.le

/-! ### The configuration -/

theorem pt_true_re (k : ℕ) : (pt Θ V p q (k, true)).re = 1 / 2 + depth Θ k := by simp [pt]

theorem pt_false_re (k : ℕ) : (pt Θ V p q (k, false)).re = 1 / 2 - depth Θ k := by simp [pt]

theorem pt_im (kb : ℕ × Bool) : (pt Θ V p q kb).im = 2 * Real.pi * height Θ V p q kb.1 := by
  rcases kb with ⟨k, _ | _⟩ <;> simp [pt]

theorem depth_pos (hΘ : 0 < Θ) (k : ℕ) : 0 < depth Θ k :=
  lt_of_lt_of_le (by positivity) (half_le_depth hΘ k)

theorem pt_injective (hΘ : 0 < Θ) : Function.Injective (pt Θ V p q) := by
  rintro ⟨k, b⟩ ⟨k', b'⟩ h
  have hre := congrArg Complex.re h
  have hd := (strictMono_depth hΘ).injective
  have h0 := depth_pos hΘ k
  have h0' := depth_pos hΘ k'
  cases b <;> cases b'
  · rw [pt_false_re, pt_false_re] at hre
    rw [hd (by linarith : depth Θ k = depth Θ k')]
  · rw [pt_false_re, pt_true_re] at hre; linarith
  · rw [pt_true_re, pt_false_re] at hre; linarith
  · rw [pt_true_re, pt_true_re] at hre
    rw [hd (by linarith : depth Θ k = depth Θ k')]

theorem reflect_pt (k : ℕ) (b : Bool) : reflect (pt Θ V p q (k, b)) = pt Θ V p q (k, !b) := by
  apply Complex.ext <;> cases b <;> simp [reflect, pt] <;> ring

variable (V)

/-- **The configuration** `{½ ± x_k + 2πiM_k}` with multiplicity one. -/
def config (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) : ZeroConfig where
  carrier := Set.range (pt Θ V p q)
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := by
    rintro ρ ⟨⟨k, b⟩, rfl⟩
    have h0 := depth_nonneg hΘ k
    have h1 := (depth_lt hΘ k).le
    cases b
    · rw [pt_false_re]; constructor <;> linarith
    · rw [pt_true_re]; constructor <;> linarith
  reflect_mem := by
    rintro ρ ⟨⟨k, b⟩, rfl⟩
    exact ⟨(k, !b), (reflect_pt (V := V) p q k b).symm⟩
  mult_reflect := fun _ _ => rfl
  finite_window := by
    intro T₁ T₂
    refine (((Set.finite_Iic ⌊T₂⌋₊).prod (Set.finite_univ (α := Bool))).image (pt Θ V p q)).subset ?_
    rintro ρ ⟨⟨⟨k, b⟩, rfl⟩, -, hT⟩
    refine ⟨(k, b), ⟨Set.mem_Iic.mpr ?_, Set.mem_univ _⟩, rfl⟩
    rw [pt_im] at hT
    have hk : (k : ℝ) ≤ height Θ V p q k := by exact_mod_cast k_le_height p q k
    have hM0 : (0 : ℝ) ≤ height Θ V p q k := Nat.cast_nonneg _
    have : (k : ℝ) ≤ T₂ := by nlinarith [Real.pi_gt_three]
    exact Nat.le_floor this

variable {V}

theorem gammaOf_pt_true (k : ℕ) :
    gammaOf (pt Θ V p q (k, true)) = splinePoint (height Θ V p q k) (depth Θ k) := by
  apply Complex.ext <;> simp [gammaOf, pt, splinePoint, Complex.div_I]

theorem gammaOf_pt_false (k : ℕ) :
    gammaOf (pt Θ V p q (k, false)) = conj (splinePoint (height Θ V p q k) (depth Θ k)) := by
  apply Complex.ext <;> simp [gammaOf, pt, splinePoint, Complex.div_I]

theorem normSq_gammaOf_pt_ge (kb : ℕ × Bool) :
    (kb.1 : ℝ) ^ 2 ≤ Complex.normSq (gammaOf (pt Θ V p q kb)) := by
  have hre : (gammaOf (pt Θ V p q kb)).re = 2 * Real.pi * height Θ V p q kb.1 := by
    rcases kb with ⟨k, _ | _⟩
    · rw [gammaOf_pt_false, Complex.conj_re, splinePoint_re]
    · rw [gammaOf_pt_true, splinePoint_re]
  rw [Complex.normSq_apply, hre]
  have hk : (kb.1 : ℝ) ≤ height Θ V p q kb.1 := by exact_mod_cast k_le_height p q kb.1
  have h0 : (0 : ℝ) ≤ kb.1 := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ height Θ V p q kb.1 := Nat.cast_nonneg _
  have h1 : (kb.1 : ℝ) ≤ 2 * Real.pi * height Θ V p q kb.1 := by nlinarith [Real.pi_gt_three]
  have h2 := mul_le_mul h1 h1 h0 (h0.trans h1)
  nlinarith [mul_self_nonneg (gammaOf (pt Θ V p q kb)).im]

theorem temperedConfig_config (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    TemperedConfig (config V p q hΘ hΘ2) := by
  unfold TemperedConfig
  set e := Equiv.ofInjective (pt Θ V p q) (pt_injective p q hΘ)
  show Summable fun ρ : Set.range (pt Θ V p q) => ((1 : ℕ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
  refine (e.summable_iff).mp ?_
  have hg : Summable fun kb : ℕ × Bool => 1 / (1 + (kb.1 : ℝ) ^ 2) := by
    refine (summable_prod_of_nonneg (fun kb => by positivity)).mpr ⟨fun k => ?_, ?_⟩
    · exact (hasSum_fintype _).summable
    · have h1 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
        have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
        simpa [Nat.cast_add, Nat.cast_one] using this
      refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun _ => by positivity)
        (fun k => ?_) (h1.mul_left 4)
      rw [tsum_fintype, Fintype.sum_bool]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have h : 1 / (1 + (k : ℝ) ^ 2) ≤ 2 / ((k : ℝ) + 1) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg ((k : ℝ) - 1)]
      have h' : 2 / ((k : ℝ) + 1) ^ 2 = 2 * (1 / ((k : ℝ) + 1) ^ 2) := by ring
      simp only
      linarith
  simp only [Function.comp_def, e, Equiv.ofInjective_apply, Nat.cast_one]
  refine Summable.of_nonneg_of_le (fun kb => div_nonneg zero_le_one
    (by linarith [Complex.normSq_nonneg (gammaOf (pt Θ V p q kb))])) (fun kb => ?_) hg
  exact one_div_le_one_div_of_le (by positivity) (by linarith [normSq_gammaOf_pt_ge (Θ := Θ) (V := V) p q kb])

/-! ### The traces -/

theorem paperFT_weilTest_spline (w : ℂ) :
    paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) w = sincC w ^ 8 := by
  have hb := (contDiff_boxSpline (r := 1) one_pos 2).continuous
  have hbc := hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3)
  rw [EF.paperFT_weilTest hb hb hbc hbc, conj_paperFT_boxSpline, paperFT_boxSpline_eq]
  ring

theorem sincC_conj (w : ℂ) : sincC (conj w) = conj (sincC w) := by
  unfold sincC
  by_cases h : w = 0
  · simp [h]
  · rw [if_neg ((map_ne_zero _).mpr h), if_neg h, map_div₀, Complex.sin_conj]

theorem I_mul_splinePoint (M : ℕ) (x u : ℝ) : I * splinePoint M x * u =
    ((x * u : ℝ) : ℂ) + ((2 * Real.pi * M * u : ℝ) : ℂ) * I := by
  unfold splinePoint; push_cast
  linear_combination (-((x : ℂ) * u)) * Complex.I_sq

theorem I_mul_conj_splinePoint (M : ℕ) (x u : ℝ) : I * conj (splinePoint M x) * u =
    ((-(x * u) : ℝ) : ℂ) + ((2 * Real.pi * M * u : ℝ) : ℂ) * I := by
  unfold splinePoint; simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast
  linear_combination ((x : ℂ) * u) * Complex.I_sq

/-- **The traces of the tower.** `2 Re S(u) = Σ_k (e^{x_k u} 2 Re(c_k e^{iγ_k u}) +
e^{−x_k u} 2 Re(c̄_k e^{iγ_k u}))`, `γ_k = 2πM_k`. -/
theorem two_re_lagStructure_config (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (u : ℝ) :
    2 * (lagStructure (config V p q hΘ hΘ2) (boxSpline 1 3) u).re =
      ∑' k, (Real.exp (depth Θ k * u) * (2 * (coef Θ V p q k *
          cexp (((2 * Real.pi * height Θ V p q k * u : ℝ) : ℂ) * I)).re) +
        Real.exp (-(depth Θ k * u)) * (2 * (conj (coef Θ V p q k) *
          cexp (((2 * Real.pi * height Θ V p q k * u : ℝ) : ℂ) * I)).re)) := by
  set Z := config V p q hΘ hΘ2
  have hb3 := contDiff_boxSpline (r := 1) one_pos 2
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hs := summable_lagStructure Z (temperedConfig_config p q hΘ hΘ2) hb3 hbs u
  set e := Equiv.ofInjective (pt Θ V p q) (pt_injective p q hΘ)
  set F : ℕ × Bool → ℂ := fun kb => paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3))
    (gammaOf (pt Θ V p q kb)) * cexp (I * gammaOf (pt Θ V p q kb) * u) with hF
  have hcomp : ∀ kb, ((Z.mult (e kb) : ℂ) * paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3))
      (gammaOf (e kb)) * cexp (I * gammaOf (e kb) * u)) = F kb := by
    intro kb
    simp only [Z, config, e, Equiv.ofInjective_apply, Nat.cast_one, one_mul, hF]
  have hS : HasSum F (lagStructure Z (boxSpline 1 3) u) := by
    have h1 := ((e.hasSum_iff).mpr hs.hasSum)
    simp only [Function.comp_def, hcomp] at h1
    exact h1
  -- the fibre over level `k`
  set g : ℕ → ℂ := fun k => coef Θ V p q k * (Real.exp (depth Θ k * u) : ℂ) *
      cexp (((2 * Real.pi * height Θ V p q k * u : ℝ) : ℂ) * I) +
    conj (coef Θ V p q k) * (Real.exp (-(depth Θ k * u)) : ℂ) *
      cexp (((2 * Real.pi * height Θ V p q k * u : ℝ) : ℂ) * I) with hg
  have hfib : ∀ k, HasSum (fun b : Bool => F (k, b)) (g k) := by
    intro k
    have h := hasSum_fintype (fun b : Bool => F (k, b))
    rw [Fintype.sum_bool] at h
    convert h using 1
    simp only [hF, hg, gammaOf_pt_true, gammaOf_pt_false, paperFT_weilTest_spline, sincC_conj,
      map_pow, I_mul_splinePoint, I_mul_conj_splinePoint, Complex.exp_add, ← Complex.ofReal_exp,
      coef]
    ring
  have hG : HasSum g (lagStructure Z (boxSpline 1 3) u) := hS.prod_fiberwise hfib
  have hre := (Complex.reCLM.hasSum hG).mul_left 2
  simp only [Complex.reCLM_apply] at hre
  rw [← hre.tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [hg, Complex.add_re]
  rw [show coef Θ V p q k * (Real.exp (depth Θ k * u) : ℂ) *
      cexp (((2 * Real.pi * height Θ V p q k * u : ℝ) : ℂ) * I) =
      (Real.exp (depth Θ k * u) : ℂ) * (coef Θ V p q k *
        cexp (((2 * Real.pi * height Θ V p q k * u : ℝ) : ℂ) * I)) by ring,
    show conj (coef Θ V p q k) * (Real.exp (-(depth Θ k * u)) : ℂ) *
      cexp (((2 * Real.pi * height Θ V p q k * u : ℝ) : ℂ) * I) =
      (Real.exp (-(depth Θ k * u)) : ℂ) * (conj (coef Θ V p q k) *
        cexp (((2 * Real.pi * height Θ V p q k * u : ℝ) : ℂ) * I)) by ring,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

end SplineTower

open SplineTower in
/-- **Zero configurations need an attained top at two Frobenii.** For all primes `p, q` and
`0 < Θ ≤ ½` there is a tempered zero configuration without real zeros whose real parts have the
supremum `½ + Θ`, not attained, and whose spline traces are bounded below at every degree `pᵃqᵇ`.
So the attainment hypothesis of `onLine_of_bddBelow_twoPrimes_of_max` cannot be removed. -/
theorem exists_zeroConfig_twoPrimes_bddBelow_nonattained {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧ (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1 / 2 + Θ) ∧ (∀ β < 1 / 2 + Θ, ∃ ρ ∈ Z.carrier, β < ρ.re) ∧
      ∀ a b : ℕ, -5 ≤ 2 * (lagStructure Z (boxSpline 1 3) (a * Real.log p + b * Real.log q)).re := by
  set V : ℝ := 8 * ((306 + 8 * Real.log (1 / Θ)) / Θ) with hVdef
  have hL0 : 0 ≤ Real.log (1 / Θ) := Real.log_nonneg (by rw [le_div_iff₀ hΘ]; linarith)
  have hV8 : 8 ≤ V := by
    rw [hVdef]
    have : 1 ≤ (306 + 8 * Real.log (1 / Θ)) / Θ := by rw [le_div_iff₀ hΘ]; linarith
    linarith
  have hV1 : 1 ≤ V := by linarith
  refine ⟨config V p q hΘ hΘ2, temperedConfig_config p q hΘ hΘ2, ?_, ?_, ?_, fun a b => ?_⟩
  · rintro ρ ⟨kb, rfl⟩
    rw [pt_im]
    have := six_le_height (Θ := Θ) (V := V) p q kb.1
    have hM : (0 : ℝ) < height Θ V p q kb.1 := by exact_mod_cast (by omega : 0 < height Θ V p q kb.1)
    positivity
  · rintro ρ ⟨⟨k, b⟩, rfl⟩
    have h1 := depth_lt hΘ k
    have h0 := depth_nonneg hΘ k
    cases b
    · rw [pt_false_re]; linarith
    · rw [pt_true_re]; linarith
  · intro β hβ
    obtain ⟨k, hk⟩ := exists_depth_gt hΘ (show β - 1 / 2 < Θ by linarith)
    exact ⟨pt Θ V p q (k, true), ⟨(k, true), rfl⟩, by rw [pt_true_re]; linarith⟩
  · set lam := a * Real.log p + b * Real.log q with hlam
    have hlp := Real.log_nonneg (show (1 : ℝ) ≤ p by exact_mod_cast hp.one_lt.le)
    have hlq := Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast hq.one_lt.le)
    have hlam0 : 0 ≤ lam := by positivity
    rw [two_re_lagStructure_config p q hΘ hΘ2]
    obtain ⟨k, hkl, hku⟩ := exists_window (monotone_win hV1) (by rw [win_zero]; exact hlam0)
      (exists_le_win (by linarith) lam)
    -- the phases of level `j` are within `¼` of `1` on `[0, U_{j+1}]`
    have hph : ∀ j, lam ≤ win V (j + 1) → wt Θ V p q j / 2 ≤
        2 * (coef Θ V p q j * cexp (((2 * Real.pi * height Θ V p q j * lam : ℝ) : ℂ) * I)).re := by
      intro j hj
      have hres := norm_exp_height_sub_one_le (Θ := Θ) p q hp hq hV1 j a b hj
      have h := re_sincPow_mul_exp_ge (six_le_height (Θ := Θ) (V := V) p q j)
        (depth_nonneg hΘ j) ((depth_lt hΘ j).le.trans hΘ2) hres
      unfold wt coef
      linarith
    have hnorm : ∀ j (c : ℂ), |2 * (c * cexp (((2 * Real.pi * height Θ V p q j * lam : ℝ) : ℂ) *
        I)).re| ≤ 2 * ‖c‖ := by
      intro j c
      rw [abs_mul, abs_two]
      refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by norm_num)
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    refine neg_five_le_tsum_of_window hΘ (x := depth Θ) (w := wt Θ V p q) (U := win V)
      (fun j => depth_nonneg hΘ j) (fun j => (depth_lt hΘ j).le) (strictMono_depth hΘ).monotone
      (wt_nonneg p q) ?_ ?_ (monotone_win hV1) (le_of_eq win_zero.symm) (fun j => ?_) (fun j => ?_)
      hlam0 hkl hku (hph k hku) ?_ ?_
    · have := wt_le_hiW (V := V) p q hΘ hΘ2 0
      simpa [hiW] using this
    · intro j
      have := wt_le_hiW (V := V) p q hΘ hΘ2 (j + 1)
      simpa [hiW] using this
    · exact hnorm j _
    · have h := hnorm j (conj (coef Θ V p q j))
      rwa [Complex.norm_conj] at h
    · exact le_trans (by have := wt_nonneg (Θ := Θ) (V := V) p q (k + 1); linarith)
        (hph (k + 1) (hku.trans (monotone_win hV1 (Nat.le_succ _))))
    · rintro n rfl
      exact eight_le_wt_mul_exp p q hΘ hΘ2 le_rfl n

end GaloisForLFunctions.SurfaceOfSpecZ
