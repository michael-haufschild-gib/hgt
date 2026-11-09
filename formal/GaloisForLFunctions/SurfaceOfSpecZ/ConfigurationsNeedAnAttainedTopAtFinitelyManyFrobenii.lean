import GaloisForLFunctions.SurfaceOfSpecZ.HeightsAtTheZerosOfTheSplineAreInPhase

/-!
# Zero configurations need an attained top at finitely many Frobenii

`TwoFrobeniiSuffice`: a lower bound on the spline traces at the degrees `pᵃqᵇ` puts every zero of a
tempered configuration on the line, provided the maximal real part is attained. The attainment cannot
be dropped, at the degrees of any finite set of primes
(`exists_zeroConfig_finPrimes_bddBelow_nonattained`):
for primes `P₁, …, P_r` and `0 < Θ ≤ ½` there is a tempered configuration without real zeros, with
`sup Re ρ = ½ + Θ` not attained, whose traces satisfy `2 Re S(Σ aᵢ log Pᵢ) ≥ −5` for all `a ∈ ℕ^r`.
Such a monoid has `≍ (log x)^r` elements up to `x`; the primes, with power-saving gaps, need no
attainment (`TheGapMethodIterates`).

**The blind side is a sign.** For the spline of order `o` the coefficient at the zero `2πM` of `B̂`
is `(−1)^{o+1}` times a positive number, so the same towers satisfy `(−1)^{o+1} 2 Re S ≥ −5` at every
degree (`exists_zeroConfig_finPrimes_signed_nonattained`): from below for the cubic spline, from above
for the quartic one (`exists_zeroConfig_finPrimes_bddAbove_nonattained_quartic`). The other side
would need coefficients of the opposite sign at resonant heights, i.e. heights at a prescribed
offset from `πℤ`: inhomogeneous Kronecker on `(1, log P₁, …, log P_r)`.

**Construction.** Level `k` is the pair `½ ± x_k + 2πiM_k`, `x_k = Θ(1 − 2^{−k−1})`, its height at a
zero of `B̂`. Its coefficient `c_k = sinc(2πM_k − ix_k)⁸` is in phase (`re_sincPow_mul_exp_ge`) and
`2 Re S(λ) = Σ_k (e^{x_kλ} a_k + e^{−x_kλ} b_k)`, `a_k = 2 Re(c_k e^{2πiM_kλ})`, `|a_k|, |b_k| ≤ 2|c_k|`
(`two_re_lagStructure_config`). The windows are `U_0 = 0`, `U_k = V^{2^k}`. The height
`M_k ∈ [A_k, 2A_k + (2A_kQ_k)^r]` is resonant to precision `1/Q_k`, `Q_k ≥ 8πU_{k+1}/log 2`, so
`e^{2πiM_kλ}` is within `¼` of `1` at every degree `λ ≤ U_{k+1}` (`norm_exp_height_sub_one_le`); and
`A_k ≥ 2^{k+1}e^{ΘU_{k−1}}` gives `2|c_k| ≤ 2^{−k}e^{−ΘU_{k−1}}`. Since `M_k = e^{O(√U_k)}`, the weight
`2|c_k| ≥ 2x_k⁸/(7M_k)⁸` takes over from the earlier levels within the window once
`V ≥ 8W` (`towerW`, `eight_le_wt_mul_exp`), and the dominance lemma applies on every window.
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

namespace SplineTower

variable (o : ℕ) (Θ V : ℝ)

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

/-- The least height `⌈(2o + 4)/hi_k⌉ + k + 2(o + 1)`. -/
def lowH (k : ℕ) : ℕ := ⌈(2 * (o : ℝ) + 4) / hiW Θ V k⌉₊ + k + 2 * (o + 1)

/-- The precision `⌈8πU_{k+1}/log 2⌉ + 1`. -/
def prec (k : ℕ) : ℕ := ⌈8 * Real.pi * win V (k + 1) / Real.log 2⌉₊ + 1

variable {r : ℕ} (P : Fin r → ℕ)

theorem exists_height (k : ℕ) : ∃ M : ℕ, lowH o Θ V k ≤ M ∧
    M ≤ 2 * lowH o Θ V k + (2 * lowH o Θ V k * prec V k) ^ r ∧
    ∀ i, ∃ z : ℤ, |(M : ℝ) * Real.log (P i) - z| ≤ 1 / (prec V k : ℝ) :=
  exists_resonant_ge (fun i => Real.log (P i)) (by unfold lowH; omega) (by unfold prec; omega)

/-- The heights `M_k`, resonant with every `log Pᵢ`. -/
def height (k : ℕ) : ℕ := Classical.choose (exists_height o Θ V P k)

theorem height_spec (k : ℕ) : lowH o Θ V k ≤ height o Θ V P k ∧
    height o Θ V P k ≤ 2 * lowH o Θ V k + (2 * lowH o Θ V k * prec V k) ^ r ∧
    ∀ i, ∃ z : ℤ, |(height o Θ V P k : ℝ) * Real.log (P i) - z| ≤ 1 / (prec V k : ℝ) :=
  Classical.choose_spec (exists_height o Θ V P k)

/-- The coefficient `c_k = sinc(2πM_k − ix_k)^{2(o+1)}` of the spline of order `o`. -/
def coef (k : ℕ) : ℂ := sincC (splinePoint (height o Θ V P k) (depth Θ k)) ^ (2 * (o + 1))

/-- The weight `2|c_k|`. -/
def wt (k : ℕ) : ℝ := 2 * ‖coef o Θ V P k‖

/-- The points `½ ± x_k + 2πiM_k`. -/
def pt : ℕ × Bool → ℂ
  | (k, true) => (1 / 2 : ℂ) + (depth Θ k : ℂ) + ((2 * Real.pi * height o Θ V P k : ℝ) : ℂ) * I
  | (k, false) => (1 / 2 : ℂ) - (depth Θ k : ℂ) + ((2 * Real.pi * height o Θ V P k : ℝ) : ℂ) * I

/-! ### The depths and windows -/

variable {o Θ V}

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

theorem lowH_le_height (k : ℕ) : lowH o Θ V k ≤ height o Θ V P k := (height_spec o Θ V P k).1

theorem two_mul_le_height (k : ℕ) : 2 * (o + 1) ≤ height o Θ V P k :=
  le_trans (by unfold lowH; omega) (lowH_le_height P k)

theorem k_le_height (k : ℕ) : k ≤ height o Θ V P k :=
  le_trans (by unfold lowH; omega) (lowH_le_height P k)

theorem hiW_pos (k : ℕ) : 0 < hiW Θ V k := by
  rcases k with _ | k
  · simp [hiW]
  · simp only [hiW]; positivity

theorem wt_le_hiW (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (k : ℕ) : wt o Θ V P k ≤ hiW Θ V k := by
  have hM := two_mul_le_height (o := o) (Θ := Θ) (V := V) P k
  have hM1 : 1 ≤ height o Θ V P k := by omega
  have hx0 := depth_nonneg hΘ k
  have hx1 : depth Θ k ≤ 1 / 2 := (depth_lt hΘ k).le.trans hΘ2
  have h1 := norm_sincPow_le hM1 hx0 hx1 (o + 1)
  have hMr : (1 : ℝ) ≤ height o Θ V P k := by exact_mod_cast hM1
  have hhi := hiW_pos (Θ := Θ) (V := V) k
  have hceil : 2 / hiW Θ V k ≤ height o Θ V P k := by
    have h2 : 2 / hiW Θ V k ≤ (2 * (o : ℝ) + 4) / hiW Θ V k :=
      div_le_div_of_nonneg_right (by have : (0 : ℝ) ≤ o := Nat.cast_nonneg o; linarith) hhi.le
    have h3 : (2 * (o : ℝ) + 4) / hiW Θ V k ≤ (lowH o Θ V k : ℝ) := by
      unfold lowH; push_cast
      linarith [Nat.le_ceil ((2 * (o : ℝ) + 4) / hiW Θ V k)]
    exact h2.trans (h3.trans (by exact_mod_cast lowH_le_height P k))
  have hpow : (height o Θ V P k : ℝ) ≤ (height o Θ V P k : ℝ) ^ (2 * (o + 1)) :=
    le_self_pow₀ hMr (by omega)
  unfold wt coef
  calc 2 * ‖sincC (splinePoint (height o Θ V P k) (depth Θ k)) ^ (2 * (o + 1))‖
      ≤ 2 * (1 / (height o Θ V P k : ℝ) ^ (2 * (o + 1))) := by linarith
    _ ≤ 2 * (1 / (height o Θ V P k : ℝ)) := by gcongr
    _ ≤ hiW Θ V k := by
        rw [div_le_iff₀ hhi] at hceil
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        linarith

theorem wt_nonneg (k : ℕ) : 0 ≤ wt o Θ V P k := by unfold wt; positivity

/-! ### Resonance -/

theorem norm_exp_I_sub_one_le (t : ℝ) : ‖cexp ((t : ℂ) * I) - 1‖ ≤ |t| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t)
  rw [mul_comm] at h
  simpa [Real.norm_eq_abs] using h

/-- **Resonance on the window.** At every degree `λ = Σ aᵢ log Pᵢ ≤ U_{k+1}`, the phase
`e^{2πiM_kλ}` is within `¼` of `1`. -/
theorem norm_exp_height_sub_one_le (hP : ∀ i, (P i).Prime) (hV : 1 ≤ V) (k : ℕ) (a : Fin r → ℕ)
    (hlam : ∑ i, (a i : ℝ) * Real.log (P i) ≤ win V (k + 1)) :
    ‖cexp (((2 * Real.pi * height o Θ V P k * ∑ i, (a i : ℝ) * Real.log (P i) : ℝ) : ℂ) * I) -
      1‖ ≤ 1 / 4 := by
  obtain ⟨-, -, hres⟩ := height_spec o Θ V P k
  choose z hz using hres
  set M : ℝ := (height o Θ V P k : ℝ)
  set Q : ℝ := (prec V k : ℝ)
  set U : ℝ := win V (k + 1)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlP : ∀ i, Real.log 2 ≤ Real.log (P i) := fun i =>
    Real.log_le_log (by norm_num) (by exact_mod_cast (hP i).two_le)
  have hU1 : 1 ≤ U := one_le_win_succ hV k
  have hQ : 8 * Real.pi * U / Real.log 2 ≤ Q := by
    simp only [Q, prec]; push_cast
    linarith [Nat.le_ceil (8 * Real.pi * U / Real.log 2)]
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  set ε : Fin r → ℝ := fun i => M * Real.log (P i) - z i with hε
  have hsplit : 2 * Real.pi * M * ∑ i, (a i : ℝ) * Real.log (P i) =
      2 * Real.pi * ∑ i, (a i : ℝ) * ε i + ((∑ i, (a i : ℤ) * z i : ℤ) : ℝ) * (2 * Real.pi) := by
    simp only [hε]; push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit]
  have hexp : cexp (((2 * Real.pi * ∑ i, (a i : ℝ) * ε i + ((∑ i, (a i : ℤ) * z i : ℤ) : ℝ) *
      (2 * Real.pi) : ℝ) : ℂ) * I) = cexp (((2 * Real.pi * ∑ i, (a i : ℝ) * ε i : ℝ) : ℂ) * I) := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    have : ((((∑ i, (a i : ℤ) * z i : ℤ) : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * I =
        ((∑ i, (a i : ℤ) * z i : ℤ) : ℂ) * (2 * Real.pi * I) := by push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hexp]
  refine (norm_exp_I_sub_one_le _).trans ?_
  -- `2π Σ aᵢ / Q ≤ ¼`
  have hsum : (∑ i, (a i : ℝ)) * Real.log 2 ≤ U := by
    have : (∑ i, (a i : ℝ)) * Real.log 2 ≤ ∑ i, (a i : ℝ) * Real.log (P i) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hlP i) (Nat.cast_nonneg _)
    linarith
  have he : |∑ i, (a i : ℝ) * ε i| ≤ (∑ i, (a i : ℝ)) * (1 / Q) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hz i) (Nat.cast_nonneg _)
  have hA0 : 0 ≤ ∑ i, (a i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  calc 2 * Real.pi * |∑ i, (a i : ℝ) * ε i| ≤ 2 * Real.pi * ((∑ i, (a i : ℝ)) * (1 / Q)) :=
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

/-- **The exponential comparison.** If `Θ ≤ ½`, `C, R, N ≥ 1`, `1 ≤ s`, `n ≤ s` and
`2^{n+2}((25 + C)NR + N log(1/Θ)) ≤ Θs`, then
`8 (C^R 2^{(n+12)R} 16 e^{RΘs} s^{4R})^N ≤ 2(Θ/2)^N e^{Θs²/2^{n+2}}`: the exponent
`RNC + (n+12)RN + 5N + 2 + N log(1/Θ) + NRΘs + 4RNs` is at most
`((25 + C)NR + N log(1/Θ))s ≤ Θs²/2^{n+2}`. -/
theorem key_ineq {Θ s C : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (hC : 1 ≤ C) (n R N : ℕ)
    (hR : 1 ≤ R) (hN : 1 ≤ N) (hs1 : 1 ≤ s) (hns : (n : ℝ) ≤ s)
    (hsW : 2 ^ (n + 2) * ((25 + C) * (N * R) + N * Real.log (1 / Θ)) ≤ Θ * s) :
    8 * (C ^ R * 2 ^ ((n + 12) * R) * 16 * (Real.exp (Θ * s) ^ R * s ^ (4 * R))) ^ N ≤
      2 * (Θ / 2) ^ N * Real.exp (Θ * s ^ 2 / 2 ^ (n + 2)) := by
  set L := Real.log (1 / Θ) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hΘ]; linarith)
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs0 : (0 : ℝ) ≤ s := by linarith
  set T : ℝ := (N : ℝ) * R with hT
  have hT1 : 1 ≤ T := by rw [hT]; nlinarith
  have hexpo : T * C + (n + 12) * T + (5 * N + 2) + N * L + T * (Θ * s) + 4 * T * s ≤
      Θ * s ^ 2 / 2 ^ (n + 2) := by
    have h1 : ((25 + C) * T + N * L) * s ≤ Θ * s ^ 2 / 2 ^ (n + 2) := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right hsW hs0
      nlinarith
    have f1 : T * C ≤ T * C * s := by
      have h := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ T * C); linarith
    have f2 : (n : ℝ) * T ≤ s * T := mul_le_mul_of_nonneg_right hns (by linarith)
    have f3 : 12 * T ≤ 12 * T * s := by nlinarith
    have f4 : 5 * (N : ℝ) + 2 ≤ 7 * T * s := by
      have : (N : ℝ) ≤ T := by rw [hT]; nlinarith
      nlinarith
    have f5 : N * L ≤ N * L * s := by nlinarith
    have f6 : T * (Θ * s) ≤ T * (s / 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    nlinarith
  have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have eC : (C ^ R) ^ N ≤ Real.exp (T * C) := by
    have hCe : C ≤ Real.exp C := by have := Real.add_one_le_exp C; linarith
    calc (C ^ R) ^ N = C ^ (N * R) := by rw [← pow_mul, mul_comm]
      _ ≤ Real.exp C ^ (N * R) := pow_le_pow_left₀ (by linarith) hCe _
      _ = Real.exp (T * C) := by rw [← Real.exp_nat_mul, hT]; push_cast; ring_nf
  have eX : ((2 : ℝ) ^ ((n + 12) * R)) ^ N ≤ Real.exp ((n + 12) * T) := by
    calc ((2 : ℝ) ^ ((n + 12) * R)) ^ N = 2 ^ ((n + 12) * R * N) := by rw [← pow_mul]
      _ ≤ Real.exp 1 ^ ((n + 12) * R * N) := pow_le_pow_left₀ (by norm_num) he _
      _ = Real.exp ((n + 12) * T) := by rw [← Real.exp_nat_mul, hT]; push_cast; ring_nf
  have e2 : (2 : ℝ) ^ (5 * N + 2) ≤ Real.exp (5 * N + 2) := by
    calc (2 : ℝ) ^ (5 * N + 2) ≤ Real.exp 1 ^ (5 * N + 2) := pow_le_pow_left₀ (by norm_num) he _
      _ = Real.exp (5 * N + 2) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have eΘ : (1 / Θ) ^ N = Real.exp (N * L) := by
    rw [Real.exp_nat_mul, hL, Real.exp_log (by positivity)]
  have eE : (Real.exp (Θ * s) ^ R) ^ N = Real.exp (T * (Θ * s)) := by
    rw [← pow_mul, ← Real.exp_nat_mul, hT]; push_cast; ring_nf
  have es : (s ^ (4 * R)) ^ N ≤ Real.exp (4 * T * s) := by
    have h := Real.add_one_le_exp s
    calc (s ^ (4 * R)) ^ N = s ^ (4 * R * N) := by rw [← pow_mul]
      _ ≤ Real.exp s ^ (4 * R * N) := pow_le_pow_left₀ hs0 (by linarith) _
      _ = Real.exp (4 * T * s) := by rw [← Real.exp_nat_mul, hT]; push_cast; ring_nf
  set CR := C ^ R
  set X := (2 : ℝ) ^ ((n + 12) * R)
  set Y := Real.exp (Θ * s) ^ R
  set Z := s ^ (4 * R)
  have hCR : 0 ≤ CR := by positivity
  have hfin : CR ^ N * X ^ N * 2 ^ (5 * N + 2) * (1 / Θ) ^ N * Y ^ N * Z ^ N ≤
      Real.exp (Θ * s ^ 2 / 2 ^ (n + 2)) := by
    rw [eΘ, eE]
    calc CR ^ N * X ^ N * 2 ^ (5 * N + 2) * Real.exp (N * L) * Real.exp (T * (Θ * s)) * Z ^ N
        ≤ Real.exp (T * C) * Real.exp ((n + 12) * T) * Real.exp (5 * N + 2) * Real.exp (N * L) *
            Real.exp (T * (Θ * s)) * Real.exp (4 * T * s) := by
          gcongr
      _ = Real.exp (T * C + (n + 12) * T + (5 * N + 2) + N * L + T * (Θ * s) + 4 * T * s) := by
          simp only [← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr hexpo
  have hid : 8 * (CR * X * 16 * (Y * Z)) ^ N =
      2 * (Θ / 2) ^ N * (CR ^ N * X ^ N * 2 ^ (5 * N + 2) * (1 / Θ) ^ N * Y ^ N * Z ^ N) := by
    have e1 : (Θ / 2) ^ N * (1 / Θ) ^ N = (1 / 2) ^ N := by
      rw [← mul_pow]; congr 1; field_simp
    have e3 : (2 : ℝ) ^ (5 * N + 2) = 2 ^ N * 16 ^ N * 4 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add, show (4 : ℝ) = 2 ^ 2 by norm_num,
        ← pow_add]
      congr 1; ring
    have e2 : (1 / 2 : ℝ) ^ N * 2 ^ (5 * N + 2) = 4 * 16 ^ N := by
      rw [e3, show (1 / 2 : ℝ) ^ N * (2 ^ N * 16 ^ N * 4) = ((1 / 2) * 2) ^ N * 16 ^ N * 4 by
        rw [mul_pow]; ring]
      norm_num; ring
    calc 8 * (CR * X * 16 * (Y * Z)) ^ N = 2 * (4 * 16 ^ N) * (CR ^ N * X ^ N * Y ^ N * Z ^ N) := by
          ring
      _ = 2 * ((1 / 2) ^ N * 2 ^ (5 * N + 2)) * (CR ^ N * X ^ N * Y ^ N * Z ^ N) := by rw [e2]
      _ = 2 * ((Θ / 2) ^ N * (1 / Θ) ^ N * 2 ^ (5 * N + 2)) *
            (CR ^ N * X ^ N * Y ^ N * Z ^ N) := by rw [e1]
      _ = _ := by ring
  rw [hid]
  exact mul_le_mul_of_nonneg_left hfin (by positivity)

theorem win_le_base (hV0 : 0 ≤ V) (n : ℕ) : win V n ≤ V ^ 2 ^ n := by
  rcases n with _ | m
  · rw [win_zero]; positivity
  · rw [win_succ]

/-- The least height at level `n + 1`: `A ≤ (o + 2) 2^{n+5} e^{Θ V^{2^n}}`. -/
theorem lowH_succ_le (hΘ : 0 < Θ) (hV1 : 1 ≤ V) (n : ℕ) :
    (lowH o Θ V (n + 1) : ℝ) ≤ (o + 2) * 2 ^ (n + 5) * Real.exp (Θ * V ^ 2 ^ n) := by
  set s := V ^ 2 ^ n
  have hs0 : 0 ≤ s := by positivity
  have hy0 : 2 / hiW Θ V (n + 1) = 2 ^ (n + 2) * Real.exp (Θ * win V n) := by
    rw [div_eq_iff (hiW_pos (Θ := Θ) (V := V) (n + 1)).ne']
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
  have hy : (2 * (o : ℝ) + 4) / hiW Θ V (n + 1) =
      (o + 2) * (2 ^ (n + 2) * Real.exp (Θ * win V n)) := by
    rw [← hy0]; ring
  have hexp : Real.exp (Θ * win V n) ≤ Real.exp (Θ * s) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (win_le_base (by linarith) n) hΘ.le)
  have hexp1 : 1 ≤ Real.exp (Θ * s) := Real.one_le_exp (by positivity)
  have hceil := ceil_le_add_one (le_of_lt (div_pos (by positivity : (0 : ℝ) < 2 * (o : ℝ) + 4)
    (hiW_pos (Θ := Θ) (V := V) (n + 1))))
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
  have ho0 : (0 : ℝ) ≤ o := Nat.cast_nonneg o
  unfold lowH; push_cast
  rw [hy, e5]
  rw [e4] at hn
  have h6 := mul_le_mul_of_nonneg_left hexp h5.le
  have h7 := mul_le_mul_of_nonneg_left hexp1 h5.le
  have h8 := mul_le_mul_of_nonneg_left h6 (by linarith : (0 : ℝ) ≤ o + 2)
  have h9 : (n : ℝ) + 4 + 2 * o ≤ (o + 2) * (4 * (2 ^ (n + 2) * Real.exp (Θ * s))) := by
    have h10 : (n : ℝ) + 4 ≤ 4 * (2 ^ (n + 2) * Real.exp (Θ * s)) := by nlinarith
    have h11 : (n : ℝ) + 4 + 2 * o ≤ (o + 2) * (n + 4) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith
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
theorem height_le (k : ℕ) : (height o Θ V P k : ℝ) ≤
    2 * (2 * (lowH o Θ V k : ℝ) * (prec V k : ℝ)) ^ (r + 1) := by
  have h := (height_spec o Θ V P k).2.1
  have hA : (1 : ℝ) ≤ lowH o Θ V k := by exact_mod_cast (by unfold lowH; omega : 1 ≤ lowH o Θ V k)
  have hQ : (1 : ℝ) ≤ prec V k := by exact_mod_cast (by unfold prec; omega : 1 ≤ prec V k)
  have h' : (height o Θ V P k : ℝ) ≤ 2 * lowH o Θ V k + (2 * lowH o Θ V k * prec V k) ^ r := by
    exact_mod_cast h
  set y : ℝ := 2 * (lowH o Θ V k : ℝ) * (prec V k : ℝ)
  have hy1 : 1 ≤ y := by nlinarith
  have h1 : 2 * (lowH o Θ V k : ℝ) ≤ y ^ (r + 1) :=
    le_trans (by nlinarith) (le_self_pow₀ hy1 (by omega))
  have h2 : y ^ r ≤ y ^ (r + 1) := pow_le_pow_right₀ hy1 (by omega)
  linarith

/-- The weight from below: `2|c_k| ≥ 2(Θ/2)^{2(o+1)}/(7M_k)^{2(o+1)}`. -/
theorem wt_ge (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (k : ℕ) :
    2 * (Θ / 2) ^ (2 * (o + 1)) / (7 * (height o Θ V P k : ℝ)) ^ (2 * (o + 1)) ≤ wt o Θ V P k := by
  have hM1 : 1 ≤ height o Θ V P k := by
    have := two_mul_le_height (o := o) (Θ := Θ) (V := V) P k; omega
  have h1 := le_norm_sincPow hM1 (depth_nonneg hΘ k) ((depth_lt hΘ k).le.trans hΘ2) (o + 1)
  have h2 : (Θ / 2) ^ (2 * (o + 1)) / (7 * (height o Θ V P k : ℝ)) ^ (2 * (o + 1)) ≤
      depth Θ k ^ (2 * (o + 1)) / (7 * (height o Θ V P k : ℝ)) ^ (2 * (o + 1)) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) (half_le_depth hΘ k) _)
      (by positivity)
  unfold wt coef
  rw [mul_div_assoc]
  linarith

/-- The constant `W = ((27 + o) 2(o+1)(r+1) + 2(o+1) log(1/Θ))/Θ` of the windows. -/
def towerW (o r : ℕ) (Θ : ℝ) : ℝ :=
  ((27 + o) * (2 * (o + 1) * (r + 1)) + 2 * (o + 1) * Real.log (1 / Θ)) / Θ

theorem one_le_towerW (o r : ℕ) {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) : 1 ≤ towerW o r Θ := by
  have hL0 : 0 ≤ Real.log (1 / Θ) := Real.log_nonneg (by rw [le_div_iff₀ hΘ]; linarith)
  have ho : (0 : ℝ) ≤ o := Nat.cast_nonneg o
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  rw [towerW, le_div_iff₀ hΘ]
  have h1 : (54 : ℝ) ≤ (27 + o) * (2 * (o + 1) * (r + 1)) := by
    have h2 : (2 : ℝ) ≤ 2 * (o + 1) * (r + 1) := by nlinarith
    nlinarith
  have h3 : 0 ≤ 2 * ((o : ℝ) + 1) * Real.log (1 / Θ) := by positivity
  linarith

/-- **The takeover.** For `V ≥ 8W`, the weight of level `n + 1` exceeds the earlier ones from the
start of its window: `2|c_{n+1}| e^{(x_{n+1} − x_n)U_{n+1}} ≥ 8`. -/
theorem eight_le_wt_mul_exp (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (hV : 8 * towerW o r Θ ≤ V)
    (n : ℕ) :
    8 ≤ wt o Θ V P (n + 1) * Real.exp ((depth Θ (n + 1) - depth Θ n) * win V (n + 1)) := by
  have hW1 := one_le_towerW o r hΘ hΘ2
  have hV1 : 1 ≤ V := by linarith
  set s := V ^ 2 ^ n with hs
  have hsW := two_pow_mul_le_pow hW1 hV n
  rw [← hs] at hsW
  set N : ℕ := 2 * (o + 1)
  set R : ℕ := r + 1
  set C : ℝ := (o : ℝ) + 2
  have hC : 1 ≤ C := by have : (0 : ℝ) ≤ o := Nat.cast_nonneg o; simp only [C]; linarith
  have hsW' : 2 ^ (n + 2) * ((25 + C) * ((N : ℝ) * R) + N * Real.log (1 / Θ)) ≤ Θ * s := by
    have := mul_le_mul_of_nonneg_left hsW hΘ.le
    rw [towerW, show Θ * (2 ^ (n + 2) * (((27 + o) * (2 * (o + 1) * (r + 1)) +
      2 * (o + 1) * Real.log (1 / Θ)) / Θ)) = 2 ^ (n + 2) * ((27 + o) * (2 * (o + 1) * (r + 1)) +
      2 * (o + 1) * Real.log (1 / Θ)) by field_simp] at this
    have hnum : (25 + C) * ((N : ℝ) * R) + N * Real.log (1 / Θ) =
        (27 + o) * (2 * (o + 1) * (r + 1)) + 2 * (o + 1) * Real.log (1 / Θ) := by
      simp only [N, R, C]; push_cast; ring
    rw [hnum]; exact this
  have h2n : (1 : ℝ) ≤ 2 ^ (n + 2) := one_le_pow₀ (by norm_num)
  have hs1 : 1 ≤ s := le_trans (by nlinarith) hsW
  have hns : (n : ℝ) ≤ s := by
    have h : (n : ℝ) ≤ 2 ^ (n + 2) := by
      have : n ≤ 2 ^ (n + 2) := (Nat.lt_two_pow_self (n := n + 2)).le.trans' (by omega)
      exact_mod_cast this
    nlinarith
  have hkey := key_ineq hΘ hΘ2 hC n R N (by omega) (by omega) hs1 hns hsW'
  have hA := lowH_succ_le (o := o) (Θ := Θ) hΘ hV1 n
  have hQ := prec_succ_le hV1 n
  have hM := height_le (o := o) (Θ := Θ) (V := V) P (n + 1)
  have hwt := wt_ge (o := o) (V := V) P hΘ hΘ2 (n + 1)
  rw [← hs] at hA hQ
  have hA1 : (1 : ℝ) ≤ (lowH o Θ V (n + 1) : ℝ) := by
    exact_mod_cast (by unfold lowH; omega : 1 ≤ lowH o Θ V (n + 1))
  have hQ1 : (1 : ℝ) ≤ (prec V (n + 1) : ℝ) := by
    exact_mod_cast (by unfold prec; omega : 1 ≤ prec V (n + 1))
  have hM1 : (1 : ℝ) ≤ (height o Θ V P (n + 1) : ℝ) := by
    exact_mod_cast (by have := two_mul_le_height (o := o) (Θ := Θ) (V := V) P (n + 1); omega :
      1 ≤ height o Θ V P (n + 1))
  set A : ℝ := (lowH o Θ V (n + 1) : ℝ)
  set Q : ℝ := (prec V (n + 1) : ℝ)
  set M : ℝ := (height o Θ V P (n + 1) : ℝ)
  -- `7M ≤ 14(2AQ)^R ≤ C^R 2^{(n+12)R} 16 e^{RΘs} s^{4R}`
  have hbase : 7 * M ≤ C ^ R * 2 ^ ((n + 12) * R) * 16 *
      (Real.exp (Θ * s) ^ R * s ^ (4 * R)) := by
    have h2AQ : 2 * A * Q ≤ C * (2 ^ (n + 12) * (Real.exp (Θ * s) * s ^ 4)) := by
      have h1 : 2 * A * Q ≤ 2 * (C * 2 ^ (n + 5) * Real.exp (Θ * s)) * (39 * s ^ 4) :=
        mul_le_mul (by simp only [C]; linarith) hQ (by linarith) (by positivity)
      have e : (2 : ℝ) ^ (n + 12) = 2 ^ (n + 5) * 128 := by
        rw [show n + 12 = (n + 5) + 7 by ring, pow_add]; norm_num
      have hpos : 0 ≤ C * (2 ^ (n + 5) * (Real.exp (Θ * s) * s ^ 4)) := by positivity
      calc 2 * A * Q ≤ 2 * (C * 2 ^ (n + 5) * Real.exp (Θ * s)) * (39 * s ^ 4) := h1
        _ = 78 * (C * (2 ^ (n + 5) * (Real.exp (Θ * s) * s ^ 4))) := by ring
        _ ≤ 128 * (C * (2 ^ (n + 5) * (Real.exp (Θ * s) * s ^ 4))) :=
            mul_le_mul_of_nonneg_right (by norm_num) hpos
        _ = C * (2 ^ (n + 12) * (Real.exp (Θ * s) * s ^ 4)) := by rw [e]; ring
    have hpow := pow_le_pow_left₀ (by nlinarith) h2AQ R
    have e : (C * (2 ^ (n + 12) * (Real.exp (Θ * s) * s ^ 4))) ^ R =
        C ^ R * 2 ^ ((n + 12) * R) * (Real.exp (Θ * s) ^ R * s ^ (4 * R)) := by
      rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]; ring
    rw [e] at hpow
    have hpos : 0 ≤ C ^ R * 2 ^ ((n + 12) * R) * (Real.exp (Θ * s) ^ R * s ^ (4 * R)) := by
      positivity
    have hM' : M ≤ 2 * (2 * A * Q) ^ R := hM
    nlinarith
  have hdelta : (depth Θ (n + 1) - depth Θ n) * win V (n + 1) = Θ * s ^ 2 / 2 ^ (n + 2) := by
    rw [depth_succ_sub, win_succ, hs, ← pow_mul, ← pow_succ, one_div_pow]; ring
  rw [hdelta]
  set B := C ^ R * 2 ^ ((n + 12) * R) * 16 * (Real.exp (Θ * s) ^ R * s ^ (4 * R))
  have hB : 0 < B := by positivity
  have hwt' : 2 * (Θ / 2) ^ N / B ^ N ≤ wt o Θ V P (n + 1) :=
    le_trans (div_le_div_of_nonneg_left (by positivity) (pow_pos (by linarith) _)
      (pow_le_pow_left₀ (by linarith) hbase _)) hwt
  have hE : 0 < Real.exp (Θ * s ^ 2 / 2 ^ (n + 2)) := Real.exp_pos _
  calc (8 : ℝ) = 8 * B ^ N / B ^ N := by field_simp
    _ ≤ 2 * (Θ / 2) ^ N * Real.exp (Θ * s ^ 2 / 2 ^ (n + 2)) / B ^ N :=
        div_le_div_of_nonneg_right hkey (by positivity)
    _ = 2 * (Θ / 2) ^ N / B ^ N * Real.exp (Θ * s ^ 2 / 2 ^ (n + 2)) := by ring
    _ ≤ wt o Θ V P (n + 1) * Real.exp (Θ * s ^ 2 / 2 ^ (n + 2)) :=
        mul_le_mul_of_nonneg_right hwt' hE.le

/-! ### The configuration -/

theorem pt_true_re (k : ℕ) : (pt o Θ V P (k, true)).re = 1 / 2 + depth Θ k := by simp [pt]

theorem pt_false_re (k : ℕ) : (pt o Θ V P (k, false)).re = 1 / 2 - depth Θ k := by simp [pt]

theorem pt_im (kb : ℕ × Bool) : (pt o Θ V P kb).im = 2 * Real.pi * height o Θ V P kb.1 := by
  rcases kb with ⟨k, _ | _⟩ <;> simp [pt]

theorem depth_pos (hΘ : 0 < Θ) (k : ℕ) : 0 < depth Θ k :=
  lt_of_lt_of_le (by positivity) (half_le_depth hΘ k)

theorem pt_injective (hΘ : 0 < Θ) : Function.Injective (pt o Θ V P) := by
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

theorem reflect_pt (k : ℕ) (b : Bool) : reflect (pt o Θ V P (k, b)) = pt o Θ V P (k, !b) := by
  apply Complex.ext <;> cases b <;> simp [reflect, pt] <;> ring

variable (o V)

/-- **The configuration** `{½ ± x_k + 2πiM_k}` with multiplicity one. -/
def config (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) : ZeroConfig where
  carrier := Set.range (pt o Θ V P)
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
    exact ⟨(k, !b), (reflect_pt (V := V) P k b).symm⟩
  mult_reflect := fun _ _ => rfl
  finite_window := by
    intro T₁ T₂
    refine (((Set.finite_Iic ⌊T₂⌋₊).prod (Set.finite_univ (α := Bool))).image (pt o Θ V P)).subset ?_
    rintro ρ ⟨⟨⟨k, b⟩, rfl⟩, -, hT⟩
    refine ⟨(k, b), ⟨Set.mem_Iic.mpr ?_, Set.mem_univ _⟩, rfl⟩
    rw [pt_im] at hT
    have hk : (k : ℝ) ≤ height o Θ V P k := by exact_mod_cast k_le_height P k
    have hM0 : (0 : ℝ) ≤ height o Θ V P k := Nat.cast_nonneg _
    have : (k : ℝ) ≤ T₂ := by nlinarith [Real.pi_gt_three]
    exact Nat.le_floor this

variable {o V}

theorem gammaOf_pt_true (k : ℕ) :
    gammaOf (pt o Θ V P (k, true)) = splinePoint (height o Θ V P k) (depth Θ k) := by
  apply Complex.ext <;> simp [gammaOf, pt, splinePoint, Complex.div_I]

theorem gammaOf_pt_false (k : ℕ) :
    gammaOf (pt o Θ V P (k, false)) = conj (splinePoint (height o Θ V P k) (depth Θ k)) := by
  apply Complex.ext <;> simp [gammaOf, pt, splinePoint, Complex.div_I]

theorem normSq_gammaOf_pt_ge (kb : ℕ × Bool) :
    (kb.1 : ℝ) ^ 2 ≤ Complex.normSq (gammaOf (pt o Θ V P kb)) := by
  have hre : (gammaOf (pt o Θ V P kb)).re = 2 * Real.pi * height o Θ V P kb.1 := by
    rcases kb with ⟨k, _ | _⟩
    · rw [gammaOf_pt_false, Complex.conj_re, splinePoint_re]
    · rw [gammaOf_pt_true, splinePoint_re]
  rw [Complex.normSq_apply, hre]
  have hk : (kb.1 : ℝ) ≤ height o Θ V P kb.1 := by exact_mod_cast k_le_height P kb.1
  have h0 : (0 : ℝ) ≤ kb.1 := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ height o Θ V P kb.1 := Nat.cast_nonneg _
  have h1 : (kb.1 : ℝ) ≤ 2 * Real.pi * height o Θ V P kb.1 := by nlinarith [Real.pi_gt_three]
  have h2 := mul_le_mul h1 h1 h0 (h0.trans h1)
  nlinarith [mul_self_nonneg (gammaOf (pt o Θ V P kb)).im]

theorem temperedConfig_config (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    TemperedConfig (config o V P hΘ hΘ2) := by
  unfold TemperedConfig
  set e := Equiv.ofInjective (pt o Θ V P) (pt_injective P hΘ)
  show Summable fun ρ : Set.range (pt o Θ V P) => ((1 : ℕ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
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
    (by linarith [Complex.normSq_nonneg (gammaOf (pt o Θ V P kb))])) (fun kb => ?_) hg
  exact one_div_le_one_div_of_le (by positivity) (by linarith [normSq_gammaOf_pt_ge (o := o) (Θ := Θ) (V := V) P kb])

/-! ### The traces -/

theorem contDiff_two_boxSpline {o : ℕ} (ho : 3 ≤ o) : ContDiff ℝ 2 (boxSpline 1 o) := by
  obtain ⟨m, rfl⟩ : ∃ m, o = m + 3 := ⟨o - 3, by omega⟩
  exact (contDiff_boxSpline (r := 1) one_pos (m + 2)).of_le (by exact_mod_cast (by omega : 2 ≤ m + 2))

theorem paperFT_weilTest_spline {o : ℕ} (ho : 3 ≤ o) (w : ℂ) :
    paperFT (EF.weilTest (boxSpline 1 o) (boxSpline 1 o)) w = sincC w ^ (2 * (o + 1)) := by
  have hb := (contDiff_two_boxSpline ho).continuous
  have hbc := hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos o)
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
theorem two_re_lagStructure_config (ho : 3 ≤ o) (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (u : ℝ) :
    2 * (lagStructure (config o V P hΘ hΘ2) (boxSpline 1 o) u).re =
      ∑' k, (Real.exp (depth Θ k * u) * (2 * (coef o Θ V P k *
          cexp (((2 * Real.pi * height o Θ V P k * u : ℝ) : ℂ) * I)).re) +
        Real.exp (-(depth Θ k * u)) * (2 * (conj (coef o Θ V P k) *
          cexp (((2 * Real.pi * height o Θ V P k * u : ℝ) : ℂ) * I)).re)) := by
  set Z := config o V P hΘ hΘ2
  have hb3 := contDiff_two_boxSpline ho
  have hbs := boxSpline_support (r := 1) one_pos o
  have hs := summable_lagStructure Z (temperedConfig_config P hΘ hΘ2) hb3 hbs u
  set e := Equiv.ofInjective (pt o Θ V P) (pt_injective P hΘ)
  set F : ℕ × Bool → ℂ := fun kb => paperFT (EF.weilTest (boxSpline 1 o) (boxSpline 1 o))
    (gammaOf (pt o Θ V P kb)) * cexp (I * gammaOf (pt o Θ V P kb) * u) with hF
  have hcomp : ∀ kb, ((Z.mult (e kb) : ℂ) * paperFT (EF.weilTest (boxSpline 1 o) (boxSpline 1 o))
      (gammaOf (e kb)) * cexp (I * gammaOf (e kb) * u)) = F kb := by
    intro kb
    simp only [Z, config, e, Equiv.ofInjective_apply, Nat.cast_one, one_mul, hF]
  have hS : HasSum F (lagStructure Z (boxSpline 1 o) u) := by
    have h1 := ((e.hasSum_iff).mpr hs.hasSum)
    simp only [Function.comp_def, hcomp] at h1
    exact h1
  -- the fibre over level `k`
  set g : ℕ → ℂ := fun k => coef o Θ V P k * (Real.exp (depth Θ k * u) : ℂ) *
      cexp (((2 * Real.pi * height o Θ V P k * u : ℝ) : ℂ) * I) +
    conj (coef o Θ V P k) * (Real.exp (-(depth Θ k * u)) : ℂ) *
      cexp (((2 * Real.pi * height o Θ V P k * u : ℝ) : ℂ) * I) with hg
  have hfib : ∀ k, HasSum (fun b : Bool => F (k, b)) (g k) := by
    intro k
    have h := hasSum_fintype (fun b : Bool => F (k, b))
    rw [Fintype.sum_bool] at h
    convert h using 1
    simp only [hF, hg, gammaOf_pt_true, gammaOf_pt_false, paperFT_weilTest_spline ho, sincC_conj,
      map_pow, I_mul_splinePoint, I_mul_conj_splinePoint, Complex.exp_add, ← Complex.ofReal_exp,
      coef]
    ring
  have hG : HasSum g (lagStructure Z (boxSpline 1 o) u) := hS.prod_fiberwise hfib
  have hre := (Complex.reCLM.hasSum hG).mul_left 2
  simp only [Complex.reCLM_apply] at hre
  rw [← hre.tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [hg, Complex.add_re]
  rw [show coef o Θ V P k * (Real.exp (depth Θ k * u) : ℂ) *
      cexp (((2 * Real.pi * height o Θ V P k * u : ℝ) : ℂ) * I) =
      (Real.exp (depth Θ k * u) : ℂ) * (coef o Θ V P k *
        cexp (((2 * Real.pi * height o Θ V P k * u : ℝ) : ℂ) * I)) by ring,
    show conj (coef o Θ V P k) * (Real.exp (-(depth Θ k * u)) : ℂ) *
      cexp (((2 * Real.pi * height o Θ V P k * u : ℝ) : ℂ) * I) =
      (Real.exp (-(depth Θ k * u)) : ℂ) * (conj (coef o Θ V P k) *
        cexp (((2 * Real.pi * height o Θ V P k * u : ℝ) : ℂ) * I)) by ring,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

end SplineTower

open SplineTower in
/-- **The blind side of finitely many Frobenii is the sign of `B̂²` at the zeros of `B̂`.** For the
spline of order `o ≥ 3`, every finite family of primes `P₁, …, P_r` and `0 < Θ ≤ ½`, there is a
tempered zero configuration without real zeros whose real parts have the supremum `½ + Θ`, not
attained, and whose spline traces satisfy `(−1)^{o+1} 2 Re S(Σ aᵢ log Pᵢ) ≥ −5` at every degree. -/
theorem exists_zeroConfig_finPrimes_signed_nonattained {o : ℕ} (ho : 3 ≤ o) {r : ℕ}
    (P : Fin r → ℕ) (hP : ∀ i, (P i).Prime) {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧ (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1 / 2 + Θ) ∧ (∀ β < 1 / 2 + Θ, ∃ ρ ∈ Z.carrier, β < ρ.re) ∧
      ∀ a : Fin r → ℕ, -5 ≤ (-1) ^ (o + 1) *
        (2 * (lagStructure Z (boxSpline 1 o) (∑ i, (a i : ℝ) * Real.log (P i))).re) := by
  set V : ℝ := 8 * towerW o r Θ with hVdef
  have hW1 := one_le_towerW o r hΘ hΘ2
  have hV8 : 8 ≤ V := by rw [hVdef]; linarith
  have hV1 : 1 ≤ V := by linarith
  refine ⟨config o V P hΘ hΘ2, temperedConfig_config P hΘ hΘ2, ?_, ?_, ?_, fun a => ?_⟩
  · rintro ρ ⟨kb, rfl⟩
    rw [pt_im]
    have := two_mul_le_height (o := o) (Θ := Θ) (V := V) P kb.1
    have hM : (0 : ℝ) < height o Θ V P kb.1 := by
      exact_mod_cast (by omega : 0 < height o Θ V P kb.1)
    positivity
  · rintro ρ ⟨⟨k, b⟩, rfl⟩
    have h1 := depth_lt hΘ k
    have h0 := depth_nonneg hΘ k
    cases b
    · rw [pt_false_re]; linarith
    · rw [pt_true_re]; linarith
  · intro β hβ
    obtain ⟨k, hk⟩ := exists_depth_gt hΘ (show β - 1 / 2 < Θ by linarith)
    exact ⟨pt o Θ V P (k, true), ⟨(k, true), rfl⟩, by rw [pt_true_re]; linarith⟩
  · set lam := ∑ i, (a i : ℝ) * Real.log (P i) with hlam
    have hlam0 : 0 ≤ lam := Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by exact_mod_cast (hP i).one_lt.le))
    rw [two_re_lagStructure_config P ho hΘ hΘ2, ← tsum_mul_left]
    obtain ⟨k, hkl, hku⟩ := exists_window (monotone_win hV1) (by rw [win_zero]; exact hlam0)
      (exists_le_win (by linarith) lam)
    set σ : ℝ := (-1) ^ (o + 1)
    have hσ : |σ| = 1 := by simp [σ]
    -- the phases of level `j` are within `¼` of `1` on `[0, U_{j+1}]`
    have hph : ∀ j, lam ≤ win V (j + 1) → wt o Θ V P j / 2 ≤
        σ * (2 * (coef o Θ V P j * cexp (((2 * Real.pi * height o Θ V P j * lam : ℝ) : ℂ) *
          I)).re) := by
      intro j hj
      have hres := norm_exp_height_sub_one_le (o := o) (Θ := Θ) P hP hV1 j a hj
      have h := re_sincPow_mul_exp_ge (k := o + 1) (by omega)
        (two_mul_le_height (o := o) (Θ := Θ) (V := V) P j)
        (depth_nonneg hΘ j) ((depth_lt hΘ j).le.trans hΘ2) hres
      unfold wt coef
      simp only [σ]
      linarith
    have hnorm : ∀ j (c : ℂ), |σ * (2 * (c * cexp (((2 * Real.pi * height o Θ V P j * lam : ℝ) :
        ℂ) * I)).re)| ≤ 2 * ‖c‖ := by
      intro j c
      rw [abs_mul, hσ, one_mul, abs_mul, abs_two]
      refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by norm_num)
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hterm : ∀ j, σ * (Real.exp (depth Θ j * lam) * (2 * (coef o Θ V P j *
        cexp (((2 * Real.pi * height o Θ V P j * lam : ℝ) : ℂ) * I)).re) +
        Real.exp (-(depth Θ j * lam)) * (2 * (conj (coef o Θ V P j) *
          cexp (((2 * Real.pi * height o Θ V P j * lam : ℝ) : ℂ) * I)).re)) =
        Real.exp (depth Θ j * lam) * (σ * (2 * (coef o Θ V P j *
          cexp (((2 * Real.pi * height o Θ V P j * lam : ℝ) : ℂ) * I)).re)) +
        Real.exp (-(depth Θ j * lam)) * (σ * (2 * (conj (coef o Θ V P j) *
          cexp (((2 * Real.pi * height o Θ V P j * lam : ℝ) : ℂ) * I)).re)) := fun j => by ring
    simp only [hterm]
    refine neg_five_le_tsum_of_window hΘ (x := depth Θ) (w := wt o Θ V P) (U := win V)
      (fun j => depth_nonneg hΘ j) (fun j => (depth_lt hΘ j).le) (strictMono_depth hΘ).monotone
      (wt_nonneg P) ?_ ?_ (monotone_win hV1) (le_of_eq win_zero.symm) (fun j => ?_) (fun j => ?_)
      hlam0 hkl hku (hph k hku) ?_ ?_
    · have := wt_le_hiW (o := o) (V := V) P hΘ hΘ2 0
      simpa [hiW] using this
    · intro j
      have := wt_le_hiW (o := o) (V := V) P hΘ hΘ2 (j + 1)
      simpa [hiW] using this
    · exact hnorm j _
    · have h := hnorm j (conj (coef o Θ V P j))
      rwa [Complex.norm_conj] at h
    · exact le_trans (by have := wt_nonneg (o := o) (Θ := Θ) (V := V) P (k + 1); linarith)
        (hph (k + 1) (hku.trans (monotone_win hV1 (Nat.le_succ _))))
    · rintro n rfl
      exact eight_le_wt_mul_exp P hΘ hΘ2 le_rfl n

/-- **Zero configurations need an attained top at finitely many Frobenii** (cubic spline, from
below). -/
theorem exists_zeroConfig_finPrimes_bddBelow_nonattained {r : ℕ} (P : Fin r → ℕ)
    (hP : ∀ i, (P i).Prime) {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧ (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1 / 2 + Θ) ∧ (∀ β < 1 / 2 + Θ, ∃ ρ ∈ Z.carrier, β < ρ.re) ∧
      ∀ a : Fin r → ℕ,
        -5 ≤ 2 * (lagStructure Z (boxSpline 1 3) (∑ i, (a i : ℝ) * Real.log (P i))).re := by
  obtain ⟨Z, h1, h2, h3, h4, h5⟩ := exists_zeroConfig_finPrimes_signed_nonattained le_rfl P hP hΘ hΘ2
  refine ⟨Z, h1, h2, h3, h4, fun a => ?_⟩
  have := h5 a
  norm_num at this
  exact this

/-- **The other side for the quartic spline.** For the spline of order `4` the coefficients at the
zeros of `B̂` are negative, and the same towers keep the traces bounded above at every degree of a
finite family of primes, with an unattained top. -/
theorem exists_zeroConfig_finPrimes_bddAbove_nonattained_quartic {r : ℕ} (P : Fin r → ℕ)
    (hP : ∀ i, (P i).Prime) {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧ (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1 / 2 + Θ) ∧ (∀ β < 1 / 2 + Θ, ∃ ρ ∈ Z.carrier, β < ρ.re) ∧
      ∀ a : Fin r → ℕ,
        2 * (lagStructure Z (boxSpline 1 4) (∑ i, (a i : ℝ) * Real.log (P i))).re ≤ 5 := by
  obtain ⟨Z, h1, h2, h3, h4, h5⟩ :=
    exists_zeroConfig_finPrimes_signed_nonattained (by norm_num : 3 ≤ 4) P hP hΘ hΘ2
  refine ⟨Z, h1, h2, h3, h4, fun a => ?_⟩
  have := h5 a
  norm_num at this
  linarith

end GaloisForLFunctions.SurfaceOfSpecZ
