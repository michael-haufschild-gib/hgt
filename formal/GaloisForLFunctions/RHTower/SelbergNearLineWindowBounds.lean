import GaloisForLFunctions.RHTower.SelbergNearLineGaussianField

/-!
# Pointwise and edge bounds for the Gaussian-windowed mollified tail

For the windowed field `F_τ(z) = exp((z − iτ)²/H²) W_N(z)` on the strip `1/4 ≤ Re z ≤ 3`:

* `F_τ` is bounded, `‖F_τ(z)‖ ≤ e C N (1+|τ|)(1+H)` (`norm_nearLineWindowField_le`);
* on the right edge every window of length `2H` has mean square at most `16H/N²`
  (`integral_nearLineWindowField_three_le`);
* on a left line `Re z = σ ≤ 1/2`, at distance `D` from `τ`, the Gaussian beats the linear growth:
  `‖F_τ‖² ≤ 8 C² N² (1+|τ|)² H² e^{−D²/H²}` (`normSq_nearLineWindowField_far_le`);
* on the center line `1/2 ≤ Re z ≤ 1`, inside the window, the tail is dominated by the field,
  `‖ζΨ_N − 1 − P_N‖² ≤ 2e² ‖F_τ‖²` (`normSq_hbMollifiedTail_le_window`).
-/

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

theorem exp_neg_le_inv_one_add {y : ℝ} (hy : 0 ≤ y) : Real.exp (-y) ≤ 1 / (1 + y) := by
  rw [Real.exp_neg, ← one_div, one_div_le_one_div (Real.exp_pos y) (by linarith)]
  linarith [Real.add_one_le_exp y]

theorem mul_exp_neg_sq_div_le {x H : ℝ} (hx : 0 ≤ x) (hH : 0 < H) :
    x * Real.exp (-(x ^ 2 / H ^ 2)) ≤ H := by
  have h := exp_neg_le_inv_one_add (y := x ^ 2 / H ^ 2) (by positivity)
  calc x * Real.exp (-(x ^ 2 / H ^ 2)) ≤ x * (1 / (1 + x ^ 2 / H ^ 2)) :=
        mul_le_mul_of_nonneg_left h hx
    _ = x * H ^ 2 / (H ^ 2 + x ^ 2) := by field_simp
    _ ≤ H := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg hH.le (sq_nonneg (x - H / 2)), pow_pos hH 3]

theorem sq_mul_exp_neg_sq_div_le {x H : ℝ} (hH : 0 < H) :
    x ^ 2 * Real.exp (-(x ^ 2 / H ^ 2)) ≤ H ^ 2 := by
  have h := exp_neg_le_inv_one_add (y := x ^ 2 / H ^ 2) (by positivity)
  calc x ^ 2 * Real.exp (-(x ^ 2 / H ^ 2)) ≤ x ^ 2 * (1 / (1 + x ^ 2 / H ^ 2)) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg x)
    _ = x ^ 2 * H ^ 2 / (H ^ 2 + x ^ 2) := by field_simp
    _ ≤ H ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg x, sq_nonneg H, mul_nonneg (sq_nonneg H) (sq_nonneg H)]

theorem norm_nearLineGauss_eq (H τ : ℝ) (z : ℂ) :
    ‖nearLineGauss H τ z‖ = Real.exp ((z.re ^ 2 - (z.im - τ) ^ 2) / H ^ 2) := by
  conv_lhs => rw [← Complex.re_add_im z]
  exact norm_nearLineGauss H τ z.re z.im

theorem norm_nearLineGauss_le {H τ : ℝ} (hH : 3 ≤ H) {z : ℂ} (hz : |z.re| ≤ 3) :
    ‖nearLineGauss H τ z‖ ≤ Real.exp 1 * Real.exp (-((z.im - τ) ^ 2 / H ^ 2)) := by
  rw [norm_nearLineGauss_eq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hH0 : 0 < H := by linarith
  have hre : z.re ^ 2 ≤ 9 := by nlinarith [abs_le.mp hz, sq_abs z.re]
  have hH9 : 9 ≤ H ^ 2 := by nlinarith
  rw [sub_div]
  have : z.re ^ 2 / H ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  linarith

/-- **The windowed field is bounded on the strip.** -/
theorem norm_nearLineWindowField_le {N : ℕ} {H τ CW : ℝ} (hH : 3 ≤ H) (hCW : 0 ≤ CW)
    (hW : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField N z‖ ≤ CW * N * (1 + |z.im|))
    {z : ℂ} (hz : 1 / 4 ≤ z.re) (hz' : z.re ≤ 3) :
    ‖nearLineWindowField N H τ z‖ ≤ Real.exp 1 * (CW * N * ((1 + |τ|) * (1 + H))) := by
  have hH0 : 0 < H := by linarith
  unfold nearLineWindowField
  rw [norm_mul]
  set x : ℝ := |z.im - τ| with hx
  have hx0 : 0 ≤ x := abs_nonneg _
  have hG := norm_nearLineGauss_le (τ := τ) hH (z := z) (abs_le.mpr ⟨by linarith, hz'⟩)
  have hsq : (z.im - τ) ^ 2 = x ^ 2 := (sq_abs _).symm
  rw [hsq] at hG
  have hWz := hW z hz hz'
  have him : 1 + |z.im| ≤ (1 + |τ|) * (1 + x) := by
    have : |z.im| ≤ |τ| + x := by
      have := abs_sub_abs_le_abs_sub z.im τ
      rw [hx]; linarith
    nlinarith [abs_nonneg τ]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hWz' : ‖nearLineField N z‖ ≤ CW * N * ((1 + |τ|) * (1 + x)) :=
    hWz.trans (mul_le_mul_of_nonneg_left him (by positivity))
  have hkey : (1 + x) * Real.exp (-(x ^ 2 / H ^ 2)) ≤ 1 + H := by
    have h1 := mul_exp_neg_sq_div_le hx0 hH0
    have h2 : Real.exp (-(x ^ 2 / H ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : 0 ≤ x ^ 2 / H ^ 2 := by positivity
      linarith)
    nlinarith
  calc ‖nearLineGauss H τ z‖ * ‖nearLineField N z‖
      ≤ (Real.exp 1 * Real.exp (-(x ^ 2 / H ^ 2))) * (CW * N * ((1 + |τ|) * (1 + x))) :=
        mul_le_mul hG hWz' (norm_nonneg _) (by positivity)
    _ = Real.exp 1 * (CW * N * (1 + |τ|)) * ((1 + x) * Real.exp (-(x ^ 2 / H ^ 2))) := by ring
    _ ≤ Real.exp 1 * (CW * N * (1 + |τ|)) * (1 + H) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = Real.exp 1 * (CW * N * ((1 + |τ|) * (1 + H))) := by ring

theorem continuous_nearLineWindowField_line (N : ℕ) (H τ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Continuous fun u : ℝ => nearLineWindowField N H τ ((σ : ℂ) + (u : ℂ) * I) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hc : ContinuousOn (nearLineWindowField N H τ) {z : ℂ | 0 < z.re} :=
    (differentiableOn_nearLineWindowField N H τ).continuousOn
  refine hc.comp_continuous (by fun_prop) fun u => ?_
  show 0 < ((σ : ℂ) + (u : ℂ) * I).re
  simpa using hσ

/-- **Right edge.** Every window of length `2H` on `Re z = 3` has mean square `≤ 16H/N²`. -/
theorem integral_nearLineWindowField_three_le {N : ℕ} (hN : 2 ≤ N) {H τ : ℝ} (hH : 6 ≤ H)
    (y : ℝ) :
    ∫ t in (τ - H)..(τ + H),
        ‖nearLineWindowField N H τ ((3 : ℝ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ 16 * H / N ^ 2 := by
  have hH0 : 0 < H := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpt : ∀ t : ℝ, ‖nearLineWindowField N H τ ((3 : ℝ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤
      8 / N ^ 2 := by
    intro t
    unfold nearLineWindowField
    rw [norm_mul, mul_pow]
    have hG : ‖nearLineGauss H τ ((3 : ℝ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ 2 := by
      rw [norm_nearLineGauss, ← Real.exp_nat_mul]
      have h1 : (2 : ℕ) * ((3 ^ 2 - (y + t - τ) ^ 2) / H ^ 2) ≤ 1 / 2 := by
        have hH2 : 36 ≤ H ^ 2 := by nlinarith
        rw [mul_div_assoc']
        push_cast
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (y + t - τ)]
      calc Real.exp ((2 : ℕ) * ((3 ^ 2 - (y + t - τ) ^ 2) / H ^ 2)) ≤ Real.exp (1 / 2) :=
            Real.exp_le_exp.mpr h1
        _ ≤ 2 := by
            have he : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
              rw [← Real.exp_nat_mul]; norm_num
            have hlt := Real.exp_one_lt_d9
            nlinarith [Real.exp_pos (1 / 2)]
    have hW : ‖nearLineField N ((3 : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ (2 / N) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_nearLineField_three_le hN _) 2
    have hcast : ((3 : ℝ) : ℂ) = (3 : ℂ) := by norm_num
    rw [hcast] at hG ⊢
    calc ‖nearLineGauss H τ ((3 : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 *
          ‖nearLineField N ((3 : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ 2 * (2 / N) ^ 2 :=
          mul_le_mul hG hW (sq_nonneg _) (by norm_num)
      _ = 8 / N ^ 2 := by ring
  have hint : IntervalIntegrable
      (fun t : ℝ => ‖nearLineWindowField N H τ ((3 : ℝ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2)
      volume (τ - H) (τ + H) := by
    have hc := continuous_nearLineWindowField_line N H τ (σ := 3) (by norm_num)
    exact ((hc.comp (continuous_const.add continuous_id)).norm.pow 2).intervalIntegrable _ _
  calc ∫ t in (τ - H)..(τ + H),
        ‖nearLineWindowField N H τ ((3 : ℝ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2
      ≤ ∫ _t in (τ - H)..(τ + H), (8 / N ^ 2 : ℝ) :=
        intervalIntegral.integral_mono_on (by linarith) hint intervalIntegrable_const
          fun t _ => hpt t
    _ = 16 * H / N ^ 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring

/-- **Far part of a left line.** At distance `D` from the window center the Gaussian dominates. -/
theorem normSq_nearLineWindowField_far_le {N : ℕ} {H τ CW D σ u : ℝ} (hH : 3 ≤ H) (hCW : 0 ≤ CW)
    (hW : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField N z‖ ≤ CW * N * (1 + |z.im|))
    (hσ : 1 / 4 ≤ σ) (hσ' : σ ≤ 1 / 2) (hD : 0 ≤ D) (hu : D ≤ |u - τ|) :
    ‖nearLineWindowField N H τ ((σ : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
      8 * CW ^ 2 * N ^ 2 * (1 + |τ|) ^ 2 * H ^ 2 * Real.exp (-(D ^ 2 / H ^ 2)) := by
  have hH0 : 0 < H := by linarith
  set x : ℝ := |u - τ| with hx
  have hx0 : 0 ≤ x := abs_nonneg _
  unfold nearLineWindowField
  rw [norm_mul, mul_pow, norm_nearLineGauss]
  have hG : Real.exp ((σ ^ 2 - (u - τ) ^ 2) / H ^ 2) ^ 2 ≤
      2 * Real.exp (-(x ^ 2 / H ^ 2)) * Real.exp (-(x ^ 2 / H ^ 2)) := by
    rw [← Real.exp_nat_mul, show (u - τ) ^ 2 = x ^ 2 from (sq_abs _).symm]
    have hsplit : ((2 : ℕ) : ℝ) * ((σ ^ 2 - x ^ 2) / H ^ 2) =
        2 * σ ^ 2 / H ^ 2 + (-(x ^ 2 / H ^ 2)) + (-(x ^ 2 / H ^ 2)) := by
      push_cast; ring
    rw [hsplit, Real.exp_add, Real.exp_add]
    have h1 : Real.exp (2 * σ ^ 2 / H ^ 2) ≤ 2 := by
      have : 2 * σ ^ 2 / H ^ 2 ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      calc Real.exp (2 * σ ^ 2 / H ^ 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr this
        _ ≤ 2 := by
            have he : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
              rw [← Real.exp_nat_mul]; norm_num
            have hlt := Real.exp_one_lt_d9
            nlinarith [Real.exp_pos (1 / 2)]
    have hp := Real.exp_pos (-(x ^ 2 / H ^ 2))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hp.le) hp.le
  have hWz : ‖nearLineField N ((σ : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
      (CW * N * ((1 + |τ|) * (1 + x))) ^ 2 := by
    have h := hW ((σ : ℂ) + (u : ℂ) * I) (by simpa using hσ) (by simp; linarith)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at h
    have him : 1 + |u| ≤ (1 + |τ|) * (1 + x) := by
      have : |u| ≤ |τ| + x := by
        have := abs_sub_abs_le_abs_sub u τ
        rw [hx]; linarith
      nlinarith [abs_nonneg τ]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact pow_le_pow_left₀ (norm_nonneg _)
      (h.trans (mul_le_mul_of_nonneg_left him (by positivity))) 2
  have hkey : (1 + x) ^ 2 * Real.exp (-(x ^ 2 / H ^ 2)) ≤ 4 * H ^ 2 := by
    have h1 := sq_mul_exp_neg_sq_div_le (x := x) hH0
    have h2 : Real.exp (-(x ^ 2 / H ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : 0 ≤ x ^ 2 / H ^ 2 := by positivity
      linarith)
    have h3 : (1 + x) ^ 2 ≤ 2 + 2 * x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
    have hp := Real.exp_pos (-(x ^ 2 / H ^ 2))
    have hH9 : 9 ≤ H ^ 2 := by nlinarith
    nlinarith
  have hDx : Real.exp (-(x ^ 2 / H ^ 2)) ≤ Real.exp (-(D ^ 2 / H ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have : D ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hD hu 2
    have := div_le_div_of_nonneg_right this (by positivity : (0 : ℝ) ≤ H ^ 2)
    linarith
  have hE0 := Real.exp_pos (-(x ^ 2 / H ^ 2))
  calc Real.exp ((σ ^ 2 - (u - τ) ^ 2) / H ^ 2) ^ 2 * ‖nearLineField N ((σ : ℂ) + (u : ℂ) * I)‖ ^ 2
      ≤ (2 * Real.exp (-(x ^ 2 / H ^ 2)) * Real.exp (-(x ^ 2 / H ^ 2))) *
        (CW * N * ((1 + |τ|) * (1 + x))) ^ 2 :=
        mul_le_mul hG hWz (sq_nonneg _) (by positivity)
    _ = 2 * CW ^ 2 * N ^ 2 * (1 + |τ|) ^ 2 * Real.exp (-(x ^ 2 / H ^ 2)) *
        ((1 + x) ^ 2 * Real.exp (-(x ^ 2 / H ^ 2))) := by ring
    _ ≤ 2 * CW ^ 2 * N ^ 2 * (1 + |τ|) ^ 2 * Real.exp (-(D ^ 2 / H ^ 2)) * (4 * H ^ 2) := by
        gcongr
    _ = 8 * CW ^ 2 * N ^ 2 * (1 + |τ|) ^ 2 * H ^ 2 * Real.exp (-(D ^ 2 / H ^ 2)) := by ring

/-- **Center line.** Inside the window the tail is dominated by the windowed field. -/
theorem normSq_hbMollifiedTail_le_window {N : ℕ} {H τ σ t : ℝ} (hH : 0 < H)
    (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 1) (ht : |t - τ| ≤ H) (ht1 : 1 ≤ |t|) :
    ‖hbMollifiedTail N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      2 * Real.exp 2 * ‖nearLineWindowField N H τ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have h1 := norm_hbMollifiedTail_sq_le_two_mul (N := N) (z := (σ : ℂ) + (t : ℂ) * I)
    (by simpa using hσ) (by simpa using hσ') (by simpa using ht1)
  unfold nearLineWindowField
  rw [norm_mul, mul_pow, norm_nearLineGauss]
  have hG : 1 ≤ Real.exp 2 * Real.exp ((σ ^ 2 - (t - τ) ^ 2) / H ^ 2) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp
    have hsq : (t - τ) ^ 2 ≤ H ^ 2 := by
      have := sq_abs (t - τ)
      nlinarith [abs_nonneg (t - τ)]
    have : (t - τ) ^ 2 / H ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact hsq
    have h2 : 0 ≤ σ ^ 2 / H ^ 2 := by positivity
    rw [sub_div]
    push_cast
    linarith
  have hW0 := sq_nonneg ‖nearLineField N ((σ : ℂ) + (t : ℂ) * I)‖
  nlinarith

end RHTower
