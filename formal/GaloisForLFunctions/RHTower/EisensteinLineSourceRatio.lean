import GaloisForLFunctions.RHTower.EisensteinLineSourceMeanSquare
import GaloisForLFunctions.RHTower.ZetaOneLineLogPowerLowerBound

/-!
# The mean square of the Eisenstein source relative to `‖Λ(1+2it)‖⁴`

The mean-square bound `Vb(t) = 128‖Λ‖⁴ H + 256‖Λ‖² P₂ (log t + 1) + 2K(t)` is compared with
`‖Λ‖⁴`.  Every term other than the first carries at most two powers of `‖Λ‖` in the numerator
and exponential factors `e^{-πt}` from the Bessel bounds, while `‖Λ‖² ≥ e^{-πt} ‖ζ(1+2it)‖²` and
`‖ζ(1+2it)‖ ≥ c / log(2t)^{11}` unconditionally.  Hence

`Vb(t) ≤ ‖Λ‖⁴ · (128 H + B · t^{5/3} (log t)^{50})`

for all large `t`, with an explicit `B`.  Since `t^{5/3} (log t)^{50} = o(t²)`, the dominance
condition of the on-line sign law holds for all large `t`.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- The growth function `t^{5/3} (log t)^{50}`. -/
def growth (t : ℝ) : ℝ := t ^ (5 / 3 : ℝ) * Real.log t ^ 50

/-- The mean-square bound of the source. -/
def vBound (t : ℝ) : ℝ :=
  128 * ‖eisLineLambda t‖ ^ 4 * sourceHeight +
    256 * ‖eisLineLambda t‖ ^ 2 * ellTwoHead t * (Real.log t + 1) + 2 * vTailConst t

/-- The tail constants of the mode sums without their exponential factors. -/
def cQ₁ : ℝ := 4 / (Real.pi / 16) ^ 2
def cQ₂ : ℝ := 64 / (Real.pi / 8) ^ 3

theorem cQ₁_pos : 0 < cQ₁ := by unfold cQ₁; positivity
theorem cQ₂_pos : 0 < cQ₂ := by unfold cQ₂; positivity

theorem growth_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ growth t := by
  unfold growth; positivity

/-! ## Exponential cancellations -/

theorem exp_pi_mul_ellTwoHead_le {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (Real.pi * t) * ellTwoHead t ≤
      420 ^ 2 * t ^ (1 / 3 : ℝ) * (1 + Real.log (t + 1)) ^ 3 := by
  unfold ellTwoHead
  have ht0 : 0 < t := by linarith
  have hE : Real.exp (Real.pi * t) * Real.exp (-(Real.pi * t)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpow : t ^ (-(2 / 3 : ℝ)) * t = t ^ (1 / 3 : ℝ) := by
    calc t ^ (-(2 / 3 : ℝ)) * t = t ^ (-(2 / 3 : ℝ)) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = t ^ (-(2 / 3 : ℝ) + 1) := (Real.rpow_add ht0 _ _).symm
      _ = t ^ (1 / 3 : ℝ) := by norm_num
  have hπ : (1 : ℝ) / Real.pi ≤ 1 := by
    rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
  have hlog : 0 ≤ 1 + Real.log (t + 1) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ t + 1 by linarith); linarith
  calc Real.exp (Real.pi * t) * (420 ^ 2 * Real.exp (-(Real.pi * t)) * t ^ (-(2 / 3 : ℝ)) *
        (t / Real.pi) * (1 + Real.log (t + 1)) ^ 3)
      = (Real.exp (Real.pi * t) * Real.exp (-(Real.pi * t))) * 420 ^ 2 *
        ((t ^ (-(2 / 3 : ℝ)) * t) * (1 / Real.pi)) * (1 + Real.log (t + 1)) ^ 3 := by ring
    _ = 420 ^ 2 * (t ^ (1 / 3 : ℝ) * (1 / Real.pi)) * (1 + Real.log (t + 1)) ^ 3 := by
        rw [hE, hpow]; ring
    _ ≤ 420 ^ 2 * (t ^ (1 / 3 : ℝ) * 1) * (1 + Real.log (t + 1)) ^ 3 := by
        gcongr
    _ = _ := by ring

theorem exp_pi_mul_ellOneHead_sq_le {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (Real.pi * t) * ellOneHead t ^ 2 ≤
      420 ^ 2 * t ^ (4 / 3 : ℝ) * (1 + Real.log (t + 1)) ^ 2 := by
  unfold ellOneHead
  have ht0 : 0 < t := by linarith
  have hE : Real.exp (Real.pi * t) * Real.exp (-(Real.pi * t) / 2) ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf; simp
  have hpow : (t ^ (-(1 / 3 : ℝ))) ^ 2 * t ^ 2 = t ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le, ← Real.rpow_natCast t 2, ← Real.rpow_add ht0]
    norm_num
  have hπ : (1 : ℝ) / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  have hlog : 0 ≤ 1 + Real.log (t + 1) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ t + 1 by linarith); linarith
  calc Real.exp (Real.pi * t) * (420 * Real.exp (-(Real.pi * t) / 2) * t ^ (-(1 / 3 : ℝ)) *
        (t / Real.pi) * (1 + Real.log (t + 1))) ^ 2
      = (Real.exp (Real.pi * t) * Real.exp (-(Real.pi * t) / 2) ^ 2) * 420 ^ 2 *
        (((t ^ (-(1 / 3 : ℝ))) ^ 2 * t ^ 2) * (1 / Real.pi ^ 2)) * (1 + Real.log (t + 1)) ^ 2 := by
        ring
    _ = 420 ^ 2 * (t ^ (4 / 3 : ℝ) * (1 / Real.pi ^ 2)) * (1 + Real.log (t + 1)) ^ 2 := by
        rw [hE, hpow]; ring
    _ ≤ 420 ^ 2 * (t ^ (4 / 3 : ℝ) * 1) * (1 + Real.log (t + 1)) ^ 2 := by gcongr
    _ = _ := by ring

theorem exp_pi_mul_ellTwoTail_le {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (Real.pi * t) * ellTwoTail t ≤ cQ₂ * Real.exp 1 ^ 2 := by
  unfold ellTwoTail cQ₂
  have h : Real.exp (Real.pi * t) * Real.exp (-(7 * t / 2)) ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff]
    nlinarith [Real.pi_lt_d2]
  have h0 : 0 ≤ 64 / (Real.pi / 8) ^ 3 * Real.exp 1 ^ 2 := by positivity
  calc Real.exp (Real.pi * t) * (64 / (Real.pi / 8) ^ 3 * Real.exp 1 ^ 2 * Real.exp (-(7 * t / 2)))
      = (64 / (Real.pi / 8) ^ 3 * Real.exp 1 ^ 2) *
        (Real.exp (Real.pi * t) * Real.exp (-(7 * t / 2))) := by ring
    _ ≤ (64 / (Real.pi / 8) ^ 3 * Real.exp 1 ^ 2) * 1 := by gcongr
    _ = _ := by ring

theorem exp_pi_mul_ellOneTail_sq_le {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (Real.pi * t) * ellOneTail t ^ 2 ≤ cQ₁ ^ 2 * Real.exp 1 ^ 2 := by
  unfold ellOneTail cQ₁
  have h : Real.exp (Real.pi * t) * Real.exp (-(7 * t / 4)) ^ 2 ≤ 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_one_iff]
    push_cast
    nlinarith [Real.pi_lt_d2]
  have h0 : 0 ≤ (4 / (Real.pi / 16) ^ 2) ^ 2 * Real.exp 1 ^ 2 := by positivity
  calc Real.exp (Real.pi * t) * (4 / (Real.pi / 16) ^ 2 * Real.exp 1 * Real.exp (-(7 * t / 4))) ^ 2
      = ((4 / (Real.pi / 16) ^ 2) ^ 2 * Real.exp 1 ^ 2) *
        (Real.exp (Real.pi * t) * Real.exp (-(7 * t / 4)) ^ 2) := by ring
    _ ≤ ((4 / (Real.pi / 16) ^ 2) ^ 2 * Real.exp 1 ^ 2) * 1 := by gcongr
    _ = _ := by ring

/-! ## Logarithm comparisons for `t ≥ 3` -/

theorem one_le_log_of_three_le {t : ℝ} (ht : 3 ≤ t) : 1 ≤ Real.log t := by
  have : Real.exp 1 ≤ t := by linarith [Real.exp_one_lt_d9]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log t := Real.log_le_log (Real.exp_pos 1) this

theorem one_add_log_succ_le {t : ℝ} (ht : 3 ≤ t) : 1 + Real.log (t + 1) ≤ 3 * Real.log t := by
  have h1 := one_le_log_of_three_le ht
  have h2 : Real.log (t + 1) ≤ Real.log (2 * t) := Real.log_le_log (by linarith) (by linarith)
  have h3 : Real.log (2 * t) = Real.log 2 + Real.log t := Real.log_mul (by norm_num) (by linarith)
  have h4 := Real.log_two_lt_d9
  linarith

theorem log_two_mul_le {t : ℝ} (ht : 3 ≤ t) : Real.log (2 * t) ≤ 2 * Real.log t := by
  have h1 := one_le_log_of_three_le ht
  have h3 : Real.log (2 * t) = Real.log 2 + Real.log t := Real.log_mul (by norm_num) (by linarith)
  have h4 := Real.log_two_lt_d9
  linarith

theorem log_add_one_le {t : ℝ} (ht : 3 ≤ t) : Real.log t + 1 ≤ 2 * Real.log t := by
  have := one_le_log_of_three_le ht; linarith

theorem rpow_third_le_growthPow {t : ℝ} (ht : 1 ≤ t) : t ^ (1 / 3 : ℝ) ≤ t ^ (5 / 3 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le ht (by norm_num)

theorem one_le_growthPow {t : ℝ} (ht : 1 ≤ t) : 1 ≤ t ^ (5 / 3 : ℝ) := by
  have := Real.rpow_le_rpow_of_exponent_le ht (show (0 : ℝ) ≤ 5 / 3 by norm_num)
  rwa [Real.rpow_zero] at this

theorem one_le_rpow_third {t : ℝ} (ht : 1 ≤ t) : 1 ≤ t ^ (1 / 3 : ℝ) := by
  have := Real.rpow_le_rpow_of_exponent_le ht (show (0 : ℝ) ≤ 1 / 3 by norm_num)
  rwa [Real.rpow_zero] at this

theorem one_le_rpow_four_third {t : ℝ} (ht : 1 ≤ t) : 1 ≤ t ^ (4 / 3 : ℝ) := by
  have := Real.rpow_le_rpow_of_exponent_le ht (show (0 : ℝ) ≤ 4 / 3 by norm_num)
  rwa [Real.rpow_zero] at this

/-! ## The zeta lower bound in the form used here -/

theorem norm_zetaLine_ge_of_lower_bound {c t₀ : ℝ}
    (hz : ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 5 / 4 → t₀ ≤ |t| →
      c / (Real.log |t|) ^ 11 ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖)
    {t : ℝ} (ht : 0 < t) (ht₀ : t₀ ≤ 2 * t) :
    c / (Real.log (2 * t)) ^ 11 ≤ ‖riemannZeta (1 + 2 * ((t : ℂ) * I))‖ := by
  have h := hz 1 (2 * t) le_rfl (by norm_num) (by rw [abs_of_pos (by linarith)]; exact ht₀)
  rw [abs_of_pos (by linarith)] at h
  have e : ((1 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I = 1 + 2 * ((t : ℂ) * I) := by push_cast; ring
  rw [e] at h
  exact h

/-! ## The two reduced quantities -/

/-- `e^{πt} U₁ ≤ C₁ t^{5/3} (log t)⁴` for `t ≥ 3`. -/
theorem exp_pi_mul_uOne_le {t : ℝ} (ht3 : 3 ≤ t) :
    Real.exp (Real.pi * t) * (256 * ellTwoHead t * (Real.log t + 1) + 7680 * ellTwoTail t) ≤
      (256 * 420 ^ 2 * 54 + 7680 * cQ₂ * Real.exp 1 ^ 2) * t ^ (5 / 3 : ℝ) * Real.log t ^ 4 := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have ht2 : 2 ≤ t := by linarith
  have hℓ1 := one_le_log_of_three_le ht3
  have h1 := one_add_log_succ_le ht3
  have h2 := log_add_one_le ht3
  have h3 := rpow_third_le_growthPow ht1
  have h4 := one_le_growthPow ht1
  have hgp : 0 ≤ t ^ (5 / 3 : ℝ) := by positivity
  have hlog1 : 0 ≤ 1 + Real.log (t + 1) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ t + 1 by linarith); linarith
  have hlogt1 : 0 ≤ Real.log t + 1 := by linarith
  have hcube : (1 + Real.log (t + 1)) ^ 3 ≤ 27 * Real.log t ^ 3 := by
    have := pow_le_pow_left₀ hlog1 h1 3; linarith [this]
  have hP2 := exp_pi_mul_ellTwoHead_le ht1
  have hQ2 := exp_pi_mul_ellTwoTail_le ht0.le
  have hP2n := ellTwoHead_nonneg ht2
  have hQ2n := ellTwoTail_nonneg t
  have hc2 := cQ₂_pos
  have hl4 : 1 ≤ Real.log t ^ 4 := one_le_pow₀ hℓ1
  have hA : Real.exp (Real.pi * t) * (256 * ellTwoHead t * (Real.log t + 1)) ≤
      256 * 420 ^ 2 * 54 * t ^ (5 / 3 : ℝ) * Real.log t ^ 4 := by
    calc Real.exp (Real.pi * t) * (256 * ellTwoHead t * (Real.log t + 1))
        = 256 * (Real.exp (Real.pi * t) * ellTwoHead t) * (Real.log t + 1) := by ring
      _ ≤ 256 * (420 ^ 2 * t ^ (1 / 3 : ℝ) * (1 + Real.log (t + 1)) ^ 3) * (2 * Real.log t) := by
          gcongr
      _ ≤ 256 * (420 ^ 2 * t ^ (5 / 3 : ℝ) * (27 * Real.log t ^ 3)) * (2 * Real.log t) := by
          gcongr
      _ = 256 * 420 ^ 2 * 54 * t ^ (5 / 3 : ℝ) * Real.log t ^ 4 := by ring
  have hB : Real.exp (Real.pi * t) * (7680 * ellTwoTail t) ≤
      7680 * cQ₂ * Real.exp 1 ^ 2 * t ^ (5 / 3 : ℝ) * Real.log t ^ 4 := by
    have hone : 1 ≤ t ^ (5 / 3 : ℝ) * Real.log t ^ 4 := one_le_mul_of_one_le_of_one_le h4 hl4
    calc Real.exp (Real.pi * t) * (7680 * ellTwoTail t)
        = 7680 * (Real.exp (Real.pi * t) * ellTwoTail t) := by ring
      _ ≤ 7680 * (cQ₂ * Real.exp 1 ^ 2) := by gcongr
      _ ≤ 7680 * (cQ₂ * Real.exp 1 ^ 2) * (t ^ (5 / 3 : ℝ) * Real.log t ^ 4) :=
          le_mul_of_one_le_right (by positivity) hone
      _ = _ := by ring
  calc Real.exp (Real.pi * t) * (256 * ellTwoHead t * (Real.log t + 1) + 7680 * ellTwoTail t)
      = Real.exp (Real.pi * t) * (256 * ellTwoHead t * (Real.log t + 1)) +
        Real.exp (Real.pi * t) * (7680 * ellTwoTail t) := by ring
    _ ≤ _ := add_le_add hA hB
    _ = _ := by ring

/-- `e^{πt} (2P₁² + 60Q₁²) ≤ C · t^{4/3} (log t)²` for `t ≥ 3`. -/
theorem exp_pi_mul_firstFactor_le {t : ℝ} (ht3 : 3 ≤ t) :
    Real.exp (Real.pi * t) * (2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) ≤
      (2 * 420 ^ 2 * 9 + 60 * cQ₁ ^ 2 * Real.exp 1 ^ 2) * (t ^ (4 / 3 : ℝ) * Real.log t ^ 2) := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have ht2 : 2 ≤ t := by linarith
  have hℓ1 := one_le_log_of_three_le ht3
  have h1 := one_add_log_succ_le ht3
  have hlog1 : 0 ≤ 1 + Real.log (t + 1) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ t + 1 by linarith); linarith
  have hsq : (1 + Real.log (t + 1)) ^ 2 ≤ 9 * Real.log t ^ 2 := by
    have := pow_le_pow_left₀ hlog1 h1 2; linarith [this]
  have hl2 : 1 ≤ Real.log t ^ 2 := one_le_pow₀ hℓ1
  have hP1 := exp_pi_mul_ellOneHead_sq_le ht1
  have hQ1 := exp_pi_mul_ellOneTail_sq_le ht0.le
  have hP1n := ellOneHead_nonneg ht2
  have hQ1n := ellOneTail_nonneg t
  have hc1 := cQ₁_pos
  have h43 : 0 ≤ t ^ (4 / 3 : ℝ) := by positivity
  have hone : 1 ≤ t ^ (4 / 3 : ℝ) * Real.log t ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_rpow_four_third ht1) hl2
  have hA : Real.exp (Real.pi * t) * (2 * ellOneHead t ^ 2) ≤
      2 * 420 ^ 2 * 9 * (t ^ (4 / 3 : ℝ) * Real.log t ^ 2) := by
    calc Real.exp (Real.pi * t) * (2 * ellOneHead t ^ 2)
        = 2 * (Real.exp (Real.pi * t) * ellOneHead t ^ 2) := by ring
      _ ≤ 2 * (420 ^ 2 * t ^ (4 / 3 : ℝ) * (1 + Real.log (t + 1)) ^ 2) := by gcongr
      _ ≤ 2 * (420 ^ 2 * t ^ (4 / 3 : ℝ) * (9 * Real.log t ^ 2)) := by gcongr
      _ = _ := by ring
  have hB : Real.exp (Real.pi * t) * (60 * ellOneTail t ^ 2) ≤
      60 * cQ₁ ^ 2 * Real.exp 1 ^ 2 * (t ^ (4 / 3 : ℝ) * Real.log t ^ 2) := by
    calc Real.exp (Real.pi * t) * (60 * ellOneTail t ^ 2)
        = 60 * (Real.exp (Real.pi * t) * ellOneTail t ^ 2) := by ring
      _ ≤ 60 * (cQ₁ ^ 2 * Real.exp 1 ^ 2) := by gcongr
      _ ≤ 60 * (cQ₁ ^ 2 * Real.exp 1 ^ 2) * (t ^ (4 / 3 : ℝ) * Real.log t ^ 2) :=
          le_mul_of_one_le_right (by positivity) hone
      _ = _ := by ring
  calc Real.exp (Real.pi * t) * (2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2)
      = Real.exp (Real.pi * t) * (2 * ellOneHead t ^ 2) +
        Real.exp (Real.pi * t) * (60 * ellOneTail t ^ 2) := by ring
    _ ≤ _ := add_le_add hA hB
    _ = _ := by ring

/-- `e^{πt} (P₂ + 60Q₂) ≤ C · t^{1/3} (log t)³` for `t ≥ 3`. -/
theorem exp_pi_mul_secondFactor_le {t : ℝ} (ht3 : 3 ≤ t) :
    Real.exp (Real.pi * t) * (ellTwoHead t + 60 * ellTwoTail t) ≤
      (420 ^ 2 * 27 + 60 * cQ₂ * Real.exp 1 ^ 2) * (t ^ (1 / 3 : ℝ) * Real.log t ^ 3) := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have ht2 : 2 ≤ t := by linarith
  have hℓ1 := one_le_log_of_three_le ht3
  have h1 := one_add_log_succ_le ht3
  have hlog1 : 0 ≤ 1 + Real.log (t + 1) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ t + 1 by linarith); linarith
  have hcube : (1 + Real.log (t + 1)) ^ 3 ≤ 27 * Real.log t ^ 3 := by
    have := pow_le_pow_left₀ hlog1 h1 3; linarith [this]
  have hl3 : 1 ≤ Real.log t ^ 3 := one_le_pow₀ hℓ1
  have hP2 := exp_pi_mul_ellTwoHead_le ht1
  have hQ2 := exp_pi_mul_ellTwoTail_le ht0.le
  have hP2n := ellTwoHead_nonneg ht2
  have hQ2n := ellTwoTail_nonneg t
  have hc2 := cQ₂_pos
  have h13 : 0 ≤ t ^ (1 / 3 : ℝ) := by positivity
  have hone : 1 ≤ t ^ (1 / 3 : ℝ) * Real.log t ^ 3 :=
    one_le_mul_of_one_le_of_one_le (one_le_rpow_third ht1) hl3
  have hA : Real.exp (Real.pi * t) * ellTwoHead t ≤
      420 ^ 2 * 27 * (t ^ (1 / 3 : ℝ) * Real.log t ^ 3) := by
    calc Real.exp (Real.pi * t) * ellTwoHead t
        ≤ 420 ^ 2 * t ^ (1 / 3 : ℝ) * (1 + Real.log (t + 1)) ^ 3 := hP2
      _ ≤ 420 ^ 2 * t ^ (1 / 3 : ℝ) * (27 * Real.log t ^ 3) := by gcongr
      _ = _ := by ring
  have hB : Real.exp (Real.pi * t) * (60 * ellTwoTail t) ≤
      60 * cQ₂ * Real.exp 1 ^ 2 * (t ^ (1 / 3 : ℝ) * Real.log t ^ 3) := by
    calc Real.exp (Real.pi * t) * (60 * ellTwoTail t)
        = 60 * (Real.exp (Real.pi * t) * ellTwoTail t) := by ring
      _ ≤ 60 * (cQ₂ * Real.exp 1 ^ 2) := by gcongr
      _ ≤ 60 * (cQ₂ * Real.exp 1 ^ 2) * (t ^ (1 / 3 : ℝ) * Real.log t ^ 3) :=
          le_mul_of_one_le_right (by positivity) hone
      _ = _ := by ring
  calc Real.exp (Real.pi * t) * (ellTwoHead t + 60 * ellTwoTail t)
      = Real.exp (Real.pi * t) * ellTwoHead t +
        Real.exp (Real.pi * t) * (60 * ellTwoTail t) := by ring
    _ ≤ _ := add_le_add hA hB
    _ = _ := by ring

/-- `e^{2πt} U₂ ≤ C₂ t^{5/3} (log t)⁵` for `t ≥ 3`. -/
theorem exp_pi_sq_mul_uTwo_le {t : ℝ} (ht3 : 3 ≤ t) :
    Real.exp (Real.pi * t) ^ 2 * (2048 * ((2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) *
      (ellTwoHead t + 60 * ellTwoTail t))) ≤
      2048 * ((2 * 420 ^ 2 * 9 + 60 * cQ₁ ^ 2 * Real.exp 1 ^ 2) *
        (420 ^ 2 * 27 + 60 * cQ₂ * Real.exp 1 ^ 2)) * t ^ (5 / 3 : ℝ) * Real.log t ^ 5 := by
  have ht0 : 0 < t := by linarith
  have ht2 : 2 ≤ t := by linarith
  have hFa := exp_pi_mul_firstFactor_le ht3
  have hFb := exp_pi_mul_secondFactor_le ht3
  have hP2n := ellTwoHead_nonneg ht2
  have hP1n := ellOneHead_nonneg ht2
  have hQ2n := ellTwoTail_nonneg t
  have hQ1n := ellOneTail_nonneg t
  have hprodpow : t ^ (4 / 3 : ℝ) * t ^ (1 / 3 : ℝ) = t ^ (5 / 3 : ℝ) := by
    rw [← Real.rpow_add ht0]; norm_num
  have hFan : 0 ≤ Real.exp (Real.pi * t) * (2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) := by
    positivity
  have hFbn : 0 ≤ Real.exp (Real.pi * t) * (ellTwoHead t + 60 * ellTwoTail t) := by positivity
  calc Real.exp (Real.pi * t) ^ 2 * (2048 * ((2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) *
        (ellTwoHead t + 60 * ellTwoTail t)))
      = 2048 * ((Real.exp (Real.pi * t) * (2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2)) *
        (Real.exp (Real.pi * t) * (ellTwoHead t + 60 * ellTwoTail t))) := by ring
    _ ≤ 2048 * (((2 * 420 ^ 2 * 9 + 60 * cQ₁ ^ 2 * Real.exp 1 ^ 2) *
        (t ^ (4 / 3 : ℝ) * Real.log t ^ 2)) *
        ((420 ^ 2 * 27 + 60 * cQ₂ * Real.exp 1 ^ 2) * (t ^ (1 / 3 : ℝ) * Real.log t ^ 3))) := by
        gcongr
    _ = 2048 * ((2 * 420 ^ 2 * 9 + 60 * cQ₁ ^ 2 * Real.exp 1 ^ 2) *
        (420 ^ 2 * 27 + 60 * cQ₂ * Real.exp 1 ^ 2)) *
        (t ^ (4 / 3 : ℝ) * t ^ (1 / 3 : ℝ)) * Real.log t ^ 5 := by ring
    _ = _ := by rw [hprodpow]

/-- **Growth of the mean-square ratio.**  There are `B` and `T` such that for `t ≥ T`,
`Vb(t) ≤ ‖Λ(1+2it)‖⁴ (128 H + B t^{5/3} (log t)^{50})`. -/
theorem exists_vBound_le_growth :
    ∃ B T : ℝ, 0 ≤ B ∧ 3 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      vBound t ≤ ‖eisLineLambda t‖ ^ 4 * (128 * sourceHeight + B * growth t) := by
  obtain ⟨c, t₀, hc, -, hz⟩ := exists_lower_bound_riemannZeta_near_one_line
  have hc1 := cQ₁_pos
  have hc2 := cQ₂_pos
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 256 * 420 ^ 2 * 54 + 7680 * cQ₂ * Real.exp 1 ^ 2 := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = 2048 * ((2 * 420 ^ 2 * 9 + 60 * cQ₁ ^ 2 * Real.exp 1 ^ 2) *
    (420 ^ 2 * 27 + 60 * cQ₂ * Real.exp 1 ^ 2)) := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  refine ⟨C₁ * 2 ^ 22 / c ^ 2 + C₂ * 2 ^ 44 / c ^ 4, max t₀ 3, by positivity, le_max_right _ _,
    fun t ht => ?_⟩
  have ht3 : 3 ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : 0 < t := by linarith
  have htt₀ : t₀ ≤ 2 * t := by linarith [le_trans (le_max_left _ _) ht]
  have hℓ1 : 1 ≤ Real.log t := one_le_log_of_three_le ht3
  have hlog2t : 0 < Real.log (2 * t) := by
    have : Real.log 2 ≤ Real.log (2 * t) := Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  have hgr : 0 ≤ growth t := growth_nonneg ht0.le
  -- the zeta and Lambda lower bounds, with `Z` and `L` as opaque names
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ‖riemannZeta (1 + 2 * ((t : ℂ) * I))‖ := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ‖eisLineLambda t‖ ^ 2 := ⟨_, rfl⟩
  have hZlb : c / (Real.log (2 * t)) ^ 11 ≤ Z := by
    rw [hZ]; exact norm_zetaLine_ge_of_lower_bound hz ht0 htt₀
  have hZpos : 0 < Z := lt_of_lt_of_le (by positivity) hZlb
  have hLlb : Real.exp (-(Real.pi * t)) * Z ^ 2 ≤ L := by
    rw [hZ, hL]; exact normSq_eisLineLambda_ge ht0.le
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hLlb
  have hZsq : c ^ 2 / (Real.log (2 * t)) ^ 22 ≤ Z ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hZlb 2
    rwa [div_pow, ← pow_mul] at this
  have hZ4 : c ^ 4 / (Real.log (2 * t)) ^ 44 ≤ Z ^ 4 := by
    have := pow_le_pow_left₀ (by positivity) hZsq 2
    rw [div_pow, ← pow_mul, ← pow_mul, ← pow_mul] at this
    exact this
  have hlog22 : (Real.log (2 * t)) ^ 22 ≤ 2 ^ 22 * Real.log t ^ 22 := by
    have := pow_le_pow_left₀ hlog2t.le (log_two_mul_le ht3) 22
    rwa [mul_pow] at this
  have hlog44 : (Real.log (2 * t)) ^ 44 ≤ 2 ^ 44 * Real.log t ^ 44 := by
    have := pow_le_pow_left₀ hlog2t.le (log_two_mul_le ht3) 44
    rwa [mul_pow] at this
  have hgp : 0 ≤ t ^ (5 / 3 : ℝ) := by positivity
  have hEinv : Real.exp (-(Real.pi * t)) * Real.exp (Real.pi * t) = 1 := by
    rw [← Real.exp_add]; simp
  -- the reduced quantities
  obtain ⟨U₁, hU₁⟩ : ∃ U₁ : ℝ,
    U₁ = 256 * ellTwoHead t * (Real.log t + 1) + 7680 * ellTwoTail t := ⟨_, rfl⟩
  obtain ⟨U₂, hU₂⟩ : ∃ U₂ : ℝ, U₂ = 2048 * ((2 * ellOneHead t ^ 2 + 60 * ellOneTail t ^ 2) *
    (ellTwoHead t + 60 * ellTwoTail t)) := ⟨_, rfl⟩
  have hvB : vBound t = 128 * L ^ 2 * sourceHeight + L * U₁ + U₂ := by
    unfold vBound vTailConst
    rw [hL, hU₁, hU₂]; ring
  have hgrowth1 : Real.exp (Real.pi * t) * U₁ ≤ C₁ * t ^ (5 / 3 : ℝ) * Real.log t ^ 4 := by
    rw [hU₁, hC₁]; exact exp_pi_mul_uOne_le ht3
  have hgrowth2 : Real.exp (Real.pi * t) ^ 2 * U₂ ≤ C₂ * t ^ (5 / 3 : ℝ) * Real.log t ^ 5 := by
    rw [hU₂, hC₂]; exact exp_pi_sq_mul_uTwo_le ht3
  -- `U₁ ≤ L · (B₁ growth)`
  have hT1 : U₁ ≤ L * (C₁ * 2 ^ 22 / c ^ 2 * growth t) := by
    have h3 : C₁ * t ^ (5 / 3 : ℝ) * Real.log t ^ 4 ≤
        c ^ 2 / (Real.log (2 * t)) ^ 22 * (C₁ * 2 ^ 22 / c ^ 2 * growth t) := by
      unfold growth
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have e : c ^ 2 * (C₁ * 2 ^ 22 / c ^ 2 * (t ^ (5 / 3 : ℝ) * Real.log t ^ 50)) =
          C₁ * 2 ^ 22 * (t ^ (5 / 3 : ℝ) * Real.log t ^ 50) := by
        field_simp
      rw [e]
      have h26 : Real.log t ^ 26 ≤ Real.log t ^ 50 := pow_le_pow_right₀ hℓ1 (by norm_num)
      calc C₁ * t ^ (5 / 3 : ℝ) * Real.log t ^ 4 * Real.log (2 * t) ^ 22
          ≤ C₁ * t ^ (5 / 3 : ℝ) * Real.log t ^ 4 * (2 ^ 22 * Real.log t ^ 22) := by gcongr
        _ = C₁ * 2 ^ 22 * (t ^ (5 / 3 : ℝ) * Real.log t ^ 26) := by ring
        _ ≤ C₁ * 2 ^ 22 * (t ^ (5 / 3 : ℝ) * Real.log t ^ 50) := by gcongr
    calc U₁ = Real.exp (-(Real.pi * t)) * (Real.exp (Real.pi * t) * U₁) := by
          rw [← mul_assoc, hEinv, one_mul]
      _ ≤ Real.exp (-(Real.pi * t)) * (C₁ * t ^ (5 / 3 : ℝ) * Real.log t ^ 4) := by gcongr
      _ ≤ Real.exp (-(Real.pi * t)) *
          (c ^ 2 / (Real.log (2 * t)) ^ 22 * (C₁ * 2 ^ 22 / c ^ 2 * growth t)) := by gcongr
      _ = (Real.exp (-(Real.pi * t)) * (c ^ 2 / (Real.log (2 * t)) ^ 22)) *
          (C₁ * 2 ^ 22 / c ^ 2 * growth t) := by ring
      _ ≤ (Real.exp (-(Real.pi * t)) * Z ^ 2) * (C₁ * 2 ^ 22 / c ^ 2 * growth t) := by
          gcongr
      _ ≤ L * (C₁ * 2 ^ 22 / c ^ 2 * growth t) := by gcongr
  -- `U₂ ≤ L² · (B₂ growth)`
  have hT2 : U₂ ≤ L ^ 2 * (C₂ * 2 ^ 44 / c ^ 4 * growth t) := by
    have h3 : C₂ * t ^ (5 / 3 : ℝ) * Real.log t ^ 5 ≤
        c ^ 4 / (Real.log (2 * t)) ^ 44 * (C₂ * 2 ^ 44 / c ^ 4 * growth t) := by
      unfold growth
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have e : c ^ 4 * (C₂ * 2 ^ 44 / c ^ 4 * (t ^ (5 / 3 : ℝ) * Real.log t ^ 50)) =
          C₂ * 2 ^ 44 * (t ^ (5 / 3 : ℝ) * Real.log t ^ 50) := by
        field_simp
      rw [e]
      have h49 : Real.log t ^ 49 ≤ Real.log t ^ 50 := pow_le_pow_right₀ hℓ1 (by norm_num)
      calc C₂ * t ^ (5 / 3 : ℝ) * Real.log t ^ 5 * Real.log (2 * t) ^ 44
          ≤ C₂ * t ^ (5 / 3 : ℝ) * Real.log t ^ 5 * (2 ^ 44 * Real.log t ^ 44) := by gcongr
        _ = C₂ * 2 ^ 44 * (t ^ (5 / 3 : ℝ) * Real.log t ^ 49) := by ring
        _ ≤ C₂ * 2 ^ 44 * (t ^ (5 / 3 : ℝ) * Real.log t ^ 50) := by gcongr
    have hEinv2 : Real.exp (-(Real.pi * t)) ^ 2 * Real.exp (Real.pi * t) ^ 2 = 1 := by
      rw [← mul_pow, hEinv, one_pow]
    have hLsq : (Real.exp (-(Real.pi * t)) * Z ^ 2) ^ 2 ≤ L ^ 2 :=
      pow_le_pow_left₀ (by positivity) hLlb 2
    calc U₂ = Real.exp (-(Real.pi * t)) ^ 2 * (Real.exp (Real.pi * t) ^ 2 * U₂) := by
          rw [← mul_assoc, hEinv2, one_mul]
      _ ≤ Real.exp (-(Real.pi * t)) ^ 2 * (C₂ * t ^ (5 / 3 : ℝ) * Real.log t ^ 5) := by gcongr
      _ ≤ Real.exp (-(Real.pi * t)) ^ 2 *
          (c ^ 4 / (Real.log (2 * t)) ^ 44 * (C₂ * 2 ^ 44 / c ^ 4 * growth t)) := by gcongr
      _ = (Real.exp (-(Real.pi * t)) ^ 2 * (c ^ 4 / (Real.log (2 * t)) ^ 44)) *
          (C₂ * 2 ^ 44 / c ^ 4 * growth t) := by ring
      _ ≤ (Real.exp (-(Real.pi * t)) ^ 2 * Z ^ 4) * (C₂ * 2 ^ 44 / c ^ 4 * growth t) := by
          gcongr
      _ = (Real.exp (-(Real.pi * t)) * Z ^ 2) ^ 2 * (C₂ * 2 ^ 44 / c ^ 4 * growth t) := by ring
      _ ≤ L ^ 2 * (C₂ * 2 ^ 44 / c ^ 4 * growth t) := by gcongr
  -- assembly
  have hL4 : ‖eisLineLambda t‖ ^ 4 = L ^ 2 := by rw [hL]; ring
  rw [hvB, hL4]
  have hLU₁ : L * U₁ ≤ L ^ 2 * (C₁ * 2 ^ 22 / c ^ 2 * growth t) := by
    calc L * U₁ ≤ L * (L * (C₁ * 2 ^ 22 / c ^ 2 * growth t)) := by gcongr
      _ = _ := by ring
  nlinarith [hLU₁, hT2]

end

end RHTower
