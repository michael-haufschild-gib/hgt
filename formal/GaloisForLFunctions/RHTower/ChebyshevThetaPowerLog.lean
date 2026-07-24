import GaloisForLFunctions.RHTower.ChebyshevPsiPowerLogPNT
import GaloisForLFunctions.RHTower.SelbergSymmetryCore

/-!
# The power-log prime number theorem for `θ`

Transferring the `ψ`-estimate to mathlib's real-argument `Chebyshev.psi`
and then to `Chebyshev.theta`: the prime-power defect `ψ − θ ≤ 2√x·log x`
is exponentially smaller than the power-log error, so

`|θ(x) − x| ≤ C·x·exp(−c·(log x)^{1/10})`

for all large `x`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction

/-- Mathlib's `ψ` at a real point is the project `ψ` at its floor. -/
theorem psi_eq_chebyshevPsi_floor (x : ℝ) :
    Chebyshev.psi x = chebyshevPsi ⌊x⌋₊ := by
  rw [chebyshevPsi_eq_psi]
  unfold Chebyshev.psi
  rw [Nat.floor_natCast]

/-- The prime-power defect is beaten by the power-log decay:
`2√x·log x ≤ x·e^{-c(log x)^{1/10}}` for large `x`. -/
theorem sqrt_log_le_power_log_decay {c : ℝ} (hc : 0 < c) :
    ∃ x₁ : ℝ, 3 ≤ x₁ ∧ ∀ x : ℝ, x₁ ≤ x →
      2 * Real.sqrt x * Real.log x
        ≤ x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
  refine ⟨Real.exp (max 28 ((4 * c) ^ ((10 : ℝ) / 9))), ?_, ?_⟩
  · calc (3 : ℝ) ≤ 28 := by norm_num
      _ ≤ max 28 ((4 * c) ^ ((10 : ℝ) / 9)) := le_max_left _ _
      _ ≤ Real.exp (max 28 ((4 * c) ^ ((10 : ℝ) / 9))) := by
        linarith [Real.add_one_le_exp
          (max 28 ((4 * c) ^ ((10 : ℝ) / 9)))]
  · intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
    have hL : max 28 ((4 * c) ^ ((10 : ℝ) / 9)) ≤ Real.log x := by
      have h1 := Real.log_le_log (Real.exp_pos _) hx
      rwa [Real.log_exp] at h1
    have hL28 : (28 : ℝ) ≤ Real.log x :=
      le_trans (le_max_left _ _) hL
    have hL0 : (0 : ℝ) < Real.log x := by linarith
    have hL4c : (4 * c) ^ ((10 : ℝ) / 9) ≤ Real.log x :=
      le_trans (le_max_right _ _) hL
    -- `c·L^{1/10} ≤ L/4`
    have h910 : 4 * c ≤ Real.log x ^ ((9 : ℝ) / 10) := by
      have h1 : ((4 * c) ^ ((10 : ℝ) / 9)) ^ ((9 : ℝ) / 10)
          ≤ Real.log x ^ ((9 : ℝ) / 10) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _)
          hL4c (by norm_num)
      rwa [← Real.rpow_mul (by positivity),
        show (10 : ℝ) / 9 * (9 / 10) = 1 from by norm_num,
        Real.rpow_one] at h1
    have hcL : c * Real.log x ^ ((1 : ℝ) / 10) ≤ Real.log x / 4 := by
      have h1 : 4 * c * Real.log x ^ ((1 : ℝ) / 10)
          ≤ Real.log x ^ ((9 : ℝ) / 10)
            * Real.log x ^ ((1 : ℝ) / 10) :=
        mul_le_mul_of_nonneg_right h910
          (Real.rpow_nonneg hL0.le _)
      rw [← Real.rpow_add hL0,
        show (9 : ℝ) / 10 + 1 / 10 = 1 from by norm_num,
        Real.rpow_one] at h1
      linarith
    -- `2L ≤ e^{L/4}`
    have hexpL4 : 2 * Real.log x ≤ Real.exp (Real.log x / 4) := by
      have h1 := Real.pow_div_factorial_le_exp (Real.log x / 4)
        (by positivity) 3
      have h2 : ((Nat.factorial 3 : ℝ)) = 6 := by norm_num [Nat.factorial]
      rw [h2] at h1
      have h3 : 2 * Real.log x ≤ (Real.log x / 4) ^ 3 / 6 := by
        have h4 : (Real.log x / 4) ^ 3 / 6
            = Real.log x ^ 3 / 384 := by ring
        rw [h4]
        have h5 : (784 : ℝ) ≤ Real.log x ^ 2 := by nlinarith [hL28]
        nlinarith [h5, hL0, hL28]
      linarith
    -- assemble in `exp`-space
    have hsqrt : Real.sqrt x = Real.exp (Real.log x / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
      congr 1
      ring
    have hx_exp : x = Real.exp (Real.log x) :=
      (Real.exp_log hx0).symm
    calc 2 * Real.sqrt x * Real.log x
        = Real.exp (Real.log x / 2) * (2 * Real.log x) := by
          rw [hsqrt]
          ring
      _ ≤ Real.exp (Real.log x / 2) * Real.exp (Real.log x / 4) :=
          mul_le_mul_of_nonneg_left hexpL4 (Real.exp_nonneg _)
      _ = Real.exp (Real.log x / 2 + Real.log x / 4) :=
          (Real.exp_add _ _).symm
      _ ≤ Real.exp (Real.log x
            - c * Real.log x ^ ((1 : ℝ) / 10)) := by
          apply Real.exp_le_exp.2
          linarith [hcL]
      _ = x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
          rw [show Real.log x - c * Real.log x ^ ((1 : ℝ) / 10)
              = Real.log x + -(c * Real.log x ^ ((1 : ℝ) / 10)) from by
            ring, Real.exp_add, ← hx_exp]

/-- **The power-log PNT for `θ`**: `|θ(x) − x| ≤ C·x·e^{-c(log x)^{1/10}}`
for all large `x`. -/
theorem exists_chebyshev_theta_power_log :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 ≤ C ∧ 3 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        |Chebyshev.theta x - x|
          ≤ C * x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨c, C, x₀, hc, hC, hx₀3, hψ⟩ := exists_chebyshevPsi_power_log
  obtain ⟨x₁, hx₁3, hx₁⟩ := sqrt_log_le_power_log_decay hc
  refine ⟨c, C + 1, max x₀ x₁, hc, by linarith, ?_, ?_⟩
  · exact le_trans hx₀3 (le_max_left _ _)
  · intro x hx
    have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
    have hxx₁ : x₁ ≤ x := le_trans (le_max_right _ _) hx
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hx0 : (0 : ℝ) < x := by linarith
    have hψx := hψ x hxx₀
    rw [← psi_eq_chebyshevPsi_floor] at hψx
    have hθψ : Chebyshev.psi x - Chebyshev.theta x
        ≤ 2 * Real.sqrt x * Real.log x :=
      Chebyshev.psi_sub_theta_le hx1
    have hθψ0 : Chebyshev.theta x ≤ Chebyshev.psi x :=
      Chebyshev.theta_le_psi _
    have hdecay := hx₁ x hxx₁
    have hψ' := abs_le.1 hψx
    rw [abs_le]
    constructor
    · have h1 : -(C * x * Real.exp
          (-(c * Real.log x ^ ((1 : ℝ) / 10))))
          ≤ Chebyshev.psi x - x := hψ'.1
      have h2 : Chebyshev.theta x - x
          ≥ Chebyshev.psi x - x - 2 * Real.sqrt x * Real.log x := by
        linarith
      nlinarith [Real.exp_nonneg
        (-(c * Real.log x ^ ((1 : ℝ) / 10))), hx0.le]
    · have h1 := hψ'.2
      nlinarith [Real.exp_nonneg
        (-(c * Real.log x ^ ((1 : ℝ) / 10))), hx0.le]

end RHTower
