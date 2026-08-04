import GaloisForLFunctions.RHTower.Sieve.ChebyshevWidth
import GaloisForLFunctions.RHTower.Sieve.ChebyshevSaving
import GaloisForLFunctions.RHTower.Sieve.MellinDecayUniform

/-!
# The decay constants at the balanced parameters

At the balanced width the coefficient of the decay bound is

    C/H²·(N+H+1)² ≤ 9C·exp(2(log N)^{1/20}),

because `N/H = exp((log N)^{1/20})` and `N + H + 1 ≤ 3N`.  Multiplying by the two abscissa powers,

    C_c ≤ 27C·N·exp(2(log N)^{1/20} - A(log N)^{1/10}),
    C_d ≤ 81C·N·exp(2(log N)^{1/20} + A(log N)^{1/10}),

so the left-edge constant already carries the contour's saving and the right-edge constant carries
only the matching growth, which the truncation height `exp((log N)^{1/10})` divides away.
-/

namespace RHTower.Sieve

open RHTower GaloisForLFunctions.HTGeometry

/-- The cutoff's support is at most three times its size. -/
theorem add_chebWidth_le {N : ℝ} (hN : 1 ≤ N) (hL : 0 ≤ Real.log N) :
    N + chebWidth N + 1 ≤ 3 * N := by
  have h := chebWidth_le hL (by linarith)
  linarith

/-- **The coefficient of the decay bound at the balanced width.** -/
theorem decay_coeff_le {N Cj : ℝ} (hN : 1 ≤ N) (hL : 0 ≤ Real.log N) (hCj : 0 ≤ Cj) :
    Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
      ≤ 9 * Cj * Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hH0 : (0 : ℝ) < chebWidth N := chebWidth_pos hN0
  have hY : N + chebWidth N + 1 ≤ 3 * N := add_chebWidth_le hN hL
  have hY0 : (0 : ℝ) ≤ N + chebWidth N + 1 := by positivity
  have hsq : (N + chebWidth N + 1) ^ (1 + 1 : ℕ) ≤ (3 * N) ^ (1 + 1 : ℕ) :=
    pow_le_pow_left₀ hY0 hY _
  have hcoef : (0 : ℝ) ≤ Cj / chebWidth N ^ (1 + 1) := by positivity
  have hstep : Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
      ≤ Cj / chebWidth N ^ (1 + 1) * (3 * N) ^ (1 + 1 : ℕ) :=
    mul_le_mul_of_nonneg_left hsq hcoef
  refine le_trans hstep (le_of_eq ?_)
  have hratio : N / chebWidth N = Real.exp ((Real.log N) ^ ((1 : ℝ) / 20)) :=
    div_chebWidth hN0
  have hexp : Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20))
      = (N / chebWidth N) ^ (1 + 1 : ℕ) := by
    rw [hratio, ← Real.exp_nat_mul]
    norm_num
  rw [hexp, div_pow]
  field_simp
  ring

/-- **The left-edge decay constant.** -/
theorem decay_left_le {N Cj : ℝ} (hN : 1 ≤ N) (hL : 0 < Real.log N) (hCj : 0 ≤ Cj) :
    Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
        * (N + chebWidth N + 1) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))
      ≤ 27 * Cj * N * (Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20))
          * Real.exp (-(zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10)))) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hcoef := decay_coeff_le hN hL.le hCj
  have hcoef0 : (0 : ℝ) ≤ Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ) := by
    have hH0 : (0 : ℝ) < chebWidth N := chebWidth_pos hN0
    positivity
  have hsav := rpow_left_le_saving (x := N) (Y := N + chebWidth N + 1) hL hN0
    (by have := chebWidth_pos hN0; linarith)
  have hY3 : N + chebWidth N + 1 ≤ 3 * N := add_chebWidth_le hN hL.le
  have hexp0 : (0 : ℝ) < Real.exp (-(zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10))) :=
    Real.exp_pos _
  have hpow0 : (0 : ℝ) ≤ (N + chebWidth N + 1) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)) :=
    Real.rpow_nonneg (by have := chebWidth_pos hN0; linarith) _
  calc Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
        * (N + chebWidth N + 1) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))
      ≤ (9 * Cj * Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20)))
          * (N + chebWidth N + 1) ^ (1 - zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)) :=
        mul_le_mul_of_nonneg_right hcoef hpow0
    _ ≤ (9 * Cj * Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20)))
          * ((N + chebWidth N + 1)
            * Real.exp (-(zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10)))) := by
        refine mul_le_mul_of_nonneg_left hsav ?_
        positivity
    _ ≤ (9 * Cj * Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20)))
          * ((3 * N) * Real.exp (-(zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hY3 hexp0.le
    _ = 27 * Cj * N * (Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20))
          * Real.exp (-(zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10)))) := by ring

/-- **The right-edge decay constant.** -/
theorem decay_right_le {N Cj : ℝ} (hN : 1 ≤ N) (hL : 1 ≤ Real.log N) (hCj : 0 ≤ Cj) :
    Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
        * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))
      ≤ 81 * Cj * N * (Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20))
          * Real.exp (zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10))) := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hA1 : zetaLowerA ≤ 1 := zetaLowerA_le_one
  have hN0 : (0 : ℝ) < N := by linarith
  have hH0 : (0 : ℝ) < chebWidth N := chebWidth_pos hN0
  have hY0 : (0 : ℝ) < N + chebWidth N + 1 := by linarith
  have hY3 : N + chebWidth N + 1 ≤ 3 * N := add_chebWidth_le hN (by linarith)
  have hcoef := decay_coeff_le hN (by linarith) hCj
  have hpow9 : (1 : ℝ) ≤ (Real.log N) ^ ((9 : ℝ) / 10) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hL (by norm_num : (0 : ℝ) ≤ 9 / 10)
    rwa [Real.one_rpow] at h
  have hw0 : (0 : ℝ) < zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10) := by positivity
  have hlogY : Real.log (N + chebWidth N + 1) ≤ Real.log 3 + Real.log N := by
    have h := Real.log_le_log hY0 hY3
    rwa [Real.log_mul (by norm_num) (ne_of_gt hN0)] at h
  have hwL : zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10) * Real.log N
      = zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10) := by
    rw [← div_rpow_nine_tenths (by linarith : (0 : ℝ) < Real.log N)]
    field_simp
  have hwlog : zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10) * Real.log (N + chebWidth N + 1)
      ≤ Real.log 3 + zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10) := by
    have hstep : zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)
        * Real.log (N + chebWidth N + 1)
        ≤ zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10) * (Real.log 3 + Real.log N) :=
      mul_le_mul_of_nonneg_left hlogY hw0.le
    have hsmall : zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10) * Real.log 3 ≤ Real.log 3 := by
      have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      have hle1 : zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      nlinarith
    nlinarith [hstep, hsmall, hwL]
  have hgrow := rpow_right_le_growth (x := N) (Y := N + chebWidth N + 1) hY0
  have hexp3 : Real.exp (zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)
        * Real.log (N + chebWidth N + 1))
      ≤ 3 * Real.exp (zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10)) := by
    refine le_trans (Real.exp_le_exp.2 hwlog) (le_of_eq ?_)
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have hpow0 : (0 : ℝ) ≤ (N + chebWidth N + 1)
      ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)) := Real.rpow_nonneg hY0.le _
  have hexppos : (0 : ℝ) < Real.exp (zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10)) := Real.exp_pos _
  calc Cj / chebWidth N ^ (1 + 1) * (N + chebWidth N + 1) ^ (1 + 1 : ℕ)
        * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10))
      ≤ (9 * Cj * Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20)))
          * (N + chebWidth N + 1) ^ (1 + zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)) :=
        mul_le_mul_of_nonneg_right hcoef hpow0
    _ ≤ (9 * Cj * Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20)))
          * ((N + chebWidth N + 1)
            * Real.exp (zetaLowerA / (Real.log N) ^ ((9 : ℝ) / 10)
                * Real.log (N + chebWidth N + 1))) := by
        refine mul_le_mul_of_nonneg_left hgrow (by positivity)
    _ ≤ (9 * Cj * Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20)))
          * ((3 * N) * (3 * Real.exp (zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul hY3 hexp3 (Real.exp_pos _).le (by linarith)
    _ = 81 * Cj * N * (Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20))
          * Real.exp (zetaLowerA * (Real.log N) ^ ((1 : ℝ) / 10))) := by ring

end RHTower.Sieve
