import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
Working proof for the DR prime-curve vacuum-regularity audit.
Only Dirichlet coefficient separation is formalized here. The Hilbert-curve
Taylor argument and finite-smoothness source models remain outstanding.
This file is a draft artifact, not an integrated RH proof module.
-/

open Filter Topology

namespace DRVacuumCoefficientAudit

example : True := by
  have := @LSeries.tendsto_cpow_mul_atTop
  have := @Complex.norm_cpow_real
  have := @Real.rpow_le_rpow
  have := @Complex.cpow_neg
  have := @Asymptotics.IsLittleO.tendsto_div_nhds_zero.{0, 0}
  trivial

theorem coefficients_zero_of_scaled_limits
    {a : ℕ → ℂ} {M : ℕ}
    (ha0 : a 0 = 0)
    (ha : LSeries.abscissaOfAbsConv a < ⊤)
    (hlim : ∀ n : ℕ, 1 ≤ n → n ≤ M →
      Tendsto (fun x : ℝ => (n : ℂ) ^ (x : ℂ) * LSeries a x)
        atTop (𝓝 0)) :
    ∀ n : ℕ, n ≤ M → a n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => exact ha0
    | succ n =>
      have hprev : ∀ m ≤ n, a m = 0 := by
        intro m hm
        exact ih m (Nat.lt_succ_of_le hm) (le_trans hm (Nat.le_of_succ_le hn))
      have hvalue := LSeries.tendsto_cpow_mul_atTop hprev ha
      have hzero := hlim (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) hn
      simp only [Nat.cast_add, Nat.cast_one] at hzero
      exact tendsto_nhds_unique hvalue hzero

theorem coefficients_zero_of_scaled_limit
    {a : ℕ → ℂ} {M : ℕ}
    (ha0 : a 0 = 0)
    (ha : LSeries.abscissaOfAbsConv a < ⊤)
    (hlim : Tendsto (fun x : ℝ => (M : ℂ) ^ (x : ℂ) * LSeries a x)
      atTop (𝓝 0)) :
    ∀ n : ℕ, n ≤ M → a n = 0 := by
  apply coefficients_zero_of_scaled_limits ha0 ha
  intro n _ hn
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖(n : ℂ) ^ (x : ℂ) * LSeries a x‖ ≤
        ‖(M : ℂ) ^ (x : ℂ) * LSeries a x‖ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [norm_mul, Complex.norm_cpow_real, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn) hx) (norm_nonneg _)
  exact squeeze_zero_norm' hbound (by simpa using hlim.norm)

theorem coefficients_zero_of_littleO
    {a : ℕ → ℂ} {M : ℕ}
    (ha0 : a 0 = 0)
    (ha : LSeries.abscissaOfAbsConv a < ⊤)
    (hsmall : (fun x : ℝ => LSeries a x) =o[atTop]
      (fun x : ℝ => (M : ℂ) ^ (-(x : ℂ)))) :
    ∀ n : ℕ, n ≤ M → a n = 0 := by
  apply coefficients_zero_of_scaled_limit ha0 ha
  have h := hsmall.tendsto_div_nhds_zero
  simpa only [Complex.cpow_neg, div_inv_eq_mul, mul_comm] using h


end DRVacuumCoefficientAudit
