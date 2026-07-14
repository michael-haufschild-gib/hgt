import GaloisForLFunctions.HTGeometry.LSeriesPowerTwist
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# The canonical Euler logarithm of the Riemann zeta function

For `Re s > 1`, the canonical Euler logarithm is

`Σ_p Σ_{r≥1} p^(-r s) / r = Σ_{n≥1} (Λ(n) / log n) n^(-s)`.

This module constructs the natural-number Dirichlet coefficient sequence, proves its exact
prime-power values, identifies its `LSeries` with the prime Euler logarithm, and proves that its
exponential is `ζ(s)`.  The coefficient formulation is designed for exact all-index peeling.
-/

namespace RHTower

open Complex Filter Topology LSeries
open ArithmeticFunction
open GaloisForLFunctions

noncomputable section

/-- Coefficient `Λ(n) / log n` of the canonical Euler logarithm. -/
def eulerLogDirichletCoeff (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) / Complex.log n

@[simp]
theorem eulerLogDirichletCoeff_zero : eulerLogDirichletCoeff 0 = 0 := by
  simp [eulerLogDirichletCoeff]

@[simp]
theorem eulerLogDirichletCoeff_one : eulerLogDirichletCoeff 1 = 0 := by
  simp [eulerLogDirichletCoeff, ArithmeticFunction.vonMangoldt_apply_one]

/-- On a prime power `p^(k+1)`, the Euler-log coefficient is exactly `1/(k+1)`. -/
theorem eulerLogDirichletCoeff_prime_pow_succ (p k : ℕ) (hp : p.Prime) :
    eulerLogDirichletCoeff (p ^ (k + 1)) = 1 / (k + 1 : ℂ) := by
  rw [eulerLogDirichletCoeff,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [← Complex.natCast_log]
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogR : Real.log p ≠ 0 := ne_of_gt (Real.log_pos hpR)
  have hreal : Real.log p / Real.log (p ^ (k + 1)) = 1 / (k + 1 : ℝ) := by
    rw [Real.log_pow]
    push_cast
    field_simp
  simpa using congrArg Complex.ofReal hreal

/-- The Euler-log coefficient vanishes away from prime powers. -/
theorem eulerLogDirichletCoeff_eq_zero_of_not_primePower {n : ℕ} (hn : ¬ IsPrimePow n) :
    eulerLogDirichletCoeff n = 0 := by
  rw [eulerLogDirichletCoeff, (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn)]
  simp

/-- Every Euler-log coefficient has norm at most one. -/
theorem norm_eulerLogDirichletCoeff_le_one (n : ℕ) :
    ‖eulerLogDirichletCoeff n‖ ≤ 1 := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [eulerLogDirichletCoeff_prime_pow_succ p j hp]
    simp only [norm_div, norm_one]
    have hnorm : ‖(j : ℂ) + 1‖ = (j + 1 : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (j + 1)
    rw [hnorm]
    simpa [one_div] using
      (inv_le_one_of_one_le₀ (by norm_num : (1 : ℝ) ≤ (j + 1 : ℝ)))
  · rw [eulerLogDirichletCoeff_eq_zero_of_not_primePower hn]
    norm_num

/-- The canonical Euler logarithm of zeta, defined by its natural-number Dirichlet coefficients. -/
def canonicalEulerLogZeta (s : ℂ) : ℂ :=
  LSeries eulerLogDirichletCoeff s

/-- Absolute convergence of the canonical Euler logarithm on `Re s > 1`. -/
theorem canonicalEulerLogZeta_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable eulerLogDirichletCoeff s := by
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have h1n : Summable fun n => ‖LSeries.term (1 : ℕ → ℂ) s n‖ :=
    summable_norm_iff.mpr h1
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) h1n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div]
    simpa using mul_le_mul_of_nonneg_right (norm_eulerLogDirichletCoeff_le_one n)
      (norm_nonneg ((n : ℂ) ^ s)⁻¹)

/-- The natural-number coefficient series equals the canonical prime Euler logarithm. -/
theorem canonicalEulerLogZeta_eq_primeLog {s : ℂ} (hs : 1 < s.re) :
    canonicalEulerLogZeta s =
      ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s)) := by
  rw [canonicalEulerLogZeta, LSeries]
  have hsum : Summable (LSeries.term eulerLogDirichletCoeff s) :=
    canonicalEulerLogZeta_summable hs
  rw [tsum_eq_tsum_primes_of_support_subset_prime_powers hsum]
  · apply tsum_congr
    intro p
    have hnorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast p.prop.pos), Complex.neg_re]
      have hp1 : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
      calc
        (p : ℝ) ^ (-s.re) < (p : ℝ) ^ (0 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
        _ = 1 := Real.rpow_zero _
    have hseries := Complex.hasSum_taylorSeries_neg_log hnorm
    rw [← hseries.tsum_eq, hseries.summable.tsum_eq_zero_add]
    simp only [Nat.cast_zero, div_zero, zero_add]
    apply tsum_congr
    intro k
    rw [LSeries.term_of_ne_zero (pow_ne_zero (k + 1) p.prop.ne_zero),
      eulerLogDirichletCoeff_prime_pow_succ p k p.prop]
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
    rw [← Complex.cpow_nat_mul]
    rw [show ((k + 1 : ℕ) : ℂ) * (-s) = -(((k + 1 : ℕ) : ℂ) * s) by ring,
      Complex.cpow_neg]
    push_cast
    ring
  · intro n hn
    by_contra hpp
    apply hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn0,
        eulerLogDirichletCoeff_eq_zero_of_not_primePower hpp]
      simp

/-- The canonical Euler logarithm exponentiates to the Riemann zeta function on `Re s > 1`. -/
theorem exp_canonicalEulerLogZeta_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (canonicalEulerLogZeta s) = riemannZeta s := by
  rw [canonicalEulerLogZeta_eq_primeLog hs]
  exact riemannZeta_eulerProduct_exp_log hs

/-- The Euler-log coefficient sequence has a finite absolute-convergence abscissa. -/
theorem eulerLogDirichletCoeff_abscissa_lt_top :
    LSeries.abscissaOfAbsConv eulerLogDirichletCoeff < ⊤ := by
  exact (canonicalEulerLogZeta_summable (s := (2 : ℂ)) (by norm_num)).abscissaOfAbsConv_le.trans_lt
    (by simp)

end


end RHTower
