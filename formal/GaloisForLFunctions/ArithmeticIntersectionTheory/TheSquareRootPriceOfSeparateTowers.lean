import GaloisForLFunctions.ArithmeticIntersectionTheory.TheLocalFormsDoNotSum
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon

/-!
# The square-root price of separate towers

Weil's prime form is a sum of local tower forms, one per prime, each bounded:
`Q_p(x) ≤ (2 log p/(√p − 1)) |x|²` (`localForm_upper`). Paying every tower separately bounds the prime
form on orders `≤ M` by the sum of the local bounds, and that sum has the size of the square root:

    Σ_{m,n} x_m x_n P(m, n) ≤ 238 √M |x|²                         (`primeForm_le_sqrt`),

since `2/(√p − 1) ≤ 7/√p` and `Σ_{n ≤ M} Λ(n)/√n ≤ 34 √M` (RHTower, Chebyshev in square-root form).
Along the pole direction the prime form grows only like `log M` per unit mass
(`primeForm_poleVector_ge`), and a Schur test with the weights `n^{−1/2}`, which uses all primes at
once, gives `2 log M + O(1)` (AES). The gap between `√M` and `log M` is the price of ignoring the
transversality of the ladders: summing the local Hodge indices in absolute value is the
square-root threshold. As a weight, `log(local bound)/log M = ½`; the joint multiplicative structure
has weight `0`.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory

/-- The local bound in closed form: `Q_p(x) ≤ (2 log p/(√p − 1)) |x|²`. -/
theorem localForm_le {p : ℕ} (hp : p.Prime) (S : Finset ℕ) (x : ℕ → ℝ) :
    localForm S x p ≤ 2 * Real.log p / (Real.sqrt p - 1) * ∑ n ∈ S, x n ^ 2 := by
  have h := localForm_upper S x hp
  have hs1 : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast hp.one_lt)
  have hsp : 0 < Real.sqrt p := by linarith
  have hq : 1 - 1 / Real.sqrt p = (Real.sqrt p - 1) / Real.sqrt p := by field_simp
  rw [hq] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  have := mul_le_mul_of_nonneg_left h hsp.le
  calc localForm S x p * (Real.sqrt p - 1)
      = Real.sqrt p * ((Real.sqrt p - 1) / Real.sqrt p * localForm S x p) := by field_simp
    _ ≤ Real.sqrt p * (2 * (1 / Real.sqrt p) * Real.log p * ∑ n ∈ S, x n ^ 2) := this
    _ = 2 * Real.log p * ∑ n ∈ S, x n ^ 2 := by field_simp

/-- `2/(√p − 1) ≤ 7/√p` for every prime. -/
theorem two_div_sqrt_sub_one_le {p : ℕ} (hp : p.Prime) :
    2 / (Real.sqrt p - 1) ≤ 7 / Real.sqrt p := by
  have h2 : Real.sqrt 2 ≤ Real.sqrt p := Real.sqrt_le_sqrt (by exact_mod_cast hp.two_le)
  have hs2 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.4 : ℝ) = Real.sqrt (1.4 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsp : 0 < Real.sqrt p := by linarith
  rw [div_le_div_iff₀ (by linarith) hsp]
  linarith

/-- **Paying the towers separately costs the square root**: on orders in `[1, M]`,
`Σ_{m,n} x_m x_n P(m,n) ≤ 238 √M |x|²`. -/
theorem primeForm_le_sqrt {S : Finset ℕ} {M : ℕ} (hS : ∀ n ∈ S, 0 < n) (hSM : ∀ n ∈ S, n ≤ M)
    (x : ℕ → ℝ) : primeForm S x ≤ 238 * Real.sqrt M * ∑ n ∈ S, x n ^ 2 := by
  set P := (∏ n ∈ S, n).primeFactors
  have hmass : 0 ≤ ∑ n ∈ S, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  -- every prime of `∏ S` is at most `M`
  have hPM : P ⊆ (Ioc 0 M).filter Nat.Prime := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    obtain ⟨n, hn, hpn⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp
      (Nat.dvd_of_mem_primeFactors hp)
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpp.pos, (Nat.le_of_dvd (hS n hn) hpn).trans (hSM n hn)⟩, hpp⟩
  rw [primeForm_eq_sum_localForm S x fun n hn => (hS n hn).ne']
  calc ∑ p ∈ P, localForm S x p
      ≤ ∑ p ∈ P, 2 * Real.log p / (Real.sqrt p - 1) * ∑ n ∈ S, x n ^ 2 :=
        sum_le_sum fun p hp => localForm_le (Nat.prime_of_mem_primeFactors hp) S x
    _ ≤ ∑ p ∈ (Ioc 0 M).filter Nat.Prime, 7 * (Λ p / Real.sqrt p) * ∑ n ∈ S, x n ^ 2 := by
        refine (sum_le_sum fun p hp => ?_).trans (sum_le_sum_of_subset_of_nonneg hPM fun p hp _ => ?_)
        · have hpp := Nat.prime_of_mem_primeFactors hp
          rw [ArithmeticFunction.vonMangoldt_apply_prime hpp]
          refine mul_le_mul_of_nonneg_right ?_ hmass
          have := two_div_sqrt_sub_one_le hpp
          have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
          calc 2 * Real.log p / (Real.sqrt p - 1) = 2 / (Real.sqrt p - 1) * Real.log p := by ring
            _ ≤ 7 / Real.sqrt p * Real.log p := mul_le_mul_of_nonneg_right this hlog
            _ = 7 * (Real.log p / Real.sqrt p) := by ring
        · exact mul_nonneg (mul_nonneg (by norm_num)
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))) hmass
    _ ≤ ∑ n ∈ Ioc 0 M, 7 * (Λ n / Real.sqrt n) * ∑ n ∈ S, x n ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n _ _ => mul_nonneg
          (mul_nonneg (by norm_num) (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.sqrt_nonneg _))) hmass
    _ = 7 * (∑ n ∈ Ioc 0 M, Λ n / Real.sqrt n) * ∑ n ∈ S, x n ^ 2 := by
        rw [← sum_mul, ← mul_sum]
    _ ≤ 7 * (34 * Real.sqrt M) * ∑ n ∈ S, x n ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (RHTower.sum_vonMangoldt_div_sqrt_le M) (by norm_num)) hmass
    _ = 238 * Real.sqrt M * ∑ n ∈ S, x n ^ 2 := by ring

end GaloisForLFunctions.ArithmeticIntersectionTheory
