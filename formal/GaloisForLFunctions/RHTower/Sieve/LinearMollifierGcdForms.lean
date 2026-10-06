import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogAsymptotic
import GaloisForLFunctions.RHTower.Sieve.SelbergLogPowerGeneralAsymptotic

/-!
# The two gcd forms of the linear mollifier

For the linear mollifier `b(h) = μ(h) log(N/h)/log N` (`1 ≤ h ≤ N`) the diagonal of the mollified
second moment of `ζ` is governed by the two gcd forms

`S₀(N) = Σ_{h,k ≤ N} b(h)b(k)(h,k)/(hk)`,
`S₁(N) = Σ_{h,k ≤ N} b(h)b(k)(h,k)/(hk) · log((h,k)²/(hk))`.

**Theorem.** `S₀(N) log N → 1` (`tendsto_linearMollifierForm₀_mul_log`) and `S₁(N) → 1`
(`tendsto_linearMollifierForm₁`).  With `N = T^θ` the diagonal
`Σ b(h)b(k)(h,k)/(hk)(log(T(h,k)²/(hk)) + O(1))` is therefore `1/θ + 1 + o(1)`: the constant of
Balasubramanian, Conrey and Heath-Brown.

**Proof.**  With `L = log N`, `log h = L − log(N/h)`, so
`L² S₁ = 2 G(1,1) + Q(2,1) + Q(1,2) − 2L Q(1,1)` and `L² S₀ = Q(1,1)`, where
`Q(i,j) = Σ μμ(h,k)/(hk) log^i(N/h) log^j(N/k) ∼ ij/(i+j−1) L^{i+j−1}` and the gcd-logarithmic
`G(1,1) ∼ ½ L²` (Graham's Selberg diagonals, `tendsto_selbergOriginalLogMonomial_div_log_pow`,
`tendsto_selbergOriginalGcdLogMonomial_div_log_pow`).  Hence `S₁ → 1 + 1 + 1 − 2 = 1`.
-/

open ArithmeticFunction Finset Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- The linear mollifier coefficient `μ(h) log(N/h)/log N`. -/
def linearMollifierCoeff (N h : ℕ) : ℝ :=
  ((μ h : ℤ) : ℝ) * Real.log ((N : ℝ) / (h : ℝ)) / Real.log N

/-- `S₀(N) = Σ b(h)b(k)(h,k)/(hk)`. -/
def linearMollifierForm₀ (N : ℕ) : ℝ :=
  ∑ h ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
    linearMollifierCoeff N h * linearMollifierCoeff N k * ((Nat.gcd h k : ℕ) : ℝ) /
      ((h : ℝ) * (k : ℝ))

/-- `S₁(N) = Σ b(h)b(k)(h,k)/(hk) log((h,k)²/(hk))`. -/
def linearMollifierForm₁ (N : ℕ) : ℝ :=
  ∑ h ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
    linearMollifierCoeff N h * linearMollifierCoeff N k * ((Nat.gcd h k : ℕ) : ℝ) /
      ((h : ℝ) * (k : ℝ)) *
        Real.log (((Nat.gcd h k : ℕ) : ℝ) ^ 2 / ((h : ℝ) * (k : ℝ)))

theorem selbergOriginalLogMonomial_eq_sum (i j N : ℕ) :
    selbergOriginalLogMonomial i j N =
      ∑ h ∈ Icc 1 N, ∑ k ∈ Icc 1 N, selbergOriginalCoeff h k *
        (Real.log ((N : ℝ) / (h : ℝ)) ^ i * Real.log ((N : ℝ) / (k : ℝ)) ^ j) := by
  rw [selbergOriginalLogMonomial, Finset.sum_product]

theorem linearMollifier_term_eq {N h k : ℕ} :
    linearMollifierCoeff N h * linearMollifierCoeff N k * ((Nat.gcd h k : ℕ) : ℝ) /
      ((h : ℝ) * (k : ℝ)) =
    selbergOriginalCoeff h k * (Real.log ((N : ℝ) / (h : ℝ)) * Real.log ((N : ℝ) / (k : ℝ))) /
      Real.log N ^ 2 := by
  unfold linearMollifierCoeff selbergOriginalCoeff
  rcases eq_or_ne (Real.log N) 0 with hL | hL
  · simp [hL]
  rcases eq_or_ne (h : ℝ) 0 with hh | hh
  · simp [hh]
  rcases eq_or_ne (k : ℝ) 0 with hk | hk
  · simp [hk]
  field_simp

/-- `L² S₀ = Q(1,1)`. -/
theorem linearMollifierForm₀_mul_log_sq (N : ℕ) :
    linearMollifierForm₀ N * Real.log N ^ 2 = selbergOriginalLogMonomial 1 1 N := by
  rcases eq_or_ne (Real.log N) 0 with hL | hL
  · have hN : N ≤ 1 := by
      by_contra h
      have : 1 < (N : ℝ) := by exact_mod_cast (not_le.mp h)
      exact (Real.log_pos this).ne' hL
    interval_cases N <;> simp [selbergOriginalLogMonomial, linearMollifierForm₀]
  rw [selbergOriginalLogMonomial_eq_sum, linearMollifierForm₀, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [linearMollifier_term_eq]
  field_simp

/-- The logarithmic splitting `log((h,k)²/(hk)) = 2 log(h,k) + log(N/h) + log(N/k) − 2 log N`. -/
theorem log_gcd_sq_div_eq {N h k : ℕ} (hN : 0 < N) (hh : 0 < h) (hk : 0 < k) :
    Real.log (((Nat.gcd h k : ℕ) : ℝ) ^ 2 / ((h : ℝ) * (k : ℝ))) =
      2 * Real.log ((Nat.gcd h k : ℕ) : ℝ) + Real.log ((N : ℝ) / (h : ℝ)) +
        Real.log ((N : ℝ) / (k : ℝ)) - 2 * Real.log N := by
  have hg : (0 : ℝ) < ((Nat.gcd h k : ℕ) : ℝ) := by exact_mod_cast Nat.gcd_pos_of_pos_left k hh
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_mul hhR.ne' hkR.ne',
    Real.log_div hNR.ne' hhR.ne', Real.log_div hNR.ne' hkR.ne']
  push_cast
  ring

/-- `L² S₁ = 2 G(1,1) + Q(2,1) + Q(1,2) − 2L Q(1,1)`. -/
theorem linearMollifierForm₁_mul_log_sq {N : ℕ} (hN : 0 < N) :
    linearMollifierForm₁ N * Real.log N ^ 2 =
      2 * selbergOriginalGcdLogMonomial 1 1 N + selbergOriginalLogMonomial 2 1 N +
        selbergOriginalLogMonomial 1 2 N - 2 * Real.log N * selbergOriginalLogMonomial 1 1 N := by
  rcases eq_or_ne (Real.log N) 0 with hL | hL
  · have hN1 : N = 1 := by
      have : N ≤ 1 := by
        by_contra h
        have : 1 < (N : ℝ) := by exact_mod_cast (not_le.mp h)
        exact (Real.log_pos this).ne' hL
      omega
    subst hN1
    simp [selbergOriginalLogMonomial, selbergOriginalGcdLogMonomial, linearMollifierForm₁,
      selbergOriginalGcdLogCoeff]
  rw [selbergOriginalLogMonomial_eq_sum, selbergOriginalLogMonomial_eq_sum,
    selbergOriginalLogMonomial_eq_sum, selbergOriginalGcdLogMonomial, linearMollifierForm₁,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hh0 : 0 < h := (Finset.mem_Icc.mp hh).1
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  rw [linearMollifier_term_eq, log_gcd_sq_div_eq hN hh0 hk0, selbergOriginalGcdLogCoeff]
  field_simp

/-- **`S₀(N) log N → 1`.** -/
theorem tendsto_linearMollifierForm₀_mul_log :
    Tendsto (fun N : ℕ => linearMollifierForm₀ N * Real.log N) atTop (𝓝 1) := by
  have h := tendsto_selbergOriginalLogMonomial_div_log_pow (i := 1) (j := 1) one_pos one_pos
  norm_num at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hL : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [← linearMollifierForm₀_mul_log_sq]
  field_simp

/-- **`S₁(N) → 1`.** -/
theorem tendsto_linearMollifierForm₁ :
    Tendsto (fun N : ℕ => linearMollifierForm₁ N) atTop (𝓝 1) := by
  have hG := tendsto_selbergOriginalGcdLogMonomial_div_log_pow (i := 1) (j := 1) one_pos one_pos
  have h21 := tendsto_selbergOriginalLogMonomial_div_log_pow (i := 2) (j := 1) two_pos one_pos
  have h12 := tendsto_selbergOriginalLogMonomial_div_log_pow (i := 1) (j := 2) one_pos two_pos
  have h11 := tendsto_selbergOriginalLogMonomial_div_log_pow (i := 1) (j := 1) one_pos one_pos
  norm_num at hG h21 h12 h11
  have hsum := (((hG.const_mul 2).add h21).add h12).sub (h11.const_mul 2)
  norm_num at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hL : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have hm := linearMollifierForm₁_mul_log_sq (N := N) (by omega)
  rw [show linearMollifierForm₁ N = (linearMollifierForm₁ N * Real.log N ^ 2) / Real.log N ^ 2 by
    field_simp, hm]
  field_simp

end

end RHTower.Sieve
