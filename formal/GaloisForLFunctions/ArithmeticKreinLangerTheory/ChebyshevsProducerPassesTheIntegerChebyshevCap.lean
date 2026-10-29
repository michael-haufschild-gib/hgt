import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.WherePrecisionIsLost

/-!
# Chebyshev's producer passes the integer Chebyshev cap

Integer polynomials on `[0, 1]` produce lower counts for the primes through the integrality floor
`log (1/∫₀¹ P) ≤ ψ(n + 1)` (`ArithmeticEffectivityTheory.log_inv_integral_le_psi`). When the
smallness of `∫₀¹ P` is certified by the sup norm, the constant is capped by the integer Chebyshev
constant of `[0, 1]`: `ψ(x) ≥ c x` only for `c ≤ −log t_ℤ ≤ 0.8644` (classical). This module records
that a divisibility producer is not so capped: Chebyshev's auxiliary
`A_n = (30n)! n! / ((15n)! (10n)! (6n)!)` gives `c ≥ 0.89`.

**The ledger identity** (`chebWeight_nonneg_le_one`, `log_chebRatio_eq`). With
`T(m) = log m! = Σ_{d ≤ m} Λ(d) ⌊m/d⌋`,
`T(30n) + T(n) − T(15n) − T(10n) − T(6n) = Σ_{d ≤ 30n} Λ(d) g(⌊30n/d⌋)`, where
`g(a) = a − ⌊a/2⌋ − ⌊a/3⌋ − ⌊a/5⌋ + ⌊a/30⌋` takes only the values `0` and `1` (it is `30`-periodic).
So `log A_n ≤ ψ(30n)` (`log_chebRatio_le_psi`): every prime power below `30n` is used at most once.

**The size** (`log_chebRatio_ge`). Stirling gives
`log A_n ≥ (14 log 2 + 9 log 3 + 5 log 5) n − 3 − log 30 − (3/2) log n`, and
`14 log 2 + 9 log 3 + 5 log 5 ≥ 33 log 2 + 4 > 0.89 · 30` (`chebConst_gt`).

**The count** (`psi_thirty_mul_ge`, `psi_ge_of_chebyshev`): `ψ(x) ≥ 0.89 x − O(log x)`. The constant
passes both the Nair floor `log 2` of `x(1 − x)` certificates and the integer Chebyshev cap. It is still
a lower count for the primes at linear precision; the global law needs an upper count for the odd
Liouville class at square-root precision (`riemannHypothesis_iff_oddClass_upper`).
-/

open Finset Real
open GaloisForLFunctions.ArithmeticOfSquareRootPrecision (chebyshevTransform
  chebyshevTransform_vonMangoldt vonMangoldtWeight log_factorial_sub_bounds)

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

/-- Chebyshev's weight `g(a) = a − ⌊a/2⌋ − ⌊a/3⌋ − ⌊a/5⌋ + ⌊a/30⌋`. -/
def chebWeight (a : ℕ) : ℤ := a - (a / 2 : ℕ) - (a / 3 : ℕ) - (a / 5 : ℕ) + (a / 30 : ℕ)

/-- `g` takes only the values `0` and `1`: it is `30`-periodic and is checked on one period. -/
theorem chebWeight_nonneg_le_one (a : ℕ) : 0 ≤ chebWeight a ∧ chebWeight a ≤ 1 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 30 ∧ a = 30 * q + r :=
    ⟨a / 30, a % 30, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod a 30).symm⟩
  have h2 : (30 * q + r) / 2 = 15 * q + r / 2 := by omega
  have h3 : (30 * q + r) / 3 = 10 * q + r / 3 := by omega
  have h5 : (30 * q + r) / 5 = 6 * q + r / 5 := by omega
  have h30 : (30 * q + r) / 30 = q + r / 30 := by omega
  unfold chebWeight
  rw [h2, h3, h5, h30]
  push_cast
  interval_cases r <;> omega

/-- The quotients of `30n` by `d` determine those of `15n`, `10n`, `6n` and `n`. -/
theorem div_eq_chebQuot (n d : ℕ) (k c : ℕ) (hc : 0 < c) (hk : c * k = 30) :
    k * n / d = 30 * n / d / c := by
  rw [Nat.div_div_eq_div_mul, ← hk, mul_assoc, mul_comm d c, Nat.mul_div_mul_left _ _ hc]

/-- `T(m) = Σ_{d ≤ M} Λ(d) ⌊m/d⌋` for any `M ≥ m`. -/
theorem chebyshevTransform_eq_sum_Ioc {m M : ℕ} (hmM : m ≤ M) :
    chebyshevTransform vonMangoldtWeight m =
      ∑ d ∈ Ioc 0 M, vonMangoldtWeight d * ((m / d : ℕ) : ℝ) := by
  refine sum_subset (Ioc_subset_Ioc_right hmM) fun d hd hdm => ?_
  have : m < d := by
    simp only [mem_Ioc, not_and, not_le] at hdm
    exact hdm (mem_Ioc.mp hd).1
  rw [Nat.div_eq_of_lt this, Nat.cast_zero, mul_zero]

/-- The logarithm of Chebyshev's ratio, `log A_n = T(30n) + T(n) − T(15n) − T(10n) − T(6n)`. -/
def logChebRatio (n : ℕ) : ℝ :=
  Real.log ((30 * n).factorial : ℕ) + Real.log (n.factorial : ℕ) - Real.log ((15 * n).factorial : ℕ) -
    Real.log ((10 * n).factorial : ℕ) - Real.log ((6 * n).factorial : ℕ)

/-- **The ledger identity.** `log A_n = Σ_{d ≤ 30n} Λ(d) g(⌊30n/d⌋)`. -/
theorem log_chebRatio_eq (n : ℕ) :
    logChebRatio n = ∑ d ∈ Ioc 0 (30 * n), vonMangoldtWeight d * (chebWeight (30 * n / d) : ℝ) := by
  simp only [logChebRatio, ← chebyshevTransform_vonMangoldt]
  rw [chebyshevTransform_eq_sum_Ioc le_rfl,
    chebyshevTransform_eq_sum_Ioc (show n ≤ 30 * n by omega),
    chebyshevTransform_eq_sum_Ioc (show 15 * n ≤ 30 * n by omega),
    chebyshevTransform_eq_sum_Ioc (show 10 * n ≤ 30 * n by omega),
    chebyshevTransform_eq_sum_Ioc (show 6 * n ≤ 30 * n by omega),
    ← sum_add_distrib, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun d _ => ?_
  have e1 : n / d = 30 * n / d / 30 := by
    simpa using div_eq_chebQuot n d 1 30 (by norm_num) (by norm_num)
  rw [e1, div_eq_chebQuot n d 15 2 (by norm_num) (by norm_num),
    div_eq_chebQuot n d 10 3 (by norm_num) (by norm_num),
    div_eq_chebQuot n d 6 5 (by norm_num) (by norm_num)]
  simp only [chebWeight, Int.cast_add, Int.cast_sub, Int.cast_natCast]
  ring

/-- **Each prime power is used at most once:** `log A_n ≤ ψ(30n)`. -/
theorem log_chebRatio_le_psi (n : ℕ) : logChebRatio n ≤ Chebyshev.psi (30 * n : ℕ) := by
  rw [log_chebRatio_eq, Chebyshev.psi, Nat.floor_natCast]
  refine sum_le_sum fun d _ => ?_
  have hΛ : 0 ≤ vonMangoldtWeight d := ArithmeticFunction.vonMangoldt_nonneg
  have hg : (chebWeight (30 * n / d) : ℝ) ≤ 1 := by
    exact_mod_cast (chebWeight_nonneg_le_one _).2
  exact (mul_le_mul_of_nonneg_left hg hΛ).trans_eq (mul_one _)

/-- **The size of Chebyshev's ratio.** For `n ≥ 1`,
`log A_n ≥ (14 log 2 + 9 log 3 + 5 log 5) n − 3 − log 30 − (3/2) log n`. -/
theorem log_chebRatio_ge {n : ℕ} (hn : 1 ≤ n) :
    (14 * Real.log 2 + 9 * Real.log 3 + 5 * Real.log 5) * n - 3 - Real.log 30 -
      3 / 2 * Real.log n ≤ logChebRatio n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have b30 := (log_factorial_sub_bounds (show 1 ≤ 30 * n by omega)).1
  have b1 := (log_factorial_sub_bounds hn).1
  have b15 := (log_factorial_sub_bounds (show 1 ≤ 15 * n by omega)).2
  have b10 := (log_factorial_sub_bounds (show 1 ≤ 10 * n by omega)).2
  have b6 := (log_factorial_sub_bounds (show 1 ≤ 6 * n by omega)).2
  push_cast at b30 b15 b10 b6
  -- split `log (k n) = log k + log n`
  have hl : ∀ k : ℝ, 0 < k → Real.log (k * n) = Real.log k + Real.log n := fun k hk =>
    Real.log_mul hk.ne' hn0.ne'
  rw [hl 30 (by norm_num)] at b30
  rw [hl 15 (by norm_num)] at b15
  rw [hl 10 (by norm_num)] at b10
  rw [hl 6 (by norm_num)] at b6
  have l30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have l15 : Real.log 15 = Real.log 3 + Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [l30] at b30 ⊢
  rw [l15] at b15
  rw [l10] at b10
  rw [l6] at b6
  unfold logChebRatio
  nlinarith [b30, b1, b15, b10, b6]

/-- **Chebyshev's constant.** `14 log 2 + 9 log 3 + 5 log 5 ≥ 33 log 2 + 4 > 0.89 · 30`, using
`log (3/2) ≥ 1/3` and `log (5/4) ≥ 1/5`. -/
theorem chebConst_gt : (89 / 100 : ℝ) * 30 < 14 * Real.log 2 + 9 * Real.log 3 + 5 * Real.log 5 := by
  have h3 : Real.log 2 + 1 / 3 ≤ Real.log 3 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num)] at this
    norm_num at this ⊢
    linarith
  have h5 : 2 * Real.log 2 + 1 / 5 ≤ Real.log 5 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at this
    norm_num at this ⊢
    linarith
  have h2 := Real.log_two_gt_d9
  nlinarith

/-- **Chebyshev's lower count.** For `n ≥ 1`, `ψ(30n) ≥ 0.89 · 30n − 3 − log 30 − (3/2) log n`. -/
theorem psi_thirty_mul_ge {n : ℕ} (hn : 1 ≤ n) :
    (89 / 100 : ℝ) * (30 * n) - 3 - Real.log 30 - 3 / 2 * Real.log n ≤
      Chebyshev.psi (30 * n : ℕ) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have := log_chebRatio_ge hn
  have hc := chebConst_gt
  have := log_chebRatio_le_psi n
  nlinarith

/-- **`ψ(x) ≥ 0.89 x − O(log x)`.** For `x ≥ 30`,
`ψ(x) ≥ 0.89 x − 30 − 3 − log 30 − (3/2) log x`. -/
theorem psi_ge_of_chebyshev {x : ℝ} (hx : 30 ≤ x) :
    (89 / 100 : ℝ) * x - 30 - 3 - Real.log 30 - 3 / 2 * Real.log x ≤ Chebyshev.psi x := by
  set n := ⌊x / 30⌋₊ with hndef
  have hn : 1 ≤ n := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ (by norm_num)]; linarith)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnx : (30 * n : ℝ) ≤ x := by
    have := Nat.floor_le (show 0 ≤ x / 30 by positivity)
    rw [← hndef] at this
    linarith [(le_div_iff₀ (show (0 : ℝ) < 30 by norm_num)).mp this]
  have hxn : x < 30 * n + 30 := by
    have := Nat.lt_floor_add_one (x / 30)
    rw [← hndef] at this
    have := (div_lt_iff₀ (show (0 : ℝ) < 30 by norm_num)).mp this
    linarith
  have hmono : Chebyshev.psi (30 * n : ℕ) ≤ Chebyshev.psi x :=
    Chebyshev.psi_mono (by push_cast; exact hnx)
  have hlog : Real.log n ≤ Real.log x :=
    Real.log_le_log hn0 (by linarith)
  have := psi_thirty_mul_ge hn
  nlinarith

end GaloisForLFunctions.ArithmeticKreinLangerTheory
