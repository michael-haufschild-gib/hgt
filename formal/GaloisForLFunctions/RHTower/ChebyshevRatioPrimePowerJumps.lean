import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The Chebyshev ratio `(ψ(x) − log x)/x` peaks at prime powers

Let `R(x) = (ψ(x) − log x)/x`. Between two consecutive prime powers `ψ` is constant, and `R`
decreases there.

**Theorem** (`exists_isPrimePow_psiLogRatio_ge`). For every `x ≥ 2` there is a prime power
`m ≤ x` with `R(x) ≤ R(m)`. Hence `sup_{x ≥ 2} R(x)` is the supremum of `R` over prime powers
(`psiLogRatio_lt_of_isPrimePow_lt`), and a bound for `R` at every prime power is a bound for all
real `x ≥ 2`.

**Proof.**
* `ψ(k) ≥ ⌊log₂ k⌋ log 2 > log k − log 2`, from the powers of `2` up to `k`
  (`psi_ge_natLog_mul_log_two`).
* On a plateau `k ≤ x ≤ 2k` with `ψ(x) = ψ(k)`, write `r = x/k ∈ [1, 2]`. Then `R(x) ≤ R(k)` is
  `(r − 1)(log k − ψ(k)) ≤ log r`. This follows from `log k − ψ(k) < log 2` and the concavity
  bound `log r ≥ (r − 1) log 2` on `[1, 2]` (`psiLogRatio_le_of_plateau`).
* Let `m` be the largest prime power `≤ x`. Then `ψ(x) = ψ(m)`. Bertrand's postulate puts a
  prime in `(m, 2m]`, so `x < 2m`.
-/

open Real

noncomputable section

namespace RHTower

/-- The ratio `R(x) = (ψ(x) − log x)/x`. -/
def psiLogRatio (x : ℝ) : ℝ := (Chebyshev.psi x - Real.log x) / x

/-- `ψ(x) ≥ ⌊log₂ ⌊x⌋⌋ log 2`: the powers of `2` up to `x`. -/
theorem psi_ge_natLog_mul_log_two (x : ℝ) :
    (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log 2 ≤ Chebyshev.psi x := by
  classical
  set N := ⌊x⌋₊
  set m := Nat.log 2 N
  rcases Nat.eq_zero_or_pos N with hN | hN
  · have hm0 : m = 0 := by simp [m, hN]
    rw [hm0, Nat.cast_zero, zero_mul]
    exact Chebyshev.psi_nonneg x
  have hsub : (Finset.Icc 1 m).image (fun j => 2 ^ j) ⊆ Finset.Ioc 0 N := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.mp hj
    exact Finset.mem_Ioc.mpr ⟨by positivity,
      (Nat.pow_le_pow_right (by norm_num) hjm).trans (Nat.pow_log_le_self 2 hN.ne')⟩
  have hinj : Set.InjOn (fun j : ℕ => 2 ^ j) ((Finset.Icc 1 m : Finset ℕ) : Set ℕ) :=
    fun i _ j _ h => Nat.pow_right_injective le_rfl h
  have hval : ∑ n ∈ (Finset.Icc 1 m).image (fun j => 2 ^ j), ArithmeticFunction.vonMangoldt n =
      (m : ℝ) * Real.log 2 := by
    rw [Finset.sum_image hinj]
    have : ∀ j ∈ Finset.Icc 1 m, ArithmeticFunction.vonMangoldt (2 ^ j) = Real.log 2 := by
      intro j hj
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by linarith [(Finset.mem_Icc.mp hj).1]),
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      norm_num
    rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp
  rw [← hval, Chebyshev.psi]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
    ArithmeticFunction.vonMangoldt_nonneg

/-- `log k − log 2 < ψ(k)` for `k ≥ 1`. -/
theorem log_sub_log_two_lt_psi {k : ℕ} (hk : 1 ≤ k) :
    Real.log k - Real.log 2 < Chebyshev.psi k := by
  have h := psi_ge_natLog_mul_log_two (k : ℝ)
  rw [Nat.floor_natCast] at h
  have hlt : (k : ℝ) < 2 ^ (Nat.log 2 k + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) k
  have hlog : Real.log k < (Nat.log 2 k + 1 : ℕ) * Real.log 2 := by
    rw [← Real.log_pow]
    exact Real.log_lt_log (by exact_mod_cast hk) (by exact_mod_cast hlt)
  push_cast at hlog
  linarith

/-- `log r ≥ (r − 1) log 2` on `[1, 2]`, by concavity of `log`. -/
theorem sub_one_mul_log_two_le_log {r : ℝ} (h1 : 1 ≤ r) (h2 : r ≤ 2) :
    (r - 1) * Real.log 2 ≤ Real.log r := by
  have h := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.mpr (one_pos : (0 : ℝ) < 1))
    (Set.mem_Ioi.mpr (two_pos : (0 : ℝ) < 2)) (show (0 : ℝ) ≤ 2 - r by linarith)
    (show (0 : ℝ) ≤ r - 1 by linarith) (by ring : (2 - r) + (r - 1) = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at h
  rwa [show (2 - r) * 1 + (r - 1) * 2 = r by ring] at h

/-- **Plateau monotonicity.** If `k ≤ x ≤ 2k` and `ψ(x) = ψ(k)`, then `R(x) ≤ R(k)`. -/
theorem psiLogRatio_le_of_plateau {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hkx : (k : ℝ) ≤ x)
    (hx2 : x ≤ 2 * k) (hψ : Chebyshev.psi x = Chebyshev.psi k) :
    psiLogRatio x ≤ psiLogRatio k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hx0 : 0 < x := lt_of_lt_of_le hk0 hkx
  set r := x / k with hr
  have hr1 : 1 ≤ r := (one_le_div hk0).mpr hkx
  have hr2 : r ≤ 2 := (div_le_iff₀ hk0).mpr (by linarith)
  have hxr : x = k * r := by rw [hr]; field_simp
  have hlogx : Real.log x = Real.log k + Real.log r := by
    rw [hxr, Real.log_mul hk0.ne' (by linarith)]
  have hc := log_sub_log_two_lt_psi hk
  have hcon := sub_one_mul_log_two_le_log hr1 hr2
  have key : (r - 1) * (Real.log k - Chebyshev.psi k) ≤ Real.log r := by
    have : (r - 1) * (Real.log k - Chebyshev.psi k) ≤ (r - 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  unfold psiLogRatio
  rw [hψ, div_le_div_iff₀ hx0 hk0, hlogx, hxr]
  nlinarith

/-- **Reduction to prime powers.** For every `x ≥ 2` there is a prime power `m ≤ x` with
`R(x) ≤ R(m)`. -/
theorem exists_isPrimePow_psiLogRatio_ge {x : ℝ} (hx : 2 ≤ x) :
    ∃ m : ℕ, IsPrimePow m ∧ (m : ℝ) ≤ x ∧ psiLogRatio x ≤ psiLogRatio m := by
  classical
  set N := ⌊x⌋₊ with hN
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  set m := Nat.findGreatest IsPrimePow N with hm
  have hmP : IsPrimePow m := Nat.findGreatest_spec hN2 Nat.prime_two.isPrimePow
  have hmN : m ≤ N := Nat.findGreatest_le N
  have hm1 : 1 ≤ m := hmP.one_lt.le
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  -- `ψ` is constant on `[m, x]`
  have hψ : Chebyshev.psi x = Chebyshev.psi m := by
    rw [Chebyshev.psi, Chebyshev.psi, Nat.floor_natCast, ← hN,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le m) hmN]
    have hzero : ∑ i ∈ Finset.Ioc m N, ArithmeticFunction.vonMangoldt i = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      obtain ⟨hmn, hnN⟩ := Finset.mem_Ioc.mp hn
      exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
        (Nat.findGreatest_is_greatest hmn hnN)
    rw [hzero, add_zero]
  -- Bertrand: `N < 2m`
  have hN2m : N < 2 * m := by
    by_contra hcon
    push Not at hcon
    obtain ⟨p, hp, hmp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
    exact Nat.findGreatest_is_greatest hmp (hp2.trans hcon) hp.isPrimePow
  have hx2m : x ≤ 2 * m := by
    have : (N : ℝ) + 1 ≤ 2 * m := by exact_mod_cast hN2m
    linarith
  refine ⟨m, hmP, le_trans (by exact_mod_cast hmN) hNx, ?_⟩
  exact psiLogRatio_le_of_plateau hm1 (le_trans (by exact_mod_cast hmN) hNx) hx2m hψ

/-- A bound for `R` at every prime power bounds `R` on `[2, ∞)`. -/
theorem psiLogRatio_lt_of_isPrimePow_lt {C : ℝ} (hC : ∀ m : ℕ, IsPrimePow m → psiLogRatio m < C)
    {x : ℝ} (hx : 2 ≤ x) : psiLogRatio x < C := by
  obtain ⟨m, hm, -, hle⟩ := exists_isPrimePow_psiLogRatio_ge hx
  exact lt_of_le_of_lt hle (hC m hm)

end RHTower
