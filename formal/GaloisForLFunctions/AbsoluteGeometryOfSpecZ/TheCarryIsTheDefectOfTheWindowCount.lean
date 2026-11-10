import GaloisForLFunctions.RHTower.Matveev.FeldmanCommonDivisor
import GaloisForLFunctions.RHTower.DyadicVonMangoldtSqrtMass

/-!
# The carry is the defect of the window count

Over `𝔽_q[T]` addition has no carries and the count of monic polynomials is self-similar,
`N(qx) = qN(x) + 1`; the product of the monic irreducible polynomials of degree dividing `d` is
`T^{q^d} − T`, of degree exactly `q^d`. Over `ℤ` the same comparison has a remainder, the carry.

* **The carry cocycle.** `⌊(a+b)/k⌋ − ⌊a/k⌋ − ⌊b/k⌋ ∈ {0, 1}` is `1` exactly when adding `a` and `b`
  carries out of the residues modulo `k`, `k ≤ a mod k + b mod k`. Weighted by `Λ` it is the
  binomial coefficient (`log_choose_eq_sum_carry`):

    `log binom(a+b, a) = Σ_k Λ(k) · [k ≤ a mod k + b mod k]`.

  At `k = p^i` the bracket is Kummer's carry in base `p` (`padicValNat_choose`).
* **The multinomial** (`log_factorial_mul_sub_eq_sum_carry`):
  `log((qN)!/(N!)^q) = Σ_k Λ(k) ⌊q (N mod k)/k⌋`, where `⌊q (N mod k)/k⌋ = ⌊qN/k⌋ − q⌊N/k⌋` is the
  carry of the floor under multiplication by `q`.
* **The window** (`log_centralBinom_eq_carryTerm_add_window`). For `q = 2` the terms `N < k ≤ 2N`
  have carry `1`: they are the prime count `ψ(2N) − ψ(N)` of the window. The terms `k ≤ N` are the
  carry term (`carryTerm`): `log binom(2N, N) = carryTerm N + (ψ(2N) − ψ(N))`.
* **The carry term is a fixed positive proportion of the window count**
  (`tendsto_carryTerm_div`): `carryTerm N / N → 2 log 2 − 1 > 0`, while the window count is
  `N (1 + o(1))`. The comparison of the prime count of a window with an exact count has an error of
  the size of the count; its fluctuation is exactly minus the fluctuation of the window.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open GaloisForLFunctions.RHTower.Matveev

/-! ### The carry identities -/

/-- `log c!` as a sum over a longer range. -/
theorem log_factorial_eq_sum_Icc {c M : ℕ} (h : c ≤ M) :
    Real.log (c.factorial : ℝ) = ∑ k ∈ Icc 1 M, ((c / k : ℕ) : ℝ) * Λ k := by
  rw [log_factorial_eq_sum_vonMangoldt]
  refine Finset.sum_subset (Finset.Icc_subset_Icc_right h) fun k hk hk' => ?_
  have hlt : c < k := by
    by_contra hle
    exact hk' (mem_Icc.mpr ⟨(mem_Icc.mp hk).1, not_lt.mp hle⟩)
  rw [Nat.div_eq_of_lt hlt, Nat.cast_zero, zero_mul]

/-- **The binomial coefficient is the `Λ`-weighted number of carries.** -/
theorem log_choose_eq_sum_carry (a b : ℕ) :
    Real.log (((a + b).choose a : ℕ) : ℝ) =
      ∑ k ∈ Icc 1 (a + b), if k ≤ a % k + b % k then Λ k else 0 := by
  have hfac : (((a + b).choose a : ℕ) : ℝ) * (a.factorial : ℝ) * (b.factorial : ℝ) =
      ((a + b).factorial : ℝ) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial a b
    rw [← Nat.choose_symm_add] at h
    exact_mod_cast h
  have hc : (0 : ℝ) < (((a + b).choose a : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right a b)
  have ha : (0 : ℝ) < (a.factorial : ℝ) := by exact_mod_cast a.factorial_pos
  have hb : (0 : ℝ) < (b.factorial : ℝ) := by exact_mod_cast b.factorial_pos
  have hlog : Real.log (((a + b).choose a : ℕ) : ℝ) =
      Real.log ((a + b).factorial : ℝ) - Real.log (a.factorial : ℝ) -
        Real.log (b.factorial : ℝ) := by
    rw [← hfac, Real.log_mul (mul_pos hc ha).ne' hb.ne', Real.log_mul hc.ne' ha.ne']
    ring
  rw [hlog, log_factorial_eq_sum_Icc (le_refl (a + b)),
    log_factorial_eq_sum_Icc (Nat.le_add_right a b), log_factorial_eq_sum_Icc (Nat.le_add_left b a),
    ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun k hk => ?_
  rw [Nat.add_div (mem_Icc.mp hk).1]
  split_ifs <;> push_cast <;> ring

/-- The carry of the floor under multiplication by `q`:
`⌊qN/k⌋ = q⌊N/k⌋ + ⌊q (N mod k)/k⌋`. -/
theorem mul_div_eq_add_carry (q N : ℕ) {k : ℕ} (hk : 0 < k) :
    q * N / k = q * (N / k) + q * (N % k) / k := by
  conv_lhs => rw [← Nat.div_add_mod N k, mul_add, mul_left_comm]
  rw [Nat.mul_add_div hk]

/-- **The multinomial is the `Λ`-weighted carry of the floor.**
`log((qN)!/(N!)^q) = Σ_k Λ(k) ⌊q (N mod k)/k⌋`. -/
theorem log_factorial_mul_sub_eq_sum_carry {q : ℕ} (hq : 1 ≤ q) (N : ℕ) :
    Real.log ((q * N).factorial : ℝ) - q * Real.log (N.factorial : ℝ) =
      ∑ k ∈ Icc 1 (q * N), ((q * (N % k) / k : ℕ) : ℝ) * Λ k := by
  rw [log_factorial_eq_sum_Icc (le_refl (q * N)),
    log_factorial_eq_sum_Icc (Nat.le_mul_of_pos_left N hq), Finset.mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k hk => ?_
  rw [mul_div_eq_add_carry q N (mem_Icc.mp hk).1]
  push_cast
  ring

/-- Past `N` the carry of the floor is the window weight `⌊qN/k⌋`. -/
theorem carry_eq_of_lt (q : ℕ) {N k : ℕ} (h : N < k) : q * (N % k) / k = q * N / k := by
  rw [Nat.mod_eq_of_lt h]

/-! ### The window `(N, 2N]` -/

theorem Icc_one_eq_Ioc_zero (M : ℕ) : Icc 1 M = Ioc 0 M := by
  ext k; simp only [mem_Icc, mem_Ioc]; omega

theorem Ico_succ_succ_eq_Ioc (N M : ℕ) : Ico (N + 1) (M + 1) = Ioc N M := by
  ext k; simp only [mem_Ico, mem_Ioc]; omega

/-- The carry term of the window `(N, 2N]`: the `Λ`-weighted carries of `N + N` at the moduli
`k ≤ N`. -/
def carryTerm (N : ℕ) : ℝ := ∑ k ∈ Ioc 0 N, if k ≤ N % k + N % k then Λ k else 0

/-- The prime count of the window `(N, 2N]`. -/
def windowCount (N : ℕ) : ℝ := ∑ k ∈ Ioc N (2 * N), Λ k

/-- **The window comparison.** `log binom(2N, N)` is the carry term plus the prime count of the
window `(N, 2N]`. -/
theorem log_centralBinom_eq_carryTerm_add_window (N : ℕ) :
    Real.log ((Nat.centralBinom N : ℕ) : ℝ) = carryTerm N + windowCount N := by
  have h := log_choose_eq_sum_carry N N
  rw [← two_mul, ← Nat.centralBinom_eq_two_mul_choose] at h
  rw [h, Icc_one_eq_Ioc_zero,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le N) (by omega : N ≤ 2 * N), carryTerm, windowCount]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  obtain ⟨h1, h2⟩ := mem_Ioc.mp hk
  rw [Nat.mod_eq_of_lt h1, if_pos (by omega)]

/-- `ψ(2N) − ψ(N)` is the window count. -/
theorem chebyshevPsiReal_sub_eq_windowCount (N : ℕ) :
    RHTower.chebyshevPsiReal (2 * (N : ℝ)) - RHTower.chebyshevPsiReal (N : ℝ) = windowCount N := by
  have h2 : ⌊(2 : ℝ) * (N : ℝ)⌋₊ = 2 * N := by
    rw [show (2 : ℝ) * (N : ℝ) = ((2 * N : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  rw [RHTower.chebyshevPsiReal_eq_sum_range, RHTower.chebyshevPsiReal_eq_sum_range, h2,
    Nat.floor_natCast, ← Finset.sum_Ico_eq_sub _ (by omega : N + 1 ≤ 2 * N + 1), windowCount,
    Ico_succ_succ_eq_Ioc]

/-- **The prime number theorem on the window**: `windowCount N / N → 1`. -/
theorem tendsto_windowCount_div :
    Tendsto (fun N : ℕ => windowCount N / (N : ℝ)) atTop (𝓝 1) := by
  have h := RHTower.tendsto_chebyshevPsiReal_dyadic_sub.comp tendsto_natCast_atTop_atTop
  refine h.congr fun N => ?_
  simp only [Function.comp_apply]
  rw [chebyshevPsiReal_sub_eq_windowCount]

/-- `log binom(2N, N) / N → 2 log 2`. -/
theorem tendsto_log_centralBinom_div :
    Tendsto (fun N : ℕ => Real.log ((Nat.centralBinom N : ℕ) : ℝ) / (N : ℝ)) atTop
      (𝓝 (2 * Real.log 2)) := by
  -- `log(2N)/N → 0`
  have hlog : Tendsto (fun N : ℕ => Real.log (2 * (N : ℝ)) / (N : ℝ)) atTop (𝓝 0) := by
    have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Tendsto (fun N : ℕ => 2 * (N : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
    have h3 := (h1.comp h2).const_mul 2
    rw [mul_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    simp only [Function.comp_apply, pow_one, one_mul, add_zero]
    field_simp
  have hlow : Tendsto (fun N : ℕ => 2 * Real.log 2 - Real.log (2 * (N : ℝ)) / (N : ℝ)) atTop
      (𝓝 (2 * Real.log 2)) := by
    simpa using (tendsto_const_nhds (x := 2 * Real.log 2)).sub hlog
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · -- `4^N ≤ 2N binom(2N, N)`
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hcb : (0 : ℝ) < ((Nat.centralBinom N : ℕ) : ℝ) := by
      exact_mod_cast Nat.centralBinom_pos N
    have hle : (4 : ℝ) ^ N ≤ 2 * (N : ℝ) * ((Nat.centralBinom N : ℕ) : ℝ) := by
      exact_mod_cast Nat.four_pow_le_two_mul_self_mul_centralBinom N hN
    have h5 := Real.log_le_log (by positivity) hle
    rw [Real.log_pow, Real.log_mul (by positivity) hcb.ne', h4] at h5
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN']
    linarith
  · -- `binom(2N, N) ≤ 4^N`
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hcb : (0 : ℝ) < ((Nat.centralBinom N : ℕ) : ℝ) := by
      exact_mod_cast Nat.centralBinom_pos N
    have hle : ((Nat.centralBinom N : ℕ) : ℝ) ≤ (4 : ℝ) ^ N := by
      exact_mod_cast Nat.centralBinom_le_four_pow N
    have h5 := Real.log_le_log hcb hle
    rw [Real.log_pow, h4] at h5
    rw [div_le_iff₀ hN']
    linarith

/-- **The carry term is a fixed positive proportion of the window count**:
`carryTerm N / N → 2 log 2 − 1`. -/
theorem tendsto_carryTerm_div :
    Tendsto (fun N : ℕ => carryTerm N / (N : ℝ)) atTop (𝓝 (2 * Real.log 2 - 1)) := by
  refine (tendsto_log_centralBinom_div.sub tendsto_windowCount_div).congr fun N => ?_
  rw [log_centralBinom_eq_carryTerm_add_window]
  ring

/-- The limiting proportion is positive. -/
theorem carry_proportion_pos : 0 < 2 * Real.log 2 - 1 := by
  have := Real.log_two_gt_d9
  linarith

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ

#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.log_factorial_mul_sub_eq_sum_carry
#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.tendsto_carryTerm_div
