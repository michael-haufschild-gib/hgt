import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonDivergenceLivesOnTheTorsionOrbits

/-!
# The Liouville gauge flips the polar divergence

A real sign twin of `ζ` replaces `Λ` by `εΛ` with `ε` completely multiplicative and `ε² = 1`; its
prime form is `P` in the gauge `x ↦ εx` (AIT `signTwistForm_eq`), so every statement about the
spectrum of `P` alone is gauge blind. The archimedean place is gauge invariant, and its counterterm is
the polar direction of uniform profiles. This file shows that the **matching** of the prime
divergence with that polar direction is gauge charged: for Liouville's `λ(n) = (−1)^{Ω(n)}` it flips
sign.

* **The twisted Mertens sum** (`liouvilleMertensSum_le`, `neg_le_liouvilleMertensSum`):
  `A_λ(y) = Σ_{t ≤ y} λ(t)Λ(t)/t = −log y + O(1)`. At primes `λ = −1`; the even prime powers carry the
  difference and sum to at most `K = Σ 4 n^{−3/2}`.
* **Rows of the Liouville pole vector** (`sum_weilPrimeKernel_liouvillePole`): for `v = λ u`,
  `(P v)_m = (A_λ(⌊N/m⌋) + D_λ(m)) v_m` with `D_λ(m) = Σ_{t ∣ m} λ(t)Λ(t)`, and the divisor part
  averages to the Mertens part (`sum_divisors_div_swap`: Dirichlet's hyperbola identity).
* **The bottom of the spectrum** (`atomicWeilForm_liouvillePole_le`): `P_N(λu) ≤ −(log N − C) |λu|²`.
  With `|P_N(x)| ≤ (log N + log 4 + 4)|x|²` (`abs_atomicWeilForm_le`), the spectrum of the atomic
  prime form fills `[−log N, log N]` up to `O(1)` at both ends: the pole vector at the top, the
  Liouville pole vector at the bottom (`atomicWeilForm_spectrum_ends`).
* **The polar divergence flips** (`abs_liouvilleBilinear_add_le`,
  `abs_liouvilleForm_stepProfile_add_le`): on uniform step profiles the Liouville twin's prime form is
  `P(λx) = −ℓ(x)² + O(log N · |c|-mass)`, where `ζ`'s is `+ℓ(x)²`.

So the prime place of `ζ` diverges along the archimedean polar direction with coefficient `+1`, the
Liouville twin with coefficient `−1`. The two places' counterterms are matched at the Euler gauge and
anti-matched at the Liouville gauge: polar matching is a gauge-charged property of the coupled
renormalization, although each place's counterterm separately is blind.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

/-! ### Liouville's sign -/

/-- **Liouville's sign** `λ(n) = (−1)^{Ω(n)}`. -/
def liouvilleSign (n : ℕ) : ℝ := (-1) ^ (Ω n)

theorem liouvilleSign_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    liouvilleSign (m * n) = liouvilleSign m * liouvilleSign n := by
  rw [liouvilleSign, cardFactors_mul hm hn, pow_add]; rfl

theorem liouvilleSign_mul_self (n : ℕ) : liouvilleSign n * liouvilleSign n = 1 := by
  rw [liouvilleSign, ← pow_add, ← two_mul, pow_mul]; norm_num

theorem liouvilleSign_prime_pow {p k : ℕ} (hp : p.Prime) : liouvilleSign (p ^ k) = (-1) ^ k := by
  rw [liouvilleSign, cardFactors_apply_prime_pow hp]

/-- `λ(n) = λ(m) λ(n/m)` along a divisibility `m ∣ n`. -/
theorem liouvilleSign_of_dvd {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : m ∣ n) :
    liouvilleSign n = liouvilleSign m * liouvilleSign (n / m) := by
  have hq : n / m ≠ 0 := fun h0 => hn (by rw [← Nat.mul_div_cancel' h, h0, mul_zero])
  rw [← liouvilleSign_mul hm hq, Nat.mul_div_cancel' h]

/-! ### The twisted Mertens sum -/

/-- The twisted Mertens sum `A_λ(y) = Σ_{t ≤ y} λ(t)Λ(t)/t`. -/
def liouvilleMertensSum (y : ℕ) : ℝ := ∑ t ∈ Icc 1 y, liouvilleSign t * Λ t / t

/-- **The even prime powers**: `Σ_{t ≤ y} (1 + λ(t))Λ(t)/t ≤ K`. Only `t = q^{2j}` contribute, with
`t = s²`, `s = q^j`, and `2 log q/s² ≤ 4 s^{−3/2}`. -/
theorem sum_one_add_liouville_le (y : ℕ) :
    ∑ t ∈ Icc 1 y, (1 + liouvilleSign t) * Λ t / t ≤ tameConstant := by
  have hnn : ∀ (t : ℕ) (s : Finset ℕ),
      0 ≤ ∑ r ∈ s, (if t = r ^ 2 then 4 * ((r : ℝ) ^ ((3 : ℝ) / 2))⁻¹ else 0) :=
    fun t s => sum_nonneg fun r _ => by split_ifs <;> positivity
  have hterm : ∀ t ∈ Icc 1 y, (1 + liouvilleSign t) * Λ t / t ≤
      ∑ r ∈ Icc 1 y, (if t = r ^ 2 then 4 * ((r : ℝ) ^ ((3 : ℝ) / 2))⁻¹ else 0) := by
    intro t ht
    by_cases hΛ : Λ t = 0
    · rw [hΛ, mul_zero, zero_div]; exact hnn t _
    obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff t).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    rw [liouvilleSign_prime_pow hq]
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | hodd
    · -- `t = s²` with `s = q^j`
      have hj : j ≠ 0 := by omega
      set s := q ^ j with hs
      have hs2 : 2 ≤ s := hq.two_le.trans (Nat.le_self_pow hj q)
      have hts : q ^ (j + j) = s ^ 2 := by rw [hs, ← pow_mul, mul_two]
      have hsmem : s ∈ Icc 1 y := by
        refine mem_Icc.mpr ⟨by omega, ?_⟩
        have h1 := (mem_Icc.mp ht).2
        rw [hts] at h1
        nlinarith
      rw [← sum_erase_add _ _ hsmem, if_pos hts]
      have hΛq : Λ (q ^ (j + j)) = Real.log q := vonMangoldt_prime_pow hq (by omega)
      have heven : ((-1 : ℝ) ^ (j + j)) = 1 := by rw [← two_mul, pow_mul]; norm_num
      rw [heven, hΛq, hts]
      have hrest := hnn (s ^ 2) ((Icc 1 y).erase s)
      -- `2 log q/s² ≤ 4 s^{−3/2}`
      have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
      have hlogqs : Real.log q ≤ Real.log s := Real.log_le_log (by exact_mod_cast hq.pos)
        (by exact_mod_cast Nat.le_self_pow hj q)
      have hlog := RHTower.Mertens.log_le_rpow hs0 (show (0 : ℝ) < 1 / 2 by norm_num)
      rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num] at hlog
      have h32 : (s : ℝ) ^ ((3 : ℝ) / 2) = s * (s : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hs0, Real.rpow_one]
      have hsq : (s : ℝ) ^ ((1 : ℝ) / 2) * (s : ℝ) ^ ((1 : ℝ) / 2) = s := by
        rw [← Real.rpow_add hs0]; norm_num
      have hr : 0 < (s : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hs0 _
      have key : (1 + 1) * Real.log q / ((s ^ 2 : ℕ) : ℝ) ≤
          4 * ((s : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
        rw [h32, Nat.cast_pow, div_le_iff₀ (by positivity)]
        have hpos : 0 < (s : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 2) := by positivity
        rw [show 4 * ((s : ℝ) * (s : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * (s : ℝ) ^ 2 =
          4 * (s : ℝ) ^ ((1 : ℝ) / 2) by field_simp; nlinarith [hsq]]
        nlinarith
      linarith
    · rw [hodd.neg_one_pow]
      simp only [add_neg_cancel, zero_mul, zero_div]
      exact hnn _ _
  calc ∑ t ∈ Icc 1 y, (1 + liouvilleSign t) * Λ t / t
      ≤ ∑ t ∈ Icc 1 y, ∑ r ∈ Icc 1 y, (if t = r ^ 2 then 4 * ((r : ℝ) ^ ((3 : ℝ) / 2))⁻¹ else 0) :=
        sum_le_sum hterm
    _ = ∑ r ∈ Icc 1 y, ∑ t ∈ Icc 1 y, (if t = r ^ 2 then 4 * ((r : ℝ) ^ ((3 : ℝ) / 2))⁻¹ else 0) :=
        sum_comm
    _ ≤ ∑ r ∈ Icc 1 y, 4 * ((r : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
        refine sum_le_sum fun r _ => ?_
        rw [sum_ite_eq']
        split_ifs
        · exact le_rfl
        · positivity
    _ ≤ tameConstant := summable_tame.sum_le_tsum _ fun n _ => by positivity

/-- **`A_λ(y) ≤ −log y + log 4 + 4 + K`.** -/
theorem liouvilleMertensSum_le {y : ℕ} (hy : 1 ≤ y) :
    liouvilleMertensSum y ≤ -Real.log y + (Real.log 4 + 4 + tameConstant) := by
  have hmert := (abs_le.mp (RHTower.Mertens.mertens_first y hy)).1
  have hsplit : liouvilleMertensSum y = -(∑ t ∈ Icc 1 y, Λ t / t) +
      ∑ t ∈ Icc 1 y, (1 + liouvilleSign t) * Λ t / t := by
    rw [liouvilleMertensSum, ← sum_neg_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun t _ => by ring
  rw [hsplit]
  linarith [sum_one_add_liouville_le y]

/-- **`A_λ(y) ≥ −log y − log 4 − 4`**: the even prime powers only add. -/
theorem neg_le_liouvilleMertensSum {y : ℕ} (hy : 1 ≤ y) :
    -Real.log y - (Real.log 4 + 4) ≤ liouvilleMertensSum y := by
  have hmert := (abs_le.mp (RHTower.Mertens.mertens_first y hy)).2
  have hsplit : liouvilleMertensSum y = -(∑ t ∈ Icc 1 y, Λ t / t) +
      ∑ t ∈ Icc 1 y, (1 + liouvilleSign t) * Λ t / t := by
    rw [liouvilleMertensSum, ← sum_neg_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun t _ => by ring
  have hnn : 0 ≤ ∑ t ∈ Icc 1 y, (1 + liouvilleSign t) * Λ t / t := by
    refine sum_nonneg fun t _ => div_nonneg (mul_nonneg ?_ vonMangoldt_nonneg) (Nat.cast_nonneg _)
    rcases neg_one_pow_eq_or ℝ (Ω t) with h | h <;> rw [liouvilleSign, h] <;> norm_num
  rw [hsplit]
  linarith

/-! ### Dirichlet's hyperbola identity -/

/-- **Dirichlet's hyperbola identity**: `Σ_{m ≤ M} (Σ_{t ∣ m} g(t))/m = Σ_{k ≤ M} (Σ_{t ≤ M/k} g(t)/t)/k`. -/
theorem sum_divisors_div_swap (g : ℕ → ℝ) (M : ℕ) :
    ∑ m ∈ Icc 1 M, (∑ t ∈ m.divisors, g t) / m =
      ∑ k ∈ Icc 1 M, (∑ t ∈ Icc 1 (M / k), g t / t) / k := by
  -- both sides are `Σ_{tk ≤ M} g(t)/(tk)`
  have hL : ∑ m ∈ Icc 1 M, (∑ t ∈ m.divisors, g t) / m =
      ∑ t ∈ Icc 1 M, ∑ m ∈ (Icc 1 M).filter (t ∣ ·), g t / m := by
    simp only [sum_div]
    refine sum_comm' fun m t => ?_
    simp only [mem_Icc, mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, htm, -⟩
      exact ⟨⟨⟨h1, h2⟩, htm⟩, Nat.pos_of_dvd_of_pos htm h1, (Nat.le_of_dvd h1 htm).trans h2⟩
    · rintro ⟨⟨⟨h1, h2⟩, htm⟩, -, -⟩
      exact ⟨⟨h1, h2⟩, htm, by omega⟩
  have hinner : ∀ t ∈ Icc 1 M, ∑ m ∈ (Icc 1 M).filter (t ∣ ·), g t / m =
      ∑ k ∈ Icc 1 (M / t), g t / t / k := by
    intro t ht
    have ht0 : 0 < t := (mem_Icc.mp ht).1
    rw [filter_dvd_Icc_eq_image ht0, sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left ht0 h]
    exact sum_congr rfl fun k _ => by push_cast; rw [div_div]
  rw [hL, sum_congr rfl hinner]
  simp only [sum_div]
  refine sum_comm' fun t k => ?_
  simp only [mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    rw [Nat.le_div_iff_mul_le h1] at h4
    exact ⟨⟨h1, (Nat.le_div_iff_mul_le h3).mpr (by linarith [mul_comm t k])⟩, h3, by nlinarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    rw [Nat.le_div_iff_mul_le h3] at h2
    exact ⟨⟨h1, by nlinarith⟩, h3, (Nat.le_div_iff_mul_le h1).mpr (by linarith [mul_comm t k])⟩

/-- One step of the upper telescope: `2 log(k + 1)/(k + 1) − 1/(k(k + 1)) ≤ log²(k + 1) − log² k`. -/
theorem log_sq_step_ge {k : ℕ} (hk : 1 ≤ k) :
    2 * (Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1)) - 1 / ((k : ℝ) * (k + 1)) ≤
      Real.log ((k : ℝ) + 1) ^ 2 - Real.log k ^ 2 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  -- `log(k + 1) − log k ≥ 1/(k + 1)` and `≤ 1/k`
  have hab : 1 / ((k : ℝ) + 1) ≤ Real.log (k + 1) - Real.log k := by
    rw [← Real.log_div (by positivity) hk0.ne']
    have h1 : Real.log (((k : ℝ) + 1) / k) = -Real.log (k / ((k : ℝ) + 1)) := by
      rw [← Real.log_inv, inv_div]
    have hfrac : (k : ℝ) / (k + 1) = 1 - 1 / ((k : ℝ) + 1) := by field_simp; ring
    have h2 : Real.log (k / ((k : ℝ) + 1)) ≤ -(1 / ((k : ℝ) + 1)) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < k / (k + 1) by positivity)
      linarith [hfrac]
    linarith
  have hab' : Real.log (k + 1) - Real.log k ≤ 1 / k := by
    rw [← Real.log_div (by positivity) hk0.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k + 1) / k by positivity)
    have h1 : ((k : ℝ) + 1) / k - 1 = 1 / k := by field_simp; ring
    linarith
  have hpos : 0 ≤ 2 * Real.log (k + 1) - 1 / (k : ℝ) := by
    have h2 : Real.log 2 ≤ Real.log (k + 1) := Real.log_le_log (by norm_num) (by linarith)
    have hl2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have h3 : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one hk0]; exact hk'
    linarith
  have hfac : Real.log (k + 1) ^ 2 - Real.log k ^ 2 = (Real.log (k + 1) - Real.log k) *
      (2 * Real.log (k + 1) - (Real.log (k + 1) - Real.log k)) := by ring
  rw [hfac]
  calc 2 * (Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1)) - 1 / ((k : ℝ) * (k + 1))
      = 1 / ((k : ℝ) + 1) * (2 * Real.log (k + 1) - 1 / k) := by field_simp
    _ ≤ (Real.log (k + 1) - Real.log k) * (2 * Real.log (k + 1) - 1 / k) :=
        mul_le_mul_of_nonneg_right hab hpos
    _ ≤ (Real.log (k + 1) - Real.log k) *
          (2 * Real.log (k + 1) - (Real.log (k + 1) - Real.log k)) :=
        mul_le_mul_of_nonneg_left (by linarith)
          (by linarith [hab, show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity])

/-- `Σ_{n ≤ M} log n/n ≤ ½ log² M + ½ − 1/(2M)` for `M ≥ 1`. -/
theorem sum_log_div_le_aux {M : ℕ} (hM : 1 ≤ M) :
    ∑ n ∈ Icc 1 M, Real.log n / n ≤ Real.log M ^ 2 / 2 + 1 / 2 - 1 / (2 * M) := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hstep := log_sq_step_ge hk
    push_cast
    have htel : 1 / ((k : ℝ) * (k + 1)) = 1 / k - 1 / (k + 1) := by field_simp; ring
    have h1 : 1 / (2 * (k : ℝ)) = (1 / k) / 2 := by ring
    have h2 : 1 / (2 * ((k : ℝ) + 1)) = (1 / ((k : ℝ) + 1)) / 2 := by rw [div_div, mul_comm]
    rw [h1] at ih
    rw [h2]
    linarith

/-- `Σ_{n ≤ M} log n/n ≤ ½ log² M + ½`. -/
theorem sum_log_div_le (M : ℕ) : ∑ n ∈ Icc 1 M, Real.log n / n ≤ Real.log M ^ 2 / 2 + 1 / 2 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · have h := sum_log_div_le_aux hM
    have : 0 ≤ 1 / (2 * (M : ℝ)) := by positivity
    linarith

/-! ### The Liouville pole vector -/

/-- The **Liouville pole vector** `λ(n) n^{−1/2}`, truncated at `M`. -/
def liouvilleTrunc (M n : ℕ) : ℝ := liouvilleSign n * truncPole M n

/-- The divisor part `D_λ(m) = Σ_{t ∣ m} λ(t)Λ(t)`. -/
def liouvilleDivisorSum (m : ℕ) : ℝ := ∑ t ∈ m.divisors, liouvilleSign t * Λ t

theorem sum_up_liouville_eq {m N : ℕ} (hm : 0 < m) :
    ∑ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then
      liouvilleSign (n / m) * Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) = liouvilleMertensSum (N / m) := by
  have hterm : ∀ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then
      liouvilleSign (n / m) * Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) =
      if m ∣ n then liouvilleSign (n / m) * Λ (n / m) / ((n / m : ℕ) : ℝ) else 0 := by
    intro n _
    by_cases h : m ∣ n
    · by_cases h' : m = n
      · subst h'; simp [Nat.div_self hm]
      · rw [if_pos ⟨h, h'⟩, if_pos h]
    · rw [if_neg (fun h'' => h h''.1), if_neg h]
  rw [sum_congr rfl hterm, ← sum_filter, filter_dvd_Icc_eq_image hm,
    sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hm h, liouvilleMertensSum]
  exact sum_congr rfl fun t _ => by rw [Nat.mul_div_cancel_left t hm]

theorem sum_down_liouville_eq {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    ∑ n ∈ Icc 1 N, (if n ∣ m ∧ n ≠ m then liouvilleSign (m / n) * Λ (m / n) else 0) =
      liouvilleDivisorSum m := by
  have hterm : ∀ n ∈ Icc 1 N, (if n ∣ m ∧ n ≠ m then liouvilleSign (m / n) * Λ (m / n) else 0) =
      if n ∣ m then liouvilleSign (m / n) * Λ (m / n) else 0 := by
    intro n _
    by_cases h : n ∣ m
    · by_cases h' : n = m
      · subst h'; simp [Nat.div_self hm]
      · rw [if_pos ⟨h, h'⟩, if_pos h]
    · rw [if_neg (fun h'' => h h''.1), if_neg h]
  rw [sum_congr rfl hterm, ← sum_filter, filter_Icc_dvd_eq_divisors hm hmN, liouvilleDivisorSum]
  exact Nat.sum_div_divisors m (fun t => liouvilleSign t * Λ t)

/-- `P(m, n) u_n = u_m P(m, n) √(m/n)`. -/
theorem weilPrimeKernel_mul_poleVector {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    weilPrimeKernel m n * poleVector n =
      poleVector m * (weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [poleVector, poleVector, Real.sqrt_div' _ hn'.le]
  have hsm : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm').ne'
  have hsn : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn').ne'
  field_simp

/-- **The rows of the Liouville pole vector**: for `m ≤ M ≤ N`,
`Σ_{n ≤ M} P(m, n) λ(n) u_n = (A_λ(⌊M/m⌋) + D_λ(m)) λ(m) u_m`. -/
theorem sum_weilPrimeKernel_liouville {m M : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    ∑ n ∈ Icc 1 M, weilPrimeKernel m n * (liouvilleSign n * poleVector n) =
      (liouvilleMertensSum (M / m) + liouvilleDivisorSum m) * (liouvilleSign m * poleVector m) := by
  have hterm : ∀ n ∈ Icc 1 M, weilPrimeKernel m n * (liouvilleSign n * poleVector n) =
      liouvilleSign m * poleVector m *
        ((if m ∣ n ∧ m ≠ n then liouvilleSign (n / m) * Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) +
          (if n ∣ m ∧ n ≠ m then liouvilleSign (m / n) * Λ (m / n) else 0)) := by
    intro n hn
    have hn0 := pos_of_mem_Icc' hn
    have hstep : weilPrimeKernel m n * (liouvilleSign n * poleVector n) =
        liouvilleSign n * (poleVector m * (weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n))) := by
      rw [← weilPrimeKernel_mul_poleVector hm hn0]; ring
    rw [hstep, weilPrimeKernel_mul_sqrt_ratio hm hn0]
    by_cases h1 : m ∣ n ∧ m ≠ n
    · have h2 : ¬ (n ∣ m ∧ n ≠ m) := fun h => h1.2 (Nat.dvd_antisymm h1.1 h.1)
      rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2,
        liouvilleSign_of_dvd hm.ne' hn0.ne' h1.1]
      ring
    · by_cases h2 : n ∣ m ∧ n ≠ m
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
        have hsign : liouvilleSign n = liouvilleSign m * liouvilleSign (m / n) := by
          have h := liouvilleSign_of_dvd hn0.ne' hm.ne' h2.1
          calc liouvilleSign n
              = liouvilleSign n * (liouvilleSign (m / n) * liouvilleSign (m / n)) := by
                rw [liouvilleSign_mul_self, mul_one]
            _ = liouvilleSign n * liouvilleSign (m / n) * liouvilleSign (m / n) := by ring
            _ = liouvilleSign m * liouvilleSign (m / n) := by rw [← h]
        rw [hsign]
        ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
        ring
  rw [sum_congr rfl hterm, ← mul_sum, sum_add_distrib, sum_up_liouville_eq hm,
    sum_down_liouville_eq hm hmM]
  ring

/-- **The Liouville pole Gram**: for `M ≤ M' ≤ N`,
`⟨λu^{(M)}, P λu^{(M')}⟩ = Σ_{m ≤ M} (A_λ(⌊M'/m⌋) + D_λ(m))/m`. -/
theorem primeBilinear_liouvilleTrunc_eq {M M' N : ℕ} (hMM' : M ≤ M') (hM'N : M' ≤ N) :
    primeBilinear N (liouvilleTrunc M) (liouvilleTrunc M') =
      ∑ m ∈ Icc 1 M, (liouvilleMertensSum (M' / m) + liouvilleDivisorSum m) / m := by
  unfold primeBilinear
  have hrow : ∀ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, liouvilleTrunc M m * liouvilleTrunc M' n *
      weilPrimeKernel m n = if m ≤ M then
        (liouvilleMertensSum (M' / m) + liouvilleDivisorSum m) / m else 0 := by
    intro m hm
    have hm0 := pos_of_mem_Icc' hm
    unfold liouvilleTrunc truncPole
    split_ifs with hmM
    · have hinner : ∑ n ∈ Icc 1 N, liouvilleSign m * poleVector m *
          (liouvilleSign n * if n ≤ M' then poleVector n else 0) * weilPrimeKernel m n =
          liouvilleSign m * poleVector m *
            ∑ n ∈ Icc 1 M', weilPrimeKernel m n * (liouvilleSign n * poleVector n) := by
        rw [mul_sum, ← sum_truncate hM'N]
        refine sum_congr rfl fun n _ => ?_
        split_ifs <;> ring
      rw [hinner, sum_weilPrimeKernel_liouville hm0 (hmM.trans hMM')]
      have h1 : liouvilleSign m * liouvilleSign m = 1 := liouvilleSign_mul_self m
      have h2 : poleVector m * poleVector m = 1 / m := by rw [← sq, poleVector_sq]
      calc liouvilleSign m * poleVector m * ((liouvilleMertensSum (M' / m) +
            liouvilleDivisorSum m) * (liouvilleSign m * poleVector m))
          = (liouvilleSign m * liouvilleSign m) * (poleVector m * poleVector m) *
            (liouvilleMertensSum (M' / m) + liouvilleDivisorSum m) := by ring
        _ = (liouvilleMertensSum (M' / m) + liouvilleDivisorSum m) / m := by
            rw [h1, h2]; ring
    · simp
  rw [sum_congr rfl hrow, sum_truncate (hMM'.trans hM'N)]

/-- The divisor part averages to the Mertens part (Dirichlet's hyperbola). -/
theorem sum_liouvilleDivisorSum_div (M : ℕ) :
    ∑ m ∈ Icc 1 M, liouvilleDivisorSum m / m = ∑ k ∈ Icc 1 M, liouvilleMertensSum (M / k) / k := by
  have h := sum_divisors_div_swap (fun t => liouvilleSign t * Λ t) M
  simpa only [liouvilleDivisorSum, liouvilleMertensSum, mul_div_assoc] using h

/-- Upper bound for a Mertens-weighted harmonic sum: for `M ≤ X`,
`Σ_{m ≤ M} A_λ(⌊X/m⌋)/m ≤ −H_M log X + Σ_{m ≤ M} log m/m + (log 2 + log 4 + 4 + K) H_M`. -/
theorem sum_liouvilleMertens_div_le {M X : ℕ} (hMX : M ≤ X) :
    ∑ m ∈ Icc 1 M, liouvilleMertensSum (X / m) / m ≤
      -(harmonicSum M * Real.log X) + ∑ m ∈ Icc 1 M, Real.log m / m +
        (Real.log 2 + (Real.log 4 + 4 + tameConstant)) * harmonicSum M := by
  set C := Real.log 2 + (Real.log 4 + 4 + tameConstant)
  have hterm : ∀ m ∈ Icc 1 M, liouvilleMertensSum (X / m) / m ≤
      -(1 / (m : ℝ) * Real.log X) + Real.log m / m + C * (1 / m) := by
    intro m hm
    have hm0 := pos_of_mem_Icc' hm
    have hmX := (mem_Icc.mp hm).2.trans hMX
    have hq : 1 ≤ X / m := (Nat.le_div_iff_mul_le hm0).mpr (by linarith)
    have h1 := liouvilleMertensSum_le hq
    have h2 := log_le_log_div_add_log hm0 hmX
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
    have : liouvilleMertensSum (X / m) ≤ -Real.log X + Real.log m + C := by
      simp only [C]; linarith
    calc liouvilleMertensSum (X / m) / m ≤ (-Real.log X + Real.log m + C) / m :=
          div_le_div_of_nonneg_right this hm'.le
      _ = -(1 / (m : ℝ) * Real.log X) + Real.log m / m + C * (1 / m) := by ring
  have hR : ∑ m ∈ Icc 1 M, (-(1 / (m : ℝ) * Real.log X) + Real.log m / m + C * (1 / m)) =
      -(harmonicSum M * Real.log X) + ∑ m ∈ Icc 1 M, Real.log m / m + C * harmonicSum M := by
    rw [sum_add_distrib, sum_add_distrib, sum_neg_distrib, ← sum_mul, ← mul_sum]
    rfl
  exact (sum_le_sum hterm).trans_eq hR

/-- Lower bound: for `M ≤ X`, `Σ_{m ≤ M} A_λ(⌊X/m⌋)/m ≥ −H_M log X + Σ log m/m − (log 4 + 4) H_M`. -/
theorem le_sum_liouvilleMertens_div {M X : ℕ} (hMX : M ≤ X) :
    -(harmonicSum M * Real.log X) + ∑ m ∈ Icc 1 M, Real.log m / m -
        (Real.log 4 + 4) * harmonicSum M ≤ ∑ m ∈ Icc 1 M, liouvilleMertensSum (X / m) / m := by
  have hterm : ∀ m ∈ Icc 1 M, -(1 / (m : ℝ) * Real.log X) + Real.log m / m -
      (Real.log 4 + 4) * (1 / m) ≤ liouvilleMertensSum (X / m) / m := by
    intro m hm
    have hm0 := pos_of_mem_Icc' hm
    have hmX := (mem_Icc.mp hm).2.trans hMX
    have hq : 1 ≤ X / m := (Nat.le_div_iff_mul_le hm0).mpr (by linarith)
    have h1 := neg_le_liouvilleMertensSum hq
    have h2 := log_div_add_log_le hm0 hmX
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
    have : -Real.log X + Real.log m - (Real.log 4 + 4) ≤ liouvilleMertensSum (X / m) := by
      linarith
    calc -(1 / (m : ℝ) * Real.log X) + Real.log m / m - (Real.log 4 + 4) * (1 / m)
        = (-Real.log X + Real.log m - (Real.log 4 + 4)) / m := by ring
      _ ≤ liouvilleMertensSum (X / m) / m := div_le_div_of_nonneg_right this hm'.le
  have hR : ∑ m ∈ Icc 1 M, (-(1 / (m : ℝ) * Real.log X) + Real.log m / m -
      (Real.log 4 + 4) * (1 / m)) = -(harmonicSum M * Real.log X) +
        ∑ m ∈ Icc 1 M, Real.log m / m - (Real.log 4 + 4) * harmonicSum M := by
    rw [sum_sub_distrib, sum_add_distrib, sum_neg_distrib, ← sum_mul, ← mul_sum]
    rfl
  exact hR.symm.trans_le (sum_le_sum hterm)

/-- The constant of the Liouville polar flip. -/
def flipConstant : ℝ := 2 * Real.log 8 + 10 + 2 * tameConstant

/-- **The Liouville pole Gram is minus the product of polar functionals**: for `1 ≤ M ≤ M' ≤ N`,
`|⟨λu^{(M)}, P λu^{(M')}⟩ + H_M H_{M'}| ≤ C_λ H_M`. -/
theorem abs_primeBilinear_liouvilleTrunc_add_le {M M' N : ℕ} (hM : 1 ≤ M) (hMM' : M ≤ M')
    (hM'N : M' ≤ N) :
    |primeBilinear N (liouvilleTrunc M) (liouvilleTrunc M') + harmonicSum M * harmonicSum M'| ≤
      flipConstant * harmonicSum M := by
  rw [primeBilinear_liouvilleTrunc_eq hMM' hM'N]
  have hsplit : ∑ m ∈ Icc 1 M, (liouvilleMertensSum (M' / m) + liouvilleDivisorSum m) / m =
      ∑ m ∈ Icc 1 M, liouvilleMertensSum (M' / m) / m +
        ∑ k ∈ Icc 1 M, liouvilleMertensSum (M / k) / k := by
    rw [← sum_liouvilleDivisorSum_div, ← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  rw [hsplit]
  have hU1 := sum_liouvilleMertens_div_le (X := M') hMM'
  have hU2 := sum_liouvilleMertens_div_le (X := M) (le_refl M)
  have hL1 := le_sum_liouvilleMertens_div (X := M') hMM'
  have hL2 := le_sum_liouvilleMertens_div (X := M) (le_refl M)
  have hS1 := sum_log_div_le M
  have hS2 := sum_log_div_ge hM
  have hH1 := one_le_harmonicSum hM
  have hHle := harmonicSum_le M
  have hHge := log_le_harmonicSum M
  have hH'le := harmonicSum_le M'
  have hH'ge := log_le_harmonicSum M'
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have hlogM1 : Real.log M ≤ Real.log (M + 1) :=
    Real.log_le_log (by exact_mod_cast hM) (by linarith)
  have hK := tameConstant_nonneg
  have hl2 : Real.log 2 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
  have hl4 : Real.log 4 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
  have hl24 : Real.log 8 = Real.log 4 + Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hl2pos : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  -- `log² M ≤ H_M log M` and `H_M log M ≤ log M + log²(M + 1)`
  have hsq1 : Real.log M ^ 2 ≤ harmonicSum M * Real.log M := by nlinarith
  have hsq2 : harmonicSum M * Real.log M ≤ Real.log M + Real.log (M + 1) ^ 2 := by
    nlinarith [pow_le_pow_left₀ hlogM hlogM1 2]
  have hHH : harmonicSum M * Real.log M' ≤ harmonicSum M * harmonicSum M' :=
    mul_le_mul_of_nonneg_left hH'ge (by linarith)
  have hHH' : harmonicSum M * harmonicSum M' ≤ harmonicSum M * Real.log M' + harmonicSum M := by
    nlinarith
  unfold flipConstant
  rw [abs_le]
  constructor <;> nlinarith

/-! ### The bottom of the spectrum -/

/-- **The spectrum of the atomic prime form is two-sided**: `|P_N(x)| ≤ (log N + log 4 + 4)|x|²`,
since `P` has nonnegative entries. -/
theorem abs_atomicWeilForm_le (N : ℕ) (x : ℕ → ℝ) :
    |atomicWeilForm N x| ≤ (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have h := atomicWeilForm_le_log N (fun n => |x n|)
  simp only [sq_abs] at h
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun m _ => abs_sum_le_sum_abs _ _).trans ?_)
  refine le_of_eq_of_le ?_ h
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (weilPrimeKernel_nonneg m n)]

/-- **The Liouville pole vector sits at the bottom**: `P_N(λu) ≤ −(log N − C_λ)|λu|²`. -/
theorem atomicWeilForm_liouvillePole_le {N : ℕ} (hN : 1 ≤ N) :
    atomicWeilForm N (liouvilleTrunc N) ≤
      -(Real.log N - flipConstant) * ∑ n ∈ Icc 1 N, liouvilleTrunc N n ^ 2 := by
  have hmass : ∑ n ∈ Icc 1 N, liouvilleTrunc N n ^ 2 = harmonicSum N := by
    rw [← sum_poleVector_sq]
    refine sum_congr rfl fun n hn => ?_
    rw [liouvilleTrunc, truncPole, if_pos (mem_Icc.mp hn).2, mul_pow, sq (liouvilleSign n),
      liouvilleSign_mul_self, one_mul]
  have h := abs_primeBilinear_liouvilleTrunc_add_le hN (le_refl N) (le_refl N)
  rw [atomicWeilForm_eq_primeBilinear, hmass]
  have hge := log_le_harmonicSum N
  have hH1 := one_le_harmonicSum hN
  have := (abs_le.mp h).2
  nlinarith

/-- **Both ends of the spectrum.** On the orders `≤ N` the atomic prime form satisfies
`|P_N(x)| ≤ (log N + log 4 + 4)|x|²`; the pole vector reaches `(log N − log 8 − 4)|u|²` and the
Liouville pole vector reaches `−(log N − C_λ)|λu|²`. -/
theorem atomicWeilForm_spectrum_ends {N : ℕ} (hN : 1 ≤ N) :
    (∀ x : ℕ → ℝ, |atomicWeilForm N x| ≤ (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2) ∧
      (Real.log N - (Real.log 8 + 4)) * ∑ n ∈ Icc 1 N, poleVector n ^ 2 ≤
        atomicWeilForm N poleVector ∧
      atomicWeilForm N (liouvilleTrunc N) ≤
        -(Real.log N - flipConstant) * ∑ n ∈ Icc 1 N, liouvilleTrunc N n ^ 2 :=
  ⟨abs_atomicWeilForm_le N, atomicWeilForm_poleVector_ge N, atomicWeilForm_liouvillePole_le hN⟩

/-! ### The polar divergence flips on uniform profiles -/

/-- The Liouville-gauged step profile `λ x`. -/
theorem liouville_stepProfile {k : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ) (n : ℕ) :
    liouvilleSign n * stepProfile c M n = ∑ i, c i * liouvilleTrunc (M i) n := by
  rw [stepProfile, mul_sum]
  exact sum_congr rfl fun i _ => by rw [liouvilleTrunc]; ring

/-- **The polar divergence flips at the Liouville gauge.** For every uniform step profile on the
orders `≤ N` with all `M_i ≥ 1`, `|P_N(λx) + ℓ(x)²| ≤ C_λ Σ_{i,j} |c_i| |c_j| H_{min(M_i, M_j)}`:
the Liouville twin's prime form diverges as `−ℓ²` where `ζ`'s diverges as `+ℓ²`. -/
theorem abs_liouvilleForm_stepProfile_add_le {k : ℕ} {N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ)
    (hM : ∀ i, M i ≤ N) (hM1 : ∀ i, 1 ≤ M i) :
    |atomicWeilForm N (fun n => liouvilleSign n * stepProfile c M n) +
        polarFunctional N (stepProfile c M) ^ 2| ≤
      flipConstant * ∑ i, ∑ j, |c i| * |c j| * harmonicSum (min (M i) (M j)) := by
  have hL : ∀ y, primeBilinear N (fun n => liouvilleSign n * stepProfile c M n) y =
      ∑ i, c i * primeBilinear N (liouvilleTrunc (M i)) y := by
    intro y
    have h := primeBilinear_sum_left N c (fun i => liouvilleTrunc (M i)) y
    rw [← h]
    congr 1
    funext n
    exact liouville_stepProfile c M n
  have hexp : atomicWeilForm N (fun n => liouvilleSign n * stepProfile c M n) =
      ∑ i, ∑ j, c i * c j * primeBilinear N (liouvilleTrunc (M i)) (liouvilleTrunc (M j)) := by
    rw [atomicWeilForm_eq_primeBilinear, hL]
    refine sum_congr rfl fun i _ => ?_
    rw [primeBilinear_comm, hL, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [primeBilinear_comm]
    ring
  have hpair : ∀ i j, |primeBilinear N (liouvilleTrunc (M i)) (liouvilleTrunc (M j)) +
      harmonicSum (M i) * harmonicSum (M j)| ≤ flipConstant * harmonicSum (min (M i) (M j)) := by
    intro i j
    rcases le_total (M i) (M j) with h | h
    · rw [min_eq_left h]
      exact abs_primeBilinear_liouvilleTrunc_add_le (hM1 i) h (hM j)
    · rw [min_eq_right h, primeBilinear_comm, mul_comm]
      exact abs_primeBilinear_liouvilleTrunc_add_le (hM1 j) h (hM i)
  rw [hexp, polarFunctional_stepProfile c M hM, sq, sum_mul_sum, ← sum_add_distrib]
  simp_rw [← sum_add_distrib]
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  have hrw : c i * c j * primeBilinear N (liouvilleTrunc (M i)) (liouvilleTrunc (M j)) +
      c i * harmonicSum (M i) * (c j * harmonicSum (M j)) =
      (c i * c j) * (primeBilinear N (liouvilleTrunc (M i)) (liouvilleTrunc (M j)) +
        harmonicSum (M i) * harmonicSum (M j)) := by ring
  rw [hrw, abs_mul, abs_mul]
  calc |c i| * |c j| * |primeBilinear N (liouvilleTrunc (M i)) (liouvilleTrunc (M j)) +
        harmonicSum (M i) * harmonicSum (M j)|
      ≤ |c i| * |c j| * (flipConstant * harmonicSum (min (M i) (M j))) :=
        mul_le_mul_of_nonneg_left (hpair i j) (by positivity)
    _ = flipConstant * (|c i| * |c j| * harmonicSum (min (M i) (M j))) := by ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
