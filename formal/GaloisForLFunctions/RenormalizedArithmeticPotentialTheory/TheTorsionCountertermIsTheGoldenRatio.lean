import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheDeficitOfThePrimeFormIsADirichletEnergy
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheTorsionCountertermIsAtMostTwoLogarithms

/-!
# The torsion counterterm is the golden ratio

The torsion pairing on the orders `≤ N` keeps the self-intersection `c(n) = log n − Σ_{p ∣ n} log p/(p−1)`
of every orbit on its diagonal; off the diagonal it is Weil's prime form up to a bounded excess
(`TheTorsionCountertermIsAtMostTwoLogarithms`). Its counterterm is therefore the top of
`T_N = diag(log n) + P_N`. This file computes it:

  `φ log N − C₁ ≤ κ_tor(N) ≤ φ log N + C₂`,   `φ = (1 + √5)/2`,

for every `N ≥ 1`. The continuum model of `T_N` (`TheAnomalyCostsHalfALogarithm`), which treats
the atoms as uniformly distributed in `log n`, predicts `e/(e − 1) < φ`; the arithmetic of the
orders beats it.

* **The golden split** (`sum_log_mul_sq_le_golden`): `log n = Σ_{t ∣ n} Λ(t)` puts the diagonal on
  the edges, and `a² ≤ φ²(a − b)² + φ b²` (equality iff `a = φ b`) on each edge `m → mt` gives
  `Σ log n · x_n² ≤ φ² D_N(x) + φ Σ A(⌊N/m⌋) x_m²`.
* **The upper bound** (`diag_add_atomicWeilForm_le_golden`): with the ground-state identity
  `P_N + D_N = Σ (A(⌊N/n⌋) + log n) x_n²`, `T_N ≤ φ Σ (A(⌊N/n⌋) + log n) x_n² ≤ φ(log N + log 4 + 4)|x|²`.
  The two golden identities `2 − φ^{−2} = φ` and `1 + φ^{−1} = φ` make the rows proportional.
* **The golden vector** (`goldenTest`): `x_n = φ^{ω(n)}/√n`. On a coprime edge `x_{mt} = φ x_m/√t`,
  the equality case of the split. The Chebyshev identity and Mertens' theorem alone give the mean
  co-height of its weight, `E[log(N/m)] = (log N + O(1))/(1 + φ²)`, and so
  `T_N(x) ≥ (φ log N − C)|x|²` (`diag_add_atomicWeilForm_goldenTest_ge`); the non-coprime edges
  carry `O(1)` by the tame different.
* **The torsion counterterm** (`torsionCounterterm_golden`): the window `[φ log N − C₁, φ log N + C₂]`.

The extremal charges `φ^{ω(n)}` are multiplicative: each prime factor raises the charge by the golden
ratio, the fixed point of `z ↦ 1 + 1/z` that balances the self-intersection against the Hecke tower.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.ArithmeticIntersectionTheory

local notation "gφ" => Real.goldenRatio

/-! ### 1. The golden split -/

/-- `a² ≤ φ²(a − b)² + φ b²`, with defect `φ(a − φ b)²`. -/
theorem gold_amgm (a b : ℝ) : a ^ 2 ≤ gφ ^ 2 * (a - b) ^ 2 + gφ * b ^ 2 := by
  have h : gφ ^ 2 * (a - b) ^ 2 + gφ * b ^ 2 - a ^ 2 = gφ * (a - gφ * b) ^ 2 := by
    linear_combination (a ^ 2 - gφ * b ^ 2) * Real.goldenRatio_sq
  have := mul_nonneg Real.goldenRatio_pos.le (sq_nonneg (a - gφ * b))
  linarith

/-- `Σ_n log n · x_n² = Σ_{mt ≤ N} Λ(t) x_{mt}²`. -/
theorem sum_log_mul_sq_eq_edges (N : ℕ) (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 =
      ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), Λ t * x (m * t) ^ 2 := by
  rw [sum_edges_eq_sum_divisors N (fun n t => Λ t * x n ^ 2)]
  exact sum_congr rfl fun n _ => by rw [← sum_mul, vonMangoldt_sum]

/-- **The golden split of the diagonal**:
`Σ log n · x_n² ≤ φ² D_N(x) + φ Σ_m A(⌊N/m⌋) x_m²`. -/
theorem sum_log_mul_sq_le_golden (N : ℕ) (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 ≤
      gφ ^ 2 * poleDefect N x + gφ * ∑ m ∈ Icc 1 N, mertensSum (N / m) * x m ^ 2 := by
  rw [sum_log_mul_sq_eq_edges, poleDefect, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun m _ => ?_
  rw [mertensSum, sum_mul, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun t ht => ?_
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (mem_Icc.mp ht).1
  have hΛ := vonMangoldt_nonneg (n := t)
  have h := gold_amgm (x (m * t)) (x m / Real.sqrt t)
  have hb : (x m / Real.sqrt t) ^ 2 = x m ^ 2 / t := by rw [div_pow, Real.sq_sqrt ht0.le]
  rw [hb] at h
  calc Λ t * x (m * t) ^ 2
      ≤ Λ t * (gφ ^ 2 * (x (m * t) - x m / Real.sqrt t) ^ 2 + gφ * (x m ^ 2 / t)) :=
        mul_le_mul_of_nonneg_left h hΛ
    _ = gφ ^ 2 * (Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2) + gφ * (Λ t / t * x m ^ 2) := by
        ring

/-- **The golden upper bound**: `Σ log n · x_n² + P_N(x) ≤ φ Σ (A(⌊N/n⌋) + log n) x_n²`. -/
theorem diag_add_atomicWeilForm_le_golden (N : ℕ) (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 + atomicWeilForm N x ≤
      gφ * ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * x n ^ 2 := by
  have hid := atomicWeilForm_add_poleDefect N x
  have h := sum_log_mul_sq_le_golden N x
  set a := ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2
  set b := ∑ m ∈ Icc 1 N, mertensSum (N / m) * x m ^ 2
  have hab : ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * x n ^ 2 = b + a := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun n _ => by ring
  rw [hab] at hid ⊢
  have key : gφ ^ 2 * (2 * a + b - gφ * (b + a)) = a - gφ * b := by
    linear_combination (a * (1 - gφ) - b * gφ) * Real.goldenRatio_sq
  have hg2 : 0 < gφ ^ 2 := pow_pos Real.goldenRatio_pos 2
  have hD : 2 * a + b - gφ * (b + a) ≤ poleDefect N x := by
    have : gφ ^ 2 * (2 * a + b - gφ * (b + a)) ≤ gφ ^ 2 * poleDefect N x := by linarith
    exact le_of_mul_le_mul_left this hg2
  linarith

/-- **The top of `diag(log n) + P_N` is at most `φ(log N + log 4 + 4)`**, for every `N`. -/
theorem diag_add_atomicWeilForm_le_golden_log (N : ℕ) (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 + atomicWeilForm N x ≤
      gφ * (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  refine (diag_add_atomicWeilForm_le_golden N x).trans ?_
  rw [mul_sum, mul_sum]
  refine sum_le_sum fun n hn => ?_
  have hrow := mul_le_mul_of_nonneg_right (row_le (mem_Icc.mp hn).1 (mem_Icc.mp hn).2)
    (sq_nonneg (x n))
  have := mul_le_mul_of_nonneg_left hrow Real.goldenRatio_pos.le
  linarith

/-! ### 2. The golden vector -/

/-- The **golden weight** `φ^{2ω(n)}`. -/
def goldenWeight (n : ℕ) : ℝ := gφ ^ (2 * n.primeFactors.card)

/-- The **golden test vector** `x_n = φ^{ω(n)}/√n`. -/
def goldenTest (n : ℕ) : ℝ := gφ ^ n.primeFactors.card / Real.sqrt n

theorem goldenWeight_pos (n : ℕ) : 0 < goldenWeight n := pow_pos Real.goldenRatio_pos _

theorem goldenTest_sq (n : ℕ) : goldenTest n ^ 2 = goldenWeight n / n := by
  rw [goldenTest, div_pow, Real.sq_sqrt (Nat.cast_nonneg _), goldenWeight, mul_comm 2, pow_mul]

theorem primeFactors_mul_prime_pow {m p k : ℕ} (hm : m ≠ 0) (hp : p.Prime) (hk : k ≠ 0) :
    (m * p ^ k).primeFactors = insert p m.primeFactors := by
  rw [Nat.primeFactors_mul hm (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_prime_pow hk hp,
    Finset.union_comm, ← Finset.insert_eq]

/-- `ω(m p^k) = ω(m) + 1` when `p ∤ m`, `ω(m p^k) = ω(m)` when `p ∣ m`. -/
theorem card_primeFactors_mul_prime_pow {m p k : ℕ} (hm : m ≠ 0) (hp : p.Prime) (hk : k ≠ 0) :
    (m * p ^ k).primeFactors.card = m.primeFactors.card + (if p ∣ m then 0 else 1) := by
  rw [primeFactors_mul_prime_pow hm hp hk]
  by_cases h : p ∣ m
  · rw [if_pos h, add_zero, Finset.card_insert_of_mem (Nat.mem_primeFactors.mpr ⟨hp, h, hm⟩)]
  · rw [if_neg h, Finset.card_insert_of_notMem (fun h' => h (Nat.mem_primeFactors.mp h').2.1)]

/-- `m` is coprime to `p^k` iff `p ∤ m`. -/
theorem coprime_prime_pow_iff {m p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    m.Coprime (p ^ k) ↔ ¬ p ∣ m := by
  rw [Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero hk), Nat.coprime_comm,
    hp.coprime_iff_not_dvd]

/-- **The golden vector on an edge**: with `a = Λ(t) φ^{2ω(m)}/(mt)`,
`Λ(t) x_{mt}² = (φ² or 1)·a` and `(Λ(t)/√t) x_m x_{mt} = (φ or 1)·a`, as `m ⊥ t` or not. -/
theorem goldenTest_edge {m t : ℕ} (hm : 0 < m) (ht : 0 < t) :
    Λ t * goldenTest (m * t) ^ 2 =
        (if m.Coprime t then gφ ^ 2 else 1) * (Λ t * goldenWeight m / (m * t)) ∧
      Λ t / Real.sqrt t * (goldenTest m * goldenTest (m * t)) =
        (if m.Coprime t then gφ else 1) * (Λ t * goldenWeight m / (m * t)) := by
  by_cases hΛ : Λ t = 0
  · simp [hΛ]
  obtain ⟨p, k, hp, hk0, rfl⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hΛ)
  have hk : k ≠ 0 := hk0.ne'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have ht0 : (0 : ℝ) < ((p ^ k : ℕ) : ℝ) := by exact_mod_cast ht
  have hcard := card_primeFactors_mul_prime_pow hm.ne' hp hk
  have hsm : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm0.le
  have hst : Real.sqrt ((p ^ k : ℕ) : ℝ) ^ 2 = ((p ^ k : ℕ) : ℝ) := Real.sq_sqrt ht0.le
  have hsm0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hst0 : 0 < Real.sqrt ((p ^ k : ℕ) : ℝ) := Real.sqrt_pos.mpr ht0
  have hsmt : Real.sqrt ((m * p ^ k : ℕ) : ℝ) = Real.sqrt m * Real.sqrt ((p ^ k : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Real.sqrt_mul hm0.le]
  have hmt : ((m * p ^ k : ℕ) : ℝ) = m * ((p ^ k : ℕ) : ℝ) := by push_cast; ring
  rw [goldenTest, goldenTest, goldenWeight, hcard]
  by_cases hpm : p ∣ m
  · have hnc : ¬ m.Coprime (p ^ k) := fun h => (coprime_prime_pow_iff hp hk).mp h hpm
    rw [if_neg hnc, if_neg hnc, if_pos hpm, add_zero, one_mul]
    rw [hsmt]
    constructor
    · rw [div_pow, mul_pow, hsm, hst, mul_comm 2, pow_mul]; field_simp
    · field_simp
      rw [hsm, hst, mul_comm 2 m.primeFactors.card, pow_mul]
      ring
  · have hc : m.Coprime (p ^ k) := (coprime_prime_pow_iff hp hk).mpr hpm
    rw [if_pos hc, if_pos hc, if_neg hpm]
    rw [hsmt]
    constructor
    · rw [div_pow, mul_pow, hsm, hst, ← pow_mul,
        show (m.primeFactors.card + 1) * 2 = 2 * m.primeFactors.card + 2 by ring, pow_add]
      ring
    · field_simp
      rw [hsm, hst, show 2 * m.primeFactors.card = m.primeFactors.card + m.primeFactors.card by
        ring, pow_add, pow_succ]
      ring

/-- Prime-power edges through a fixed prime: `Σ_{t ≤ X, p ∣ t} Λ(t)/t ≤ log p/(p − 1)`. -/
theorem sum_vonMangoldt_div_dvd_le {p : ℕ} (hp : p.Prime) (X : ℕ) :
    ∑ t ∈ Icc 1 X, (if p ∣ t then Λ t / t else 0) ≤ Real.log p / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set K := (Icc 1 X).filter (fun k => p ^ k ≤ X)
  have hsub : K.image (fun k => p ^ k) ⊆ (Icc 1 X).filter (fun t => p ∣ t) := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := mem_image.mp ht
    obtain ⟨hk1, hkX⟩ := mem_filter.mp hk
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos, hkX⟩,
      dvd_pow_self p (by have := (mem_Icc.mp hk1).1; omega)⟩
  have hzero : ∀ t ∈ (Icc 1 X).filter (fun t => p ∣ t), t ∉ K.image (fun k => p ^ k) →
      Λ t / t = 0 := by
    intro t ht hnot
    obtain ⟨htX, hpt⟩ := mem_filter.mp ht
    by_contra hne
    have hΛ : Λ t ≠ 0 := fun h => hne (by rw [h, zero_div])
    obtain ⟨q, j, hq, hj, rfl⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpt)
    subst hpq
    refine hnot (mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_Icc.mpr ⟨hj, ?_⟩, (mem_Icc.mp htX).2⟩, rfl⟩)
    have := Nat.lt_pow_self (n := j) hp.one_lt
    have := (mem_Icc.mp htX).2
    omega
  rw [← sum_filter, ← sum_subset hsub hzero,
    sum_image fun a _ b _ h => Nat.pow_right_injective hp.two_le h]
  have hterm : ∀ k ∈ K, Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) = Real.log p * (1 / (p : ℝ)) ^ k := by
    intro k hk
    have hk0 : k ≠ 0 := by have := (mem_Icc.mp (mem_filter.mp hk).1).1; omega
    rw [vonMangoldt_apply_pow hk0, vonMangoldt_apply_prime hp, one_div_pow, Nat.cast_pow]
    ring
  rw [sum_congr rfl hterm, ← mul_sum]
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1.le
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; exact hp1
  have hKsub : K ⊆ Ico 1 (X + 1) := fun k hk => by
    have := mem_Icc.mp (mem_filter.mp hk).1; exact mem_Ico.mpr ⟨this.1, by omega⟩
  have hgeom : ∑ k ∈ K, (1 / (p : ℝ)) ^ k ≤ 1 / ((p : ℝ) - 1) := by
    refine (sum_le_sum_of_subset_of_nonneg hKsub fun _ _ _ => by positivity).trans ?_
    refine (geom_sum_Ico_le_of_lt_one hr0 hr1).trans (le_of_eq ?_)
    field_simp
  calc Real.log p * ∑ k ∈ K, (1 / (p : ℝ)) ^ k ≤ Real.log p * (1 / ((p : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hgeom hlog
    _ = Real.log p / ((p : ℝ) - 1) := by ring

/-- **The non-coprime edges carry the tame different**:
`Σ_{t ≤ X, (m, t) > 1} Λ(t)/t ≤ Σ_{p ∣ m} log p/(p − 1)`. -/
theorem sum_noncoprime_vonMangoldt_le {m : ℕ} (hm : 0 < m) (X : ℕ) :
    ∑ t ∈ Icc 1 X, (if m.Coprime t then 0 else Λ t / t) ≤ tameDifferent m := by
  have hpt : ∀ t ∈ Icc 1 X, (if m.Coprime t then 0 else Λ t / t) ≤
      ∑ p ∈ m.primeFactors, (if p ∣ t then Λ t / t else 0) := by
    intro t _
    have hnn : 0 ≤ ∑ p ∈ m.primeFactors, (if p ∣ t then Λ t / t else 0) :=
      sum_nonneg fun p _ => by split_ifs <;> positivity
    split_ifs with hc
    · exact hnn
    by_cases hΛ : Λ t = 0
    · exact (le_of_eq (by rw [hΛ, zero_div])).trans hnn
    obtain ⟨q, j, hq, hj, rfl⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    have hqm : q ∣ m := by
      by_contra h
      exact hc (Nat.Coprime.pow_right j ((Nat.coprime_comm).mp (hq.coprime_iff_not_dvd.mpr h)))
    have hmem : q ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqm, hm.ne'⟩
    calc Λ (q ^ j) / ((q ^ j : ℕ) : ℝ) = if q ∣ q ^ j then Λ (q ^ j) / ((q ^ j : ℕ) : ℝ) else 0 := by
          rw [if_pos (dvd_pow_self q hj.ne')]
      _ ≤ _ := single_le_sum (f := fun p => if p ∣ q ^ j then Λ (q ^ j) / ((q ^ j : ℕ) : ℝ) else 0)
          (fun p _ => by split_ifs <;> positivity) hmem
  calc ∑ t ∈ Icc 1 X, (if m.Coprime t then 0 else Λ t / t)
      ≤ ∑ t ∈ Icc 1 X, ∑ p ∈ m.primeFactors, (if p ∣ t then Λ t / t else 0) := sum_le_sum hpt
    _ = ∑ p ∈ m.primeFactors, ∑ t ∈ Icc 1 X, (if p ∣ t then Λ t / t else 0) := sum_comm
    _ ≤ ∑ p ∈ m.primeFactors, Real.log p / ((p : ℝ) - 1) :=
        sum_le_sum fun p hp => sum_vonMangoldt_div_dvd_le (Nat.prime_of_mem_primeFactors hp) X
    _ = tameDifferent m := rfl

/-- The multiples of `p` carry at most `φ²/(p − 1)` of the golden mass:
`Σ_{m ≤ N, p ∣ m} φ^{2ω(m)}/m ≤ (φ²/(p − 1)) Σ_{m ≤ N} φ^{2ω(m)}/m`. -/
theorem sum_goldenWeight_dvd_le {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ∑ m ∈ (Icc 1 N).filter (fun m => p ∣ m), goldenWeight m / m ≤
      gφ ^ 2 / ((p : ℝ) - 1) * ∑ m ∈ Icc 1 N, goldenWeight m / m := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; exact hp1
  rw [sum_filter, sum_Icc_eq_sum_ladders hp N]
  have hladder : ∀ u ∈ (Icc 1 N).filter (fun u => ¬ p ∣ u),
      ∑ j ∈ range (N + 1), (if u * p ^ j ≤ N then
        (if p ∣ u * p ^ j then goldenWeight (u * p ^ j) / ((u * p ^ j : ℕ) : ℝ) else 0) else 0) ≤
      gφ ^ 2 / ((p : ℝ) - 1) * (goldenWeight u / u) := by
    intro u hu
    obtain ⟨hu1, hpu⟩ := mem_filter.mp hu
    have hu0 : 0 < u := (mem_Icc.mp hu1).1
    have hu0' : (0 : ℝ) < u := by exact_mod_cast hu0
    have hterm : ∀ j ∈ range (N + 1), (if u * p ^ j ≤ N then
        (if p ∣ u * p ^ j then goldenWeight (u * p ^ j) / ((u * p ^ j : ℕ) : ℝ) else 0) else 0) ≤
        if j = 0 then 0 else gφ ^ 2 * (goldenWeight u / u) * (1 / (p : ℝ)) ^ j := by
      intro j _
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [pow_zero, mul_one, if_neg hpu, ite_self, if_pos rfl]
      rw [if_neg hj.ne']
      have hdvd : p ∣ u * p ^ j := Dvd.dvd.mul_left (dvd_pow_self p hj.ne') u
      have hG : goldenWeight (u * p ^ j) = gφ ^ 2 * goldenWeight u := by
        rw [goldenWeight, goldenWeight, card_primeFactors_mul_prime_pow hu0.ne' hp hj.ne',
          if_neg hpu, mul_add, mul_one, pow_add]
        ring
      have hval : goldenWeight (u * p ^ j) / ((u * p ^ j : ℕ) : ℝ) =
          gφ ^ 2 * (goldenWeight u / u) * (1 / (p : ℝ)) ^ j := by
        rw [hG]; push_cast; field_simp
        rw [mul_assoc, ← mul_pow, mul_one_div_cancel (ne_of_gt (by linarith)), one_pow, mul_one]
      have hnn : 0 ≤ gφ ^ 2 * (goldenWeight u / u) * (1 / (p : ℝ)) ^ j :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (div_nonneg (goldenWeight_pos u).le hu0'.le))
          (pow_nonneg hr0 _)
      split_ifs <;> first | rw [hval] | exact hnn
    have hc0 : 0 ≤ gφ ^ 2 * (goldenWeight u / u) :=
      mul_nonneg (sq_nonneg _) (div_nonneg (goldenWeight_pos u).le hu0'.le)
    have hgeom : ∑ j ∈ range N, (1 / (p : ℝ)) ^ j ≤ 1 / (1 - 1 / (p : ℝ)) := by
      have := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hr0 hr1
      rwa [← range_eq_Ico, pow_zero] at this
    calc _ ≤ ∑ j ∈ range (N + 1), (if j = 0 then 0 else
          gφ ^ 2 * (goldenWeight u / u) * (1 / (p : ℝ)) ^ j) := sum_le_sum hterm
      _ = gφ ^ 2 * (goldenWeight u / u) * (1 / (p : ℝ)) * ∑ j ∈ range N, (1 / (p : ℝ)) ^ j := by
          rw [sum_range_succ', if_pos rfl, add_zero, mul_sum]
          exact sum_congr rfl fun j _ => by rw [if_neg (Nat.succ_ne_zero j), pow_succ]; ring
      _ ≤ gφ ^ 2 * (goldenWeight u / u) * (1 / (p : ℝ)) * (1 / (1 - 1 / (p : ℝ))) :=
          mul_le_mul_of_nonneg_left hgeom (mul_nonneg hc0 hr0)
      _ = gφ ^ 2 / ((p : ℝ) - 1) * (goldenWeight u / u) := by
          have hp0 : (p : ℝ) ≠ 0 := by linarith
          have hp10 : (p : ℝ) - 1 ≠ 0 := by linarith
          field_simp
  refine (sum_le_sum hladder).trans ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by have := hp1; positivity)
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun u _ _ => by
    have := goldenWeight_pos u; positivity

/-- **The tame different on average under the golden weight**:
`Σ_{m ≤ N} φ^{2ω(m)} d(m)/m ≤ 2φ² K Σ_{m ≤ N} φ^{2ω(m)}/m`, `K` the tame constant. -/
theorem sum_goldenWeight_tame_le (N : ℕ) :
    ∑ m ∈ Icc 1 N, goldenWeight m / m * tameDifferent m ≤
      gφ ^ 2 * (2 * tameConstant) * ∑ m ∈ Icc 1 N, goldenWeight m / m := by
  set S := ∑ m ∈ Icc 1 N, goldenWeight m / m
  have hS : 0 ≤ S := sum_nonneg fun m _ => by have := goldenWeight_pos m; positivity
  have hswap : ∑ m ∈ Icc 1 N, goldenWeight m / m * tameDifferent m =
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) *
        ∑ m ∈ (Icc 1 N).filter (p ∣ ·), goldenWeight m / m := by
    have h1 : ∑ m ∈ Icc 1 N, goldenWeight m / m * tameDifferent m =
        ∑ m ∈ Icc 1 N, ∑ p ∈ m.primeFactors,
          Real.log p / ((p : ℝ) - 1) * (goldenWeight m / m) := by
      refine sum_congr rfl fun m _ => ?_
      rw [tameDifferent, mul_sum]
      exact sum_congr rfl fun p _ => by ring
    simp only [h1, mul_sum]
    refine sum_comm' fun m p => ?_
    simp only [mem_Icc, mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp, hpm, -⟩
      exact ⟨⟨⟨h1, h2⟩, hpm⟩, ⟨hp.one_lt.le, (Nat.le_of_dvd h1 hpm).trans h2⟩, hp⟩
    · rintro ⟨⟨⟨h1, h2⟩, hpm⟩, -, hp⟩
      exact ⟨⟨h1, h2⟩, hp, hpm, by omega⟩
  rw [hswap]
  have hterm : ∀ p ∈ (Icc 1 N).filter Nat.Prime,
      Real.log p / ((p : ℝ) - 1) * ∑ m ∈ (Icc 1 N).filter (p ∣ ·), goldenWeight m / m ≤
        gφ ^ 2 * (2 * (4 * ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹)) * S := by
    intro p hp
    have hpr := (mem_filter.mp hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpr.one_lt
    have hlog : 0 ≤ Real.log p / ((p : ℝ) - 1) :=
      div_nonneg (Real.log_nonneg hp1.le) (by linarith)
    have hinner := sum_goldenWeight_dvd_le hpr N
    have htame := log_div_mul_le hpr.two_le
    -- `log p/(p − 1)² ≤ 2 log p/((p − 1) p)`
    have hratio : Real.log p / ((p : ℝ) - 1) * (1 / ((p : ℝ) - 1)) ≤
        2 * (Real.log p / ((p : ℝ) - 1) / p) := by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
      have hq0 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have e1 : Real.log p / ((p : ℝ) - 1) * (1 / ((p : ℝ) - 1)) =
          Real.log p * (1 / (((p : ℝ) - 1) * ((p : ℝ) - 1))) := by field_simp
      have e2 : 2 * (Real.log p / ((p : ℝ) - 1) / p) =
          Real.log p * (2 / (((p : ℝ) - 1) * p)) := by field_simp
      rw [e1, e2]
      refine mul_le_mul_of_nonneg_left ?_ (Real.log_nonneg hp1.le)
      rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
      nlinarith
    calc Real.log p / ((p : ℝ) - 1) * ∑ m ∈ (Icc 1 N).filter (p ∣ ·), goldenWeight m / m
        ≤ Real.log p / ((p : ℝ) - 1) * (gφ ^ 2 / ((p : ℝ) - 1) * S) :=
          mul_le_mul_of_nonneg_left hinner hlog
      _ = gφ ^ 2 * (Real.log p / ((p : ℝ) - 1) * (1 / ((p : ℝ) - 1))) * S := by ring
      _ ≤ gφ ^ 2 * (2 * (4 * ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹)) * S := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hS
          linarith
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_mul, ← mul_sum, ← mul_sum]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left ?_ (by norm_num)) (by positivity)) hS
  exact summable_tame.sum_le_tsum _ fun n _ => by positivity

/-- **The golden lower bound**: for every `N ≥ 1`,
`T_N(x) ≥ (φ(log N − log 2 − log 4 − 4) − 2φ²K)|x|²` at the golden vector. -/
theorem diag_add_atomicWeilForm_goldenTest_ge {N : ℕ} (hN : 1 ≤ N) :
    (gφ * (Real.log N - (Real.log 2 + (Real.log 4 + 4))) - gφ ^ 2 * (2 * tameConstant)) *
        ∑ n ∈ Icc 1 N, goldenTest n ^ 2 ≤
      ∑ n ∈ Icc 1 N, Real.log n * goldenTest n ^ 2 + atomicWeilForm N goldenTest := by
  set x := goldenTest
  set a : ℕ → ℕ → ℝ := fun m t => Λ t * goldenWeight m / (m * t)
  set U := ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), (if m.Coprime t then a m t else 0)
  set W := ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), (if m.Coprime t then 0 else a m t)
  set S := ∑ m ∈ Icc 1 N, goldenWeight m / m
  set J := ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2
  set K' := Real.log 2 + (Real.log 4 + 4)
  have hxS : ∑ n ∈ Icc 1 N, x n ^ 2 = S := sum_congr rfl fun n _ => goldenTest_sq n
  have hedge : ∀ m ∈ Icc 1 N, ∀ t ∈ Icc 1 (N / m), Λ t * x (m * t) ^ 2 =
      (if m.Coprime t then gφ ^ 2 else 1) * a m t ∧
      Λ t / Real.sqrt t * (x m * x (m * t)) = (if m.Coprime t then gφ else 1) * a m t :=
    fun m hm t ht => goldenTest_edge (mem_Icc.mp hm).1 (mem_Icc.mp ht).1
  -- `J = φ² U + W`
  have hJ : J = gφ ^ 2 * U + W := by
    rw [show J = ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), Λ t * x (m * t) ^ 2 from
      sum_log_mul_sq_eq_edges N x, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun m hm => ?_
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun t ht => ?_
    rw [(hedge m hm t ht).1]
    split_ifs <;> ring
  -- `P_N(x) = 2(φ U + W)`
  have hP : atomicWeilForm N x = 2 * (gφ * U + W) := by
    rw [atomicWeilForm_eq_edges]
    congr 1
    simp only [U, W]
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun m hm => ?_
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun t ht => ?_
    rw [(hedge m hm t ht).2]
    split_ifs <;> ring
  -- the total edge mass `U + W = Σ_m (φ^{2ω(m)}/m) A(⌊N/m⌋) ≥ (log N − K') S − J`
  have htot : (Real.log N - K') * S - J ≤ U + W := by
    have hUW : U + W = ∑ m ∈ Icc 1 N, goldenWeight m / m * mertensSum (N / m) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun m hm => ?_
      rw [← sum_add_distrib, mertensSum, mul_sum]
      refine sum_congr rfl fun t ht => ?_
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
      have ht0 : (0 : ℝ) < t := by exact_mod_cast (mem_Icc.mp ht).1
      have : (if m.Coprime t then a m t else 0) + (if m.Coprime t then 0 else a m t) =
          a m t := by split_ifs <;> ring
      rw [this]
      simp only [a]
      field_simp
    have hJ' : J = ∑ m ∈ Icc 1 N, goldenWeight m / m * Real.log m :=
      sum_congr rfl fun m _ => by rw [goldenTest_sq]; ring
    have hrow : ∀ m ∈ Icc 1 N, goldenWeight m / m * (Real.log N - K') -
        goldenWeight m / m * Real.log m ≤ goldenWeight m / m * mertensSum (N / m) := by
      intro m hm
      obtain ⟨hm1, hmN⟩ := mem_Icc.mp hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
      have hq : 1 ≤ N / m := (Nat.le_div_iff_mul_le hm1).mpr (by linarith)
      have hq0 : (0 : ℝ) < ((N / m : ℕ) : ℝ) := by exact_mod_cast hq
      have hmert := (abs_le.mp (RHTower.Mertens.mertens_first (N / m) hq)).1
      -- `N ≤ 2 m ⌊N/m⌋`
      have hN2 : (N : ℝ) ≤ 2 * m * ((N / m : ℕ) : ℝ) := by
        have h1 := Nat.lt_div_mul_add (a := N) hm1
        have h2 : N ≤ 2 * m * (N / m) := by nlinarith
        exact_mod_cast h2
      have hlog : Real.log N ≤ Real.log 2 + Real.log m + Real.log ((N / m : ℕ) : ℝ) := by
        rw [← Real.log_mul (by norm_num) hm0.ne', ← Real.log_mul (by positivity) hq0.ne']
        exact Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) hN2
      have hG : 0 ≤ goldenWeight m / m := by have := goldenWeight_pos m; positivity
      have hA : Real.log N - K' - Real.log m ≤ mertensSum (N / m) := by
        simp only [mertensSum]; simp only [K']; linarith
      nlinarith [mul_le_mul_of_nonneg_left hA hG]
    rw [hUW, hJ']
    have := sum_le_sum hrow
    rw [sum_sub_distrib, ← sum_mul] at this
    linarith
  -- the non-coprime edges carry `O(1)` of the mass
  have hW : W ≤ gφ ^ 2 * (2 * tameConstant) * S := by
    refine le_trans ?_ (sum_goldenWeight_tame_le N)
    refine sum_le_sum fun m hm => ?_
    have hm0 : 0 < m := (mem_Icc.mp hm).1
    have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
    have hG : 0 ≤ goldenWeight m / m := by have := goldenWeight_pos m; positivity
    have h := mul_le_mul_of_nonneg_left (sum_noncoprime_vonMangoldt_le hm0 (N / m)) hG
    calc ∑ t ∈ Icc 1 (N / m), (if m.Coprime t then 0 else a m t)
        = goldenWeight m / m * ∑ t ∈ Icc 1 (N / m), (if m.Coprime t then 0 else Λ t / t) := by
          rw [mul_sum]
          refine sum_congr rfl fun t ht => ?_
          have ht0 : (0 : ℝ) < t := by exact_mod_cast (mem_Icc.mp ht).1
          split_ifs
          · ring
          · simp only [a]; field_simp
      _ ≤ _ := h
  have hW0 : 0 ≤ W := sum_nonneg fun m hm => sum_nonneg fun t ht => by
    split_ifs
    · exact le_rfl
    · simp only [a]
      have := goldenWeight_pos m
      have : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
      have : (0 : ℝ) < t := by exact_mod_cast (mem_Icc.mp ht).1
      have := vonMangoldt_nonneg (n := t)
      positivity
  -- the golden algebra
  have hφ0 := Real.goldenRatio_pos
  have hφ2 := Real.goldenRatio_lt_two
  have hcomb : (Real.log N - K') * S ≤ (1 + gφ ^ 2) * U + 2 * W := by linarith
  have h1 := mul_le_mul_of_nonneg_left hcomb hφ0.le
  have e1 : gφ * ((1 + gφ ^ 2) * U) = (gφ ^ 2 + 2 * gφ) * U := by
    linear_combination (gφ * U) * Real.goldenRatio_sq
  have h2 : gφ * W ≤ 2 * W := mul_le_mul_of_nonneg_right hφ2.le hW0
  rw [hxS, hP]
  simp only [J] at hJ
  linarith

/-! ### 3. The torsion counterterm -/

theorem goldenTest_eq (n : ℕ) : goldenTest n = gφ ^ n.primeFactors.card * poleVector n := by
  rw [goldenTest, poleVector]; ring

/-- **The torsion counterterm is the golden ratio.** For every `N ≥ 1`,
`κ = φ(log N + log 4 + 4) + 2C_e` renormalizes the torsion pairing on the orders `≤ N`, and every
renormalizing `κ` is at least `φ(log N − log 2 − log 4 − 4) − 4φ²K`: `κ_tor(N) = φ log N + O(1)`. -/
theorem torsionCounterterm_golden {N : ℕ} (hN : 1 ≤ N) :
    RenormalizesAt N (gφ * (Real.log N + (Real.log 4 + 4)) + 2 * excessConstant) ∧
      ∀ κ, RenormalizesAt N κ →
        gφ * (Real.log N - (Real.log 2 + (Real.log 4 + 4))) - gφ ^ 2 * (4 * tameConstant) ≤ κ := by
  constructor
  · -- the upper bound: the diagonal `c(n) ≤ log n`, Weil's kernel, the excess
    intro y
    set z := normalizedCharge y
    set S := Icc 1 N
    have hpt : ∀ m ∈ S, ∀ n ∈ S, y m * y n * orbitIntersection m n ≤
        (if m = n then Real.log m * z m ^ 2 else 0) + z m * z n * weilPrimeKernel m n +
          (z m ^ 2 + z n ^ 2) / 2 * (upExcess m n + upExcess n m) := by
      intro m hm n hn
      have hm0 := (mem_Icc.mp hm).1
      by_cases hmn : m = n
      · subst hmn
        simp only [↓reduceIte, weilPrimeKernel_self, upExcess_self hm0, mul_zero, add_zero]
        rw [normalizedCharge_sq]
        have hI := orbitIntersection_self_le hm0
        nlinarith [mul_le_mul_of_nonneg_left hI (sq_nonneg (y m))]
      · rw [if_neg hmn, zero_add]
        exact offDiag_le y hm0 (mem_Icc.mp hn).1 hmn
    have hdiag : ∑ m ∈ S, ∑ n ∈ S, (if m = n then Real.log m * z m ^ 2 else 0) =
        ∑ n ∈ S, Real.log n * z n ^ 2 :=
      sum_congr rfl fun m hm => by rw [sum_ite_eq, if_pos hm]
    have hT := diag_add_atomicWeilForm_le_golden_log N z
    have hE := sum_excess_le N z
    rw [torsionPairing, selfMass_eq]
    refine (sum_le_sum fun m hm => sum_le_sum fun n hn => hpt m hm n hn).trans ?_
    simp only [sum_add_distrib]
    rw [hdiag]
    unfold atomicWeilForm at hT
    linarith
  · -- the lower bound: the golden charges `y_n = φ^{ω(n)} (n φ(n))^{−1/2}`
    intro κ hκ
    have hφ0 := Real.goldenRatio_pos
    set y : ℕ → ℝ := fun n => gφ ^ n.primeFactors.card * torsionTest n
    set S := ∑ n ∈ Icc 1 N, goldenTest n ^ 2
    have hmass : selfMass N y = S := by
      unfold selfMass
      refine sum_congr rfl fun n hn => ?_
      have hn0 := (mem_Icc.mp hn).1
      have hφ : (0 : ℝ) < Nat.totient n := by exact_mod_cast Nat.totient_pos.mpr hn0
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
      simp only [y]
      rw [mul_pow, torsionTest_sq hn0, goldenTest_sq, goldenWeight, mul_comm 2, pow_mul]
      field_simp
    -- the pairing dominates the golden diagonal and Weil's form
    have hpair : ∑ n ∈ Icc 1 N, goldenWeight n / n * selfIntersection n +
        atomicWeilForm N goldenTest ≤ torsionPairing N y := by
      have hdiag : ∑ n ∈ Icc 1 N, goldenWeight n / n * selfIntersection n =
          ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
            (if m = n then goldenWeight n / n * selfIntersection n else 0) :=
        sum_congr rfl fun m hm => by rw [sum_ite_eq, if_pos hm]
      rw [hdiag, atomicWeilForm, ← sum_add_distrib, torsionPairing]
      refine sum_le_sum fun m hm => ?_
      rw [← sum_add_distrib]
      refine sum_le_sum fun n hn => ?_
      have hm0 := (mem_Icc.mp hm).1
      have hn0 := (mem_Icc.mp hn).1
      by_cases hmn : m = n
      · subst hmn
        rw [if_pos rfl, weilPrimeKernel_self, mul_zero, add_zero]
        simp only [y]
        have h := torsionTest_diag hm0
        rw [goldenWeight, mul_comm 2, pow_mul]
        have : gφ ^ m.primeFactors.card * torsionTest m *
            (gφ ^ m.primeFactors.card * torsionTest m) * orbitIntersection m m =
            (gφ ^ m.primeFactors.card) ^ 2 *
              (torsionTest m * torsionTest m * orbitIntersection m m) := by ring
        rw [this, h]; ring_nf; exact le_rfl
      · rw [if_neg hmn, zero_add]
        simp only [y]
        have hk := poleVector_mul_kernel_le hm0 hn0 hmn
        have hw : 0 ≤ gφ ^ m.primeFactors.card * gφ ^ n.primeFactors.card :=
          mul_nonneg (pow_nonneg hφ0.le _) (pow_nonneg hφ0.le _)
        rw [goldenTest_eq, goldenTest_eq]
        nlinarith [mul_le_mul_of_nonneg_left hk hw]
    have hc : ∑ n ∈ Icc 1 N, goldenWeight n / n * selfIntersection n =
        ∑ n ∈ Icc 1 N, Real.log n * goldenTest n ^ 2 -
          ∑ n ∈ Icc 1 N, goldenWeight n / n * tameDifferent n := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun n hn => ?_
      rw [selfIntersection_eq (mem_Icc.mp hn).1, goldenTest_sq]
      ring
    have hlow := diag_add_atomicWeilForm_goldenTest_ge hN
    have htame := sum_goldenWeight_tame_le N
    have hSeq : ∑ m ∈ Icc 1 N, goldenWeight m / m = S :=
      sum_congr rfl fun n _ => (goldenTest_sq n).symm
    rw [hSeq] at htame
    have hup := hκ y
    rw [hmass] at hup
    -- `S ≥ 1` from the atom `n = 1`
    have hS1 : 1 ≤ S := by
      have h1 : (1 : ℝ) = goldenTest 1 ^ 2 := by
        rw [goldenTest_sq, goldenWeight]; simp
      rw [h1]
      exact single_le_sum (f := fun n => goldenTest n ^ 2) (fun n _ => sq_nonneg _)
        (mem_Icc.mpr ⟨le_rfl, hN⟩)
    have hfin : (gφ * (Real.log N - (Real.log 2 + (Real.log 4 + 4))) -
        gφ ^ 2 * (4 * tameConstant)) * S ≤ κ * S := by
      rw [hc] at hpair
      nlinarith
    exact le_of_mul_le_mul_right hfin (by linarith)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
