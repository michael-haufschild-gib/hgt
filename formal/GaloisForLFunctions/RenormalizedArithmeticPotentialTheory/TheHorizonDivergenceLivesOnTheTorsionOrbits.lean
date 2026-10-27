import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonCountertermIsPolar

/-!
# The horizon divergence lives on the torsion orbits

On uniform log-scale profiles the horizon divergence of Weil's prime form is polar and rank one
(`TheHorizonCountertermIsPolar`). This file shows that on arithmetic profiles it has unbounded rank:
the arithmetic factor carries an identity counterterm, as the Abel torsion germ does.

Fix a prime `p`. The `p`-adic valuation classes `{n : v_p(n) = j}`, `0 ≤ j ≤ J`, are the orbits of
`(ℤ/p^{J+1})^×` on the nonzero residues mod `p^{J+1}`; through `n ↦ e^{2πin/p^{J+1}}` the class `j` is
the torsion orbit `O_{p^{J+1−j}}` of `μ_{p^{J+1}}`. The **class pole vector** is
`w_j = u^{(M)} 𝟙_{v_p(n) = j}` (`classPole`).

* **Prime-power sums** (`sum_dvd_vonMangoldt_div_le`, `sum_divisors_dvd_vonMangoldt_le`): the atoms
  of `Λ` divisible by `p` are the powers of `p`, so `Σ_{p ∣ t} Λ(t)/t ≤ log p/(p − 1)` and
  `Σ_{t ∣ m, p ∣ t} Λ(t) ≤ v_p(m) log p`.
* **Leaving the class is cheap** (`offClassRow_le`): the Schur-weighted row of `P` at `m`, restricted
  to orders of another valuation, is at most `log p/(p − 1) + v_p(m) log p` — a change of valuation
  costs one prime power of `p`.
* **Each class is an approximate eigenvector with eigenvalue `log M`** (`classRow_self_ge`,
  `primeBilinear_classPole_self_ge`): `⟨w_j, P w_j⟩ ≥ (log M − c_j) |w_j|²`.
* **The classes decouple** (`primeBilinear_classPole_le`): for `j ≠ j'`,
  `0 ≤ ⟨w_j, P w_{j'}⟩ ≤ c′ min(|w_j|², |w_{j'}|²)`, with no factor `log M`.
* **Full rank on the arithmetic factor** (`atomicWeilForm_classCombination_ge`): every combination
  `x = Σ_{j ≤ J} a_j w_j` has `P_M(x) ≥ (log M − C_{p,J}) |x|²`.
* **The horizon counterterm has unbounded rank** (`horizonCounterterm_rank_unbounded`): for every `J`
  and every scalar `K` there is `M₀` such that for `M ≥ M₀` and every `J` linear functionals there is a
  nonzero `x` they annihilate with `P_M(x) > K |x|²`. No counterterm of rank `≤ J` plus a bounded
  scalar renormalizes the prime place at the horizon.

Together with polarity on uniform profiles, the horizon counterterm has the shape of a tensor
product: the identity on the arithmetic factor (the torsion orbits, as for the Abel torsion germ)
times the polar projection on the log-scale factor (as for the archimedean lattice germ). Under both
regulators the divergence of the prime place lives on the torsion orbits.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

variable {p : ℕ}

/-! ### Prime-power sums -/

theorem pos_of_mem_Icc' {n M : ℕ} (h : n ∈ Icc 1 M) : 0 < n := (mem_Icc.mp h).1

/-- A von Mangoldt atom divisible by `p` is a power of `p`. -/
theorem eq_pow_of_dvd_of_vonMangoldt_ne_zero (hp : p.Prime) {t : ℕ} (hpt : p ∣ t)
    (hΛ : Λ t ≠ 0) : ∃ k, 1 ≤ k ∧ t = p ^ k := by
  obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff t).mp (vonMangoldt_ne_zero_iff.mp hΛ)
  have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpt)
  exact ⟨k, hk, by rw [hpq]⟩

theorem vonMangoldt_prime_pow (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) : Λ (p ^ k) = Real.log p := by
  rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]

/-- **The `p`-atoms of `Λ(t)/t`**: `Σ_{t ∈ T, p ∣ t} Λ(t)/t ≤ log p/(p − 1)` for every finite `T`. -/
theorem sum_dvd_vonMangoldt_div_le (hp : p.Prime) (T : Finset ℕ) :
    ∑ t ∈ T, (if p ∣ t then Λ t / t else 0) ≤ Real.log p / ((p : ℝ) - 1) := by
  set B := T.sup id
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1.le
  have hnn : ∀ (t : ℕ) (s : Finset ℕ),
      0 ≤ ∑ k ∈ s, (if t = p ^ (k + 1) then Real.log p / (p : ℝ) ^ (k + 1) else 0) :=
    fun t s => sum_nonneg fun k _ => by split_ifs <;> positivity
  -- each term is dominated by the matching term of the geometric series
  have hterm : ∀ t ∈ T, (if p ∣ t then Λ t / t else 0) ≤
      ∑ k ∈ range B, (if t = p ^ (k + 1) then Real.log p / (p : ℝ) ^ (k + 1) else 0) := by
    intro t ht
    split_ifs with hpt
    · by_cases hΛ : Λ t = 0
      · rw [hΛ, zero_div]; exact hnn t _
      · obtain ⟨k, hk, rfl⟩ := eq_pow_of_dvd_of_vonMangoldt_ne_zero hp hpt hΛ
        have hkB : k - 1 ∈ range B := by
          rw [mem_range]
          have h1 : k < p ^ k := Nat.lt_pow_self hp.one_lt
          have h2 : p ^ k ≤ B := le_sup (f := id) ht
          omega
        have hk1 : k - 1 + 1 = k := by omega
        rw [← sum_erase_add _ _ hkB, hk1, if_pos rfl, vonMangoldt_prime_pow hp hk, Nat.cast_pow]
        linarith [hnn (p ^ k) ((range B).erase (k - 1))]
    · exact hnn t _
  calc ∑ t ∈ T, (if p ∣ t then Λ t / t else 0)
      ≤ ∑ t ∈ T, ∑ k ∈ range B, (if t = p ^ (k + 1) then Real.log p / (p : ℝ) ^ (k + 1) else 0) :=
        sum_le_sum hterm
    _ = ∑ k ∈ range B, ∑ t ∈ T, (if t = p ^ (k + 1) then Real.log p / (p : ℝ) ^ (k + 1) else 0) :=
        sum_comm
    _ ≤ ∑ k ∈ range B, Real.log p / (p : ℝ) ^ (k + 1) := by
        refine sum_le_sum fun k _ => ?_
        rw [sum_ite_eq']
        split_ifs
        · exact le_rfl
        · positivity
    _ = Real.log p / p * ∑ k ∈ range B, (1 / (p : ℝ)) ^ k := by
        rw [mul_sum]
        refine sum_congr rfl fun k _ => ?_
        rw [div_pow, one_pow, pow_succ]
        field_simp
    _ ≤ Real.log p / p * (1 - 1 / (p : ℝ))⁻¹ := by
        have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
        have hr1 : (1 : ℝ) / p < 1 := by rw [div_lt_one hp0]; exact hp1
        have hg := (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum (range B)
          (fun k _ => by positivity)
        rw [tsum_geometric_of_lt_one hr0 hr1] at hg
        exact mul_le_mul_of_nonneg_left hg (by positivity)
    _ = Real.log p / ((p : ℝ) - 1) := by
        have : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp

/-- **The `p`-atoms dividing `m`**: `Σ_{t ∣ m, p ∣ t} Λ(t) ≤ v_p(m) log p`. -/
theorem sum_divisors_dvd_vonMangoldt_le (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) :
    ∑ t ∈ m.divisors, (if p ∣ t then Λ t else 0) ≤ m.factorization p * Real.log p := by
  set v := m.factorization p
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hnn : ∀ (t : ℕ) (s : Finset ℕ),
      0 ≤ ∑ k ∈ s, (if t = p ^ (k + 1) then Real.log p else 0) :=
    fun t s => sum_nonneg fun k _ => by split_ifs <;> positivity
  have hterm : ∀ t ∈ m.divisors, (if p ∣ t then Λ t else 0) ≤
      ∑ k ∈ range v, (if t = p ^ (k + 1) then Real.log p else 0) := by
    intro t ht
    split_ifs with hpt
    · by_cases hΛ : Λ t = 0
      · rw [hΛ]; exact hnn t _
      · obtain ⟨k, hk, rfl⟩ := eq_pow_of_dvd_of_vonMangoldt_ne_zero hp hpt hΛ
        have hkv : k ≤ v := (hp.pow_dvd_iff_le_factorization hm).mp (Nat.dvd_of_mem_divisors ht)
        have hkB : k - 1 ∈ range v := by rw [mem_range]; omega
        have hk1 : k - 1 + 1 = k := by omega
        rw [← sum_erase_add _ _ hkB, hk1, if_pos rfl, vonMangoldt_prime_pow hp hk]
        linarith [hnn (p ^ k) ((range v).erase (k - 1))]
    · exact hnn t _
  calc ∑ t ∈ m.divisors, (if p ∣ t then Λ t else 0)
      ≤ ∑ t ∈ m.divisors, ∑ k ∈ range v, (if t = p ^ (k + 1) then Real.log p else 0) :=
        sum_le_sum hterm
    _ = ∑ k ∈ range v, ∑ t ∈ m.divisors, (if t = p ^ (k + 1) then Real.log p else 0) := sum_comm
    _ ≤ ∑ k ∈ range v, Real.log p := by
        refine sum_le_sum fun k _ => ?_
        rw [sum_ite_eq']
        split_ifs <;> linarith
    _ = v * Real.log p := by rw [sum_const, card_range, nsmul_eq_mul]

/-! ### Leaving a valuation class -/

/-- Along a Hecke pair `m ∣ n` a change of valuation is a factor `p` of `n/m`. -/
theorem dvd_div_of_factorization_ne (hp : p.Prime) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m ∣ n) (hv : n.factorization p ≠ m.factorization p) : p ∣ n / m := by
  by_contra hpt
  apply hv
  have hq : n / m ≠ 0 := by
    intro h
    rw [Nat.div_eq_zero_iff_lt (Nat.pos_of_ne_zero hm)] at h
    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hmn) (not_le.mpr h)
  conv_lhs => rw [← Nat.mul_div_cancel' hmn]
  rw [Nat.factorization_mul hm hq, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpt,
    add_zero]

/-- The Schur-weighted row of `P` at `m` restricted to the orders `n ≤ M` of another valuation. -/
def offClassRow (p M m : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 M, (if n.factorization p ≠ m.factorization p then
    weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) else 0)

/-- **Leaving the class is cheap**: `offClassRow ≤ log p/(p − 1) + v_p(m) log p`. -/
theorem offClassRow_le (hp : p.Prime) {M m : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    offClassRow p M m ≤ Real.log p / ((p : ℝ) - 1) + m.factorization p * Real.log p := by
  have hm0 : m ≠ 0 := hm.ne'
  unfold offClassRow
  have hsplit : ∀ n ∈ Icc 1 M, (if n.factorization p ≠ m.factorization p then
      weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) else 0) ≤
      (if m ∣ n then (if p ∣ n / m then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) else 0) +
        (if n ∣ m then (if p ∣ m / n then Λ (m / n) else 0) else 0) := by
    intro n hn
    have hn0 : n ≠ 0 := (pos_of_mem_Icc' hn).ne'
    have hnn : (0 : ℝ) ≤ (if m ∣ n then (if p ∣ n / m then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0)
        else 0) := by
      split_ifs
      · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
      · exact le_rfl
      · exact le_rfl
    have hnn' : (0 : ℝ) ≤ (if n ∣ m then (if p ∣ m / n then Λ (m / n) else 0) else 0) := by
      split_ifs <;> first | exact vonMangoldt_nonneg | exact le_rfl
    by_cases hv : n.factorization p ≠ m.factorization p
    · rw [if_pos hv, weilPrimeKernel_mul_sqrt_ratio hm (Nat.pos_of_ne_zero hn0)]
      refine add_le_add ?_ ?_
      · by_cases h1 : m ∣ n ∧ m ≠ n
        · rw [if_pos h1, if_pos h1.1, if_pos (dvd_div_of_factorization_ne hp hm0 hn0 h1.1 hv)]
        · rw [if_neg h1]; exact hnn
      · by_cases h2 : n ∣ m ∧ n ≠ m
        · rw [if_pos h2, if_pos h2.1,
            if_pos (dvd_div_of_factorization_ne hp hn0 hm0 h2.1 (Ne.symm hv))]
        · rw [if_neg h2]; exact hnn'
    · rw [if_neg hv]; exact add_nonneg hnn hnn'
  calc ∑ n ∈ Icc 1 M, (if n.factorization p ≠ m.factorization p then
        weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) else 0)
      ≤ ∑ n ∈ Icc 1 M, ((if m ∣ n then (if p ∣ n / m then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0)
          else 0) + (if n ∣ m then (if p ∣ m / n then Λ (m / n) else 0) else 0)) :=
        sum_le_sum hsplit
    _ = ∑ t ∈ Icc 1 (M / m), (if p ∣ t then Λ t / t else 0) +
          ∑ t ∈ m.divisors, (if p ∣ t then Λ t else 0) := by
        rw [sum_add_distrib, ← sum_filter, filter_dvd_Icc_eq_image hm,
          sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hm h, ← sum_filter,
          filter_Icc_dvd_eq_divisors hm hmM, Nat.sum_div_divisors m
            (fun t => if p ∣ t then Λ t else 0)]
        congr 1
        exact sum_congr rfl fun t _ => by rw [Nat.mul_div_cancel_left t hm]
    _ ≤ Real.log p / ((p : ℝ) - 1) + m.factorization p * Real.log p :=
        add_le_add (sum_dvd_vonMangoldt_div_le hp _) (sum_divisors_dvd_vonMangoldt_le hp hm0)

/-! ### Class pole vectors -/

/-- The **class pole vector** `w_j = u^{(M)} 𝟙_{v_p(n) = j}`. -/
def classPole (p j M n : ℕ) : ℝ := if n.factorization p = j then truncPole M n else 0

/-- The Schur-weighted row of `P` at `m` restricted to the valuation class `j`. -/
def classRow (p j M m : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 M, (if n.factorization p = j then weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n)
    else 0)

/-- The mass `|w_j|² = Σ_{n ≤ M, v_p(n) = j} 1/n` of a class. -/
def classMass (p j M : ℕ) : ℝ := ∑ n ∈ Icc 1 M, (if n.factorization p = j then 1 / (n : ℝ) else 0)

theorem classRow_nonneg (p j M m : ℕ) : 0 ≤ classRow p j M m :=
  sum_nonneg fun n _ => by
    split_ifs
    · exact mul_nonneg (weilPrimeKernel_nonneg m n) (Real.sqrt_nonneg _)
    · exact le_rfl

theorem classMass_nonneg (p j M : ℕ) : 0 ≤ classMass p j M :=
  sum_nonneg fun n _ => by split_ifs <;> positivity

/-- **The own class carries the eigenvalue**: `classRow_{v_p(m)}(m) ≥ log M − log 8 − 4 −
log p/(p − 1) − v_p(m) log p`. -/
theorem classRow_self_ge (hp : p.Prime) {M m : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    Real.log M - (Real.log 8 + 4) - (Real.log p / ((p : ℝ) - 1) + m.factorization p * Real.log p)
      ≤ classRow p (m.factorization p) M m := by
  have hsplit : ∑ n ∈ Icc 1 M, weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) =
      classRow p (m.factorization p) M m + offClassRow p M m := by
    rw [classRow, offClassRow, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    by_cases h : n.factorization p = m.factorization p
    · rw [if_pos h, if_neg (not_not.mpr h), add_zero]
    · rw [if_neg h, if_pos h, zero_add]
  have hrow := row_ge hm hmM
  rw [← row_eq hm hmM, hsplit] at hrow
  linarith [offClassRow_le hp hm hmM]

/-- **Another class costs one prime power**: for `j ≠ v_p(m)`, `classRow_j(m) ≤ offClassRow(m)`. -/
theorem classRow_le_offClassRow {j M m : ℕ} (hj : j ≠ m.factorization p) :
    classRow p j M m ≤ offClassRow p M m := by
  refine sum_le_sum fun n _ => ?_
  by_cases h : n.factorization p = j
  · rw [if_pos h, if_pos (by rw [h]; exact hj)]
  · rw [if_neg h]
    split_ifs
    · exact mul_nonneg (weilPrimeKernel_nonneg m n) (Real.sqrt_nonneg _)
    · exact le_rfl

/-- `u_m u_n P(m, n) = P(m, n) √(m/n)/m`. -/
theorem poleVector_mul_poleVector_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    poleVector m * poleVector n * weilPrimeKernel m n =
      weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [poleVector, poleVector, Real.sqrt_div' _ hn'.le]
  have hsm : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm').ne'
  have hsn : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn').ne'
  field_simp
  ring

/-- **The class Gram through rows**: `⟨w_{j'}, P w_j⟩ = Σ_{m ≤ M, v_p(m) = j'} classRow_j(m)/m`. -/
theorem primeBilinear_classPole_eq (p j j' M : ℕ) :
    primeBilinear M (classPole p j' M) (classPole p j M) =
      ∑ m ∈ Icc 1 M, (if m.factorization p = j' then classRow p j M m / m else 0) := by
  unfold primeBilinear
  refine sum_congr rfl fun m hm => ?_
  have hm0 := pos_of_mem_Icc' hm
  have hmM := (mem_Icc.mp hm).2
  unfold classPole truncPole
  split_ifs with hj
  · rw [if_pos hmM, classRow, sum_div]
    refine sum_congr rfl fun n hn => ?_
    have hn0 := pos_of_mem_Icc' hn
    split_ifs with h1
    · rw [if_pos (mem_Icc.mp hn).2, poleVector_mul_poleVector_mul hm0 hn0]
    · simp
  · simp

theorem classMass_eq (p j M : ℕ) :
    ∑ n ∈ Icc 1 M, classPole p j M n ^ 2 = classMass p j M := by
  unfold classMass classPole truncPole
  refine sum_congr rfl fun n hn => ?_
  split_ifs with h1 h2
  · rw [poleVector_sq]
  · exact absurd (mem_Icc.mp hn).2 h2
  · simp

/-- **Each class is an approximate eigenvector with eigenvalue `log M`**:
`⟨w_j, P w_j⟩ ≥ (log M − c_j) |w_j|²`, `c_j = log 8 + 4 + log p/(p − 1) + j log p`. -/
theorem primeBilinear_classPole_self_ge (hp : p.Prime) (j M : ℕ) :
    (Real.log M - (Real.log 8 + 4 + Real.log p / ((p : ℝ) - 1) + j * Real.log p)) *
        classMass p j M ≤ primeBilinear M (classPole p j M) (classPole p j M) := by
  rw [primeBilinear_classPole_eq, classMass, mul_sum]
  refine sum_le_sum fun m hm => ?_
  have hm0 := pos_of_mem_Icc' hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  split_ifs with hj
  · have h := classRow_self_ge hp hm0 (mem_Icc.mp hm).2
    rw [hj] at h
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (by linarith) hm'.le
  · simp

/-- **The classes decouple**: for `j ≠ j'`, `⟨w_{j'}, P w_j⟩ ≤ (log p/(p − 1) + j' log p) |w_{j'}|²`. -/
theorem primeBilinear_classPole_le (hp : p.Prime) {j j' : ℕ} (hjj : j ≠ j') (M : ℕ) :
    primeBilinear M (classPole p j' M) (classPole p j M) ≤
      (Real.log p / ((p : ℝ) - 1) + j' * Real.log p) * classMass p j' M := by
  rw [primeBilinear_classPole_eq, classMass, mul_sum]
  refine sum_le_sum fun m hm => ?_
  have hm0 := pos_of_mem_Icc' hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  split_ifs with hj
  · have h1 := classRow_le_offClassRow (p := p) (j := j) (M := M) (m := m) (by rw [hj]; exact hjj)
    have h2 := offClassRow_le hp hm0 (mem_Icc.mp hm).2
    rw [hj] at h2
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (h1.trans h2) hm'.le
  · simp

theorem primeBilinear_classPole_nonneg (p j j' M : ℕ) :
    0 ≤ primeBilinear M (classPole p j' M) (classPole p j M) := by
  rw [primeBilinear_classPole_eq]
  refine sum_nonneg fun m hm => ?_
  split_ifs
  · exact div_nonneg (classRow_nonneg _ _ _ _) (Nat.cast_nonneg _)
  · exact le_rfl

theorem classMass_pos (hp : p.Prime) {j M : ℕ} (hjM : p ^ j ≤ M) : 0 < classMass p j M := by
  unfold classMass
  have hpj : 0 < p ^ j := pow_pos hp.pos j
  have hmem : p ^ j ∈ Icc 1 M := mem_Icc.mpr ⟨hpj, hjM⟩
  rw [← sum_erase_add _ _ hmem, if_pos (by rw [hp.factorization_pow]; simp)]
  have : 0 ≤ ∑ n ∈ (Icc 1 M).erase (p ^ j), (if n.factorization p = j then 1 / (n : ℝ) else 0) :=
    sum_nonneg fun n _ => by split_ifs <;> positivity
  have : (0 : ℝ) < 1 / ((p ^ j : ℕ) : ℝ) := by positivity
  linarith

/-! ### Full rank on the arithmetic factor -/

/-- The class pole vectors have disjoint supports. -/
theorem classPole_mul_eq_zero {j j' : ℕ} (h : j ≠ j') (M n : ℕ) :
    classPole p j M n * classPole p j' M n = 0 := by
  unfold classPole
  split_ifs with h1 h2
  · exact absurd (h1.symm.trans h2) h
  all_goals simp

/-- The mass of a class combination is the weighted sum of the class masses. -/
theorem sum_classCombination_sq {J : ℕ} (a : Fin (J + 1) → ℝ) (M : ℕ) :
    ∑ n ∈ Icc 1 M, (∑ j : Fin (J + 1), a j * classPole p j M n) ^ 2 =
      ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M := by
  have hpt : ∀ n, (∑ j : Fin (J + 1), a j * classPole p j M n) ^ 2 =
      ∑ j : Fin (J + 1), a j ^ 2 * classPole p j M n ^ 2 := by
    intro n
    rw [sq, sum_mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_erase_add _ _ (mem_univ j)]
    rw [sum_eq_zero fun j' hj' => by
      have hne : (j : ℕ) ≠ j' := fun h => (mem_erase.mp hj').1 (Fin.ext h).symm
      have := classPole_mul_eq_zero (p := p) hne M n
      calc a j * classPole p j M n * (a j' * classPole p j' M n)
          = a j * a j' * (classPole p j M n * classPole p j' M n) := by ring
        _ = 0 := by rw [this, mul_zero]]
    ring
  simp_rw [hpt]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_sum, classMass_eq]

/-- **Full rank on the arithmetic factor.** Every combination `x = Σ_{j ≤ J} a_j w_j` of class pole
vectors satisfies `P_M(x) ≥ (log M − C_{p,J}) |x|²`, with
`C_{p,J} = log 8 + 4 + (J + 2)(log p/(p − 1) + J log p)`. -/
theorem atomicWeilForm_classCombination_ge (hp : p.Prime) {J : ℕ} (a : Fin (J + 1) → ℝ)
    (M : ℕ) :
    (Real.log M - (Real.log 8 + 4 + (J + 2) * (Real.log p / ((p : ℝ) - 1) + J * Real.log p))) *
        ∑ n ∈ Icc 1 M, (∑ j : Fin (J + 1), a j * classPole p j M n) ^ 2 ≤
      atomicWeilForm M (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) := by
  set c' : ℝ := Real.log p / ((p : ℝ) - 1) + J * Real.log p
  set L : ℝ := Real.log M - (Real.log 8 + 4 + Real.log p / ((p : ℝ) - 1) + J * Real.log p)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1.le
  have hc'0 : 0 ≤ c' := add_nonneg (div_nonneg hlogp (by linarith)) (by positivity)
  set m : Fin (J + 1) → ℝ := fun j => classMass p j M
  set B : Fin (J + 1) → Fin (J + 1) → ℝ := fun j j' =>
    primeBilinear M (classPole p j M) (classPole p j' M)
  -- the form expands into the class Gram
  have hexp : atomicWeilForm M (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) =
      ∑ j, ∑ j', a j * a j' * B j j' := by
    have hL : ∀ y, primeBilinear M (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) y =
        ∑ j, a j * primeBilinear M (classPole p j M) y := fun y =>
      primeBilinear_sum_left M a (fun j => classPole p j M) y
    rw [atomicWeilForm_eq_primeBilinear, hL]
    refine sum_congr rfl fun j _ => ?_
    rw [primeBilinear_comm, hL, mul_sum]
    refine sum_congr rfl fun j' _ => ?_
    simp only [B]
    rw [primeBilinear_comm]
    ring
  -- termwise lower bound
  have hjJ : ∀ j : Fin (J + 1), ((j : ℕ) : ℝ) ≤ J := fun j => by exact_mod_cast Nat.lt_succ_iff.mp j.2
  have hterm : ∀ j j' : Fin (J + 1), (if j = j' then a j ^ 2 * L * m j else 0) -
      c' * ((a j ^ 2 * m j + a j' ^ 2 * m j') / 2) ≤ a j * a j' * B j j' := by
    intro j j'
    have hmj := classMass_nonneg p j M
    have hmj' := classMass_nonneg p j' M
    by_cases hjj : j = j'
    · subst hjj
      rw [if_pos rfl]
      have h := primeBilinear_classPole_self_ge hp j M
      have hL : (Real.log M - (Real.log 8 + 4 + Real.log p / ((p : ℝ) - 1) + (j : ℕ) * Real.log p))
          * m j ≥ L * m j := by
        refine mul_le_mul_of_nonneg_right ?_ hmj
        simp only [L]
        nlinarith [hjJ j]
      have : a j * a j * B j j ≥ a j ^ 2 * L * m j := by
        have := mul_le_mul_of_nonneg_left (hL.le.trans h) (sq_nonneg (a j))
        simp only [B] at this ⊢
        nlinarith [this]
      nlinarith [mul_nonneg hc'0 (add_nonneg (mul_nonneg (sq_nonneg (a j)) hmj)
        (mul_nonneg (sq_nonneg (a j)) hmj))]
    · rw [if_neg hjj, zero_sub]
      have hne : (j : ℕ) ≠ j' := fun h => hjj (Fin.ext h)
      have hB0 : 0 ≤ B j j' := primeBilinear_classPole_nonneg p j' j M
      -- `B j j' ≤ c' |w_j|²` and, by symmetry, `≤ c' |w_{j'}|²`
      have hB1 : B j j' ≤ c' * m j := by
        have h := primeBilinear_classPole_le hp (Ne.symm hne) M
        refine h.trans (mul_le_mul_of_nonneg_right ?_ hmj)
        simp only [c']
        nlinarith [hjJ j]
      have hB2 : B j j' ≤ c' * m j' := by
        have h := primeBilinear_classPole_le hp hne M
        rw [primeBilinear_comm] at h
        refine h.trans (mul_le_mul_of_nonneg_right ?_ hmj')
        simp only [c']
        nlinarith [hjJ j']
      -- `|a_j a_{j'}| B ≤ c' (a_j² m_j + a_{j'}² m_{j'})/2`
      have hab : |a j * a j'| * B j j' ≤ c' * ((a j ^ 2 * m j + a j' ^ 2 * m j') / 2) := by
        rcases le_total (m j) (m j') with hle | hle
        · calc |a j * a j'| * B j j' ≤ |a j * a j'| * (c' * m j) :=
                mul_le_mul_of_nonneg_left hB1 (abs_nonneg _)
            _ ≤ c' * ((a j ^ 2 * m j + a j' ^ 2 * m j') / 2) := by
                rw [abs_mul]
                have h2 : 2 * (|a j| * |a j'|) ≤ a j ^ 2 + a j' ^ 2 := by
                  nlinarith [sq_nonneg (|a j| - |a j'|), sq_abs (a j), sq_abs (a j')]
                nlinarith [mul_nonneg hc'0 hmj, mul_nonneg (mul_nonneg hc'0 (sq_nonneg (a j'))) (sub_nonneg.mpr hle)]
        · calc |a j * a j'| * B j j' ≤ |a j * a j'| * (c' * m j') :=
                mul_le_mul_of_nonneg_left hB2 (abs_nonneg _)
            _ ≤ c' * ((a j ^ 2 * m j + a j' ^ 2 * m j') / 2) := by
                rw [abs_mul]
                have h2 : 2 * (|a j| * |a j'|) ≤ a j ^ 2 + a j' ^ 2 := by
                  nlinarith [sq_nonneg (|a j| - |a j'|), sq_abs (a j), sq_abs (a j')]
                nlinarith [mul_nonneg hc'0 hmj', mul_nonneg (mul_nonneg hc'0 (sq_nonneg (a j))) (sub_nonneg.mpr hle)]
      have := neg_abs_le (a j * a j')
      nlinarith [abs_nonneg (a j * a j')]
  -- sum the termwise bounds
  have hsum := sum_le_sum fun j (_ : j ∈ univ) => sum_le_sum fun j' (_ : j' ∈ univ) => hterm j j'
  rw [← hexp] at hsum
  have hdiag : ∑ j : Fin (J + 1), ∑ j' : Fin (J + 1), (if j = j' then a j ^ 2 * L * m j else 0) =
      L * ∑ j, a j ^ 2 * m j := by
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by rw [sum_ite_eq]; simp; ring
  have hoff : ∑ j : Fin (J + 1), ∑ j' : Fin (J + 1), c' * ((a j ^ 2 * m j + a j' ^ 2 * m j') / 2) =
      c' * ((J + 1) * ∑ j, a j ^ 2 * m j) := by
    set X := ∑ j : Fin (J + 1), a j ^ 2 * m j
    have h1 : ∀ j : Fin (J + 1), ∑ j' : Fin (J + 1), c' * ((a j ^ 2 * m j + a j' ^ 2 * m j') / 2) =
        c' / 2 * ((J + 1) * (a j ^ 2 * m j) + X) := by
      intro j
      have h2 : ∀ j' : Fin (J + 1), c' * ((a j ^ 2 * m j + a j' ^ 2 * m j') / 2) =
          c' / 2 * (a j ^ 2 * m j) + c' / 2 * (a j' ^ 2 * m j') := fun j' => by ring
      rw [sum_congr rfl fun j' _ => h2 j', sum_add_distrib, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
      push_cast
      ring
    rw [sum_congr rfl fun j _ => h1 j, ← mul_sum, sum_add_distrib, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
    push_cast
    ring
  simp only [sum_sub_distrib] at hsum
  rw [hdiag, hoff] at hsum
  rw [sum_classCombination_sq]
  have hmass : 0 ≤ ∑ j, a j ^ 2 * m j :=
    sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (classMass_nonneg p j M)
  have hcoef : Real.log M - (Real.log 8 + 4 + (J + 2) * c') = L - c' * (J + 1) := by
    simp only [L, c']; ring
  rw [hcoef]
  nlinarith [hsum]

/-! ### The horizon counterterm has unbounded rank -/

/-- **The horizon counterterm has unbounded rank.** For every prime `p`, every `J` and every scalar
`K`, there is `M₀` such that for `M ≥ M₀` and every family of `J` linear functionals there is a vector
`x ≠ 0` they all annihilate with `P_M(x) > K |x|²`: no counterterm of rank `≤ J`, together with any
bounded scalar, renormalizes the prime place at the horizon. -/
theorem horizonCounterterm_rank_unbounded (hp : p.Prime) (J : ℕ) (K : ℝ) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ ℓ : Fin J → ((ℕ → ℝ) →ₗ[ℝ] ℝ), ∃ x : ℕ → ℝ,
      (∀ i, ℓ i x = 0) ∧ 0 < ∑ n ∈ Icc 1 M, x n ^ 2 ∧
        K * ∑ n ∈ Icc 1 M, x n ^ 2 < atomicWeilForm M x := by
  set C : ℝ := Real.log 8 + 4 + (J + 2) * (Real.log p / ((p : ℝ) - 1) + J * Real.log p)
  refine ⟨max (p ^ J) (⌈Real.exp (K + C)⌉₊ + 1), fun M hM ℓ => ?_⟩
  have hpJ : p ^ J ≤ M := (le_max_left _ _).trans hM
  have hMpos : 0 < M := (pow_pos hp.pos J).trans_le hpJ
  have hlog : K + C < Real.log M := by
    have h1 : Real.exp (K + C) < M := by
      have := Nat.le_ceil (Real.exp (K + C))
      have h2 : ((⌈Real.exp (K + C)⌉₊ + 1 : ℕ) : ℝ) ≤ M := by
        exact_mod_cast (le_max_right _ _).trans hM
      push_cast at h2
      linarith
    rw [← Real.exp_lt_exp, Real.exp_log (by exact_mod_cast hMpos)]
    exact h1
  -- `J` functionals on the `(J + 1)`-dimensional span of the classes have a common zero
  set w : Fin (J + 1) → (ℕ → ℝ) := fun j => classPole p j M
  set F : (Fin (J + 1) → ℝ) →ₗ[ℝ] (Fin J → ℝ) :=
    LinearMap.pi fun i => (ℓ i).comp (Fintype.linearCombination ℝ w)
  have hker : LinearMap.ker F ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hx : (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) =
      Fintype.linearCombination ℝ w a := by
    rw [Fintype.linearCombination_apply]
    ext n
    simp [w, Finset.sum_apply]
  refine ⟨fun n => ∑ j : Fin (J + 1), a j * classPole p j M n, fun i => ?_, ?_, ?_⟩
  · have := congrFun ((LinearMap.mem_ker).mp ha) i
    rw [hx]
    simpa [F] using this
  · rw [sum_classCombination_sq]
    obtain ⟨j₀, hj₀⟩ : ∃ j, a j ≠ 0 := by
      by_contra h
      push_neg at h
      exact ha0 (funext h)
    have hpos : 0 < a j₀ ^ 2 * classMass p j₀ M :=
      mul_pos (pow_pos (abs_pos.mpr hj₀) 2 |>.trans_eq (sq_abs _))
        (classMass_pos hp ((Nat.pow_le_pow_right hp.pos (Nat.lt_succ_iff.mp j₀.2)).trans hpJ))
    exact hpos.trans_le (single_le_sum (f := fun j => a j ^ 2 * classMass p j M)
      (fun j _ => mul_nonneg (sq_nonneg _) (classMass_nonneg p j M)) (mem_univ j₀))
  · have hge := atomicWeilForm_classCombination_ge hp a M
    rw [sum_classCombination_sq] at hge ⊢
    obtain ⟨j₀, hj₀⟩ : ∃ j, a j ≠ 0 := by
      by_contra h
      push_neg at h
      exact ha0 (funext h)
    have hpos : 0 < ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M := by
      have h1 : 0 < a j₀ ^ 2 * classMass p j₀ M :=
        mul_pos (by positivity)
          (classMass_pos hp ((Nat.pow_le_pow_right hp.pos (Nat.lt_succ_iff.mp j₀.2)).trans hpJ))
      exact h1.trans_le (single_le_sum (f := fun j => a j ^ 2 * classMass p j M)
        (fun j _ => mul_nonneg (sq_nonneg _) (classMass_nonneg p j M)) (mem_univ j₀))
    have : K * ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M <
        (Real.log M - C) * ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M :=
      mul_lt_mul_of_pos_right (by linarith) hpos
    linarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
