import GaloisForLFunctions.TransHorizonIncidenceMechanics.IntegerJumpEnergyAndBeyondEnvelopeDefect
import GaloisForLFunctions.TransHorizonIncidenceMechanics.HorizonRadicalStateAndDefectNormalForm
import GaloisForLFunctions.BezoutValuationIncidence.QuotientDualOctaveReciprocityAndValuationSwitching
import GaloisForLFunctions.TransHorizonIncidenceMechanics.RoughPrimeBoundaryUniformDampingDefectSign

/-!
# The Möbius envelope ladder and prime-shell responses

Beyond its horizon a squarefree Möbius response is a truncated Möbius divisor sum of the
radical: for squarefree `r ≥ 2`,

`s_{N,μ}(r) = -μ(r) Σ_{q ∣ r, q(N+1) ≤ r} μ(q)`,

so only the divisors `q ≤ r/(N+1)` (the radical ratio) are seen, and `|s_{N,μ}(r)| ≤ r/(N+1)`.

* **Second and third rungs.** Every truncated Möbius divisor sum below `11` has magnitude at most
  two (the only positive channels `6, 10` need the negative channels `2, 3, 5`; the channel `7`
  only opens after `6`), and below `13` at most three. Hence `|s_{N,μ}(k)| ≤ 2` whenever the
  radical state of `k` is below `11(N+1)` and `≤ 3` below `13(N+1)`, at every horizon. Both
  ratios are exact: the prime-shell families below reach `3` at ratio `11` and `4` at ratio `13`.
* **Sign.** By integer jump energy, the Möbius renormalized defect is nonpositive whenever the
  radical state of `M+1` is below `11(N+1)`; a positive Möbius defect needs radical ratio `≥ 11`.
* **Prime shells.** If `P` is a set of primes with largest element `Q` and all pair products
  above `Q`, then for every prime `ℓ > Q` the integer `n = ℓ ∏P` read at horizon `N = n/Q - 1`
  (ratio exactly `Q`) has response `±(|P| - 1)`: its divisors below the ratio are `1` and `P`.
  The shell of primes in `(√Q, Q]` makes the response at ratio `Q` as large as
  `π(Q) - π(√Q) - 1`, so the envelope grows almost linearly in the ratio.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Squarefree responses are truncated Möbius divisor sums -/

theorem moebiusReal_div_of_squarefree {r q : ℕ} (hr : Squarefree r) (hq : q ∣ r) :
    moebiusReal (r / q) = moebiusReal r * moebiusReal q := by
  obtain ⟨t, rfl⟩ := hq
  obtain ⟨hcop, hsq, -⟩ := Nat.squarefree_mul_iff.mp hr
  have hq0 : 0 < q := Nat.pos_of_ne_zero fun h => by simp [h] at hr
  rw [Nat.mul_div_cancel_left t hq0]
  have h1 : (μ q : ℝ) ^ 2 = 1 := by
    have h' : |(μ q : ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree hsq
    rw [← sq_abs, h', one_pow]
  unfold moebiusReal
  rw [isMultiplicative_moebius.map_mul_of_coprime hcop]
  push_cast
  linear_combination (-(μ t : ℝ)) * h1

/-- **Truncated divisor form.** For squarefree `r ≥ 2`,
`s_{N,μ}(r) = -μ(r) Σ_{q ∣ r, q(N+1) ≤ r} μ(q)`. -/
theorem sieveSeq_moebiusReal_squarefree_eq (N : ℕ) {r : ℕ} (hr : Squarefree r) (hr2 : 2 ≤ r) :
    sieveSeq N moebiusReal r =
      -moebiusReal r * ∑ q ∈ r.divisors.filter (fun q => q * (N + 1) ≤ r), moebiusReal q := by
  have hset : r.divisors.filter (fun q => N < r / q) =
      r.divisors.filter (fun q => q * (N + 1) ≤ r) := by
    ext q
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hqr, hr0⟩, hlt⟩
      have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hqr (by omega)
      exact ⟨⟨hqr, hr0⟩, by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hq0).mp hlt⟩
    · rintro ⟨⟨hqr, hr0⟩, hle⟩
      have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hqr (by omega)
      exact ⟨⟨hqr, hr0⟩, (Nat.le_div_iff_mul_le hq0).mpr (by rw [mul_comm]; exact hle)⟩
  rw [sieveSeq_eq_sum_divisors_sub_complementaryQuotientTail N (by omega),
    sum_divisors_moebiusReal_eq_zero hr2, zero_sub, complementaryQuotientTail, hset, neg_mul,
    mul_sum]
  congr 1
  apply sum_congr rfl
  intro q hq
  exact moebiusReal_div_of_squarefree hr (Nat.dvd_of_mem_divisors (mem_filter.mp hq).1)

/-- The response never exceeds the radical ratio: `|s_{N,μ}(r)| ≤ r/(N+1)` for squarefree `r ≥ 2`. -/
theorem abs_sieveSeq_moebiusReal_squarefree_le_ratio (N : ℕ) {r : ℕ} (hr : Squarefree r)
    (hr2 : 2 ≤ r) : |sieveSeq N moebiusReal r| ≤ (r / (N + 1) : ℕ) := by
  rw [sieveSeq_moebiusReal_squarefree_eq N hr hr2, abs_mul, abs_neg]
  have hμr : |moebiusReal r| = 1 := by
    unfold moebiusReal; exact_mod_cast abs_moebius_eq_one_of_squarefree hr
  rw [hμr, one_mul]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hsub : r.divisors.filter (fun q => q * (N + 1) ≤ r) ⊆ Icc 1 (r / (N + 1)) := by
    intro q hq
    obtain ⟨hqd, hle⟩ := mem_filter.mp hq
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hqd, (Nat.le_div_iff_mul_le (by omega)).mpr hle⟩
  calc ∑ q ∈ r.divisors.filter (fun q => q * (N + 1) ≤ r), |moebiusReal q|
      ≤ ∑ _q ∈ r.divisors.filter (fun q => q * (N + 1) ≤ r), (1 : ℝ) :=
        sum_le_sum fun q _ => by
          unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ ≤ ∑ _q ∈ Icc 1 (r / (N + 1)), (1 : ℝ) := sum_le_sum_of_subset_of_nonneg hsub (by simp)
    _ = (r / (N + 1) : ℕ) := by simp

/-! ### The second and third rungs -/

private theorem moebius_small_values :
    moebiusReal 1 = 1 ∧ moebiusReal 2 = -1 ∧ moebiusReal 3 = -1 ∧ moebiusReal 4 = 0 ∧
      moebiusReal 5 = -1 ∧ moebiusReal 6 = 1 ∧ moebiusReal 7 = -1 ∧ moebiusReal 8 = 0 ∧
      moebiusReal 9 = 0 ∧ moebiusReal 10 = 1 ∧ moebiusReal 11 = -1 ∧ moebiusReal 12 = 0 := by
  have p2 := moebius_apply_prime Nat.prime_two
  have p3 := moebius_apply_prime Nat.prime_three
  have p5 := moebius_apply_prime Nat.prime_five
  have p7 := moebius_apply_prime (by norm_num : Nat.Prime 7)
  have p11 := moebius_apply_prime (by norm_num : Nat.Prime 11)
  have m6 : μ 6 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
      p2, p3]; rfl
  have m10 : μ 10 = 1 := by
    rw [show (10 : ℕ) = 2 * 5 by rfl, isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
      p2, p5]; rfl
  have m4 : μ 4 = 0 := by decide
  have m8 : μ 8 = 0 := by decide
  have m9 : μ 9 = 0 := by
    rw [show (9 : ℕ) = 3 ^ 2 by rfl, moebius_apply_prime_pow Nat.prime_three (by norm_num)]; rfl
  have m12 : μ 12 = 0 := by decide
  unfold moebiusReal
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [p2, p3, p5, p7, p11, m6, m10, m4, m8, m9, m12]

/-- **Rung two.** Every Möbius divisor sum truncated below `11` has magnitude at most two. -/
theorem abs_truncated_moebius_divisor_sum_le_two (r Y : ℕ) :
    |∑ q ∈ Icc 1 10, (if q ∣ r ∧ q ≤ Y then moebiusReal q else 0)| ≤ 2 := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, -, -⟩ := moebius_small_values
  have h6 : 6 ∣ r ↔ 2 ∣ r ∧ 3 ∣ r := by omega
  have h10 : 10 ∣ r ↔ 2 ∣ r ∧ 5 ∣ r := by omega
  rw [show Icc 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} by decide]
  simp only [sum_insert, mem_insert, mem_singleton, sum_singleton, m1, m2, m3, m4, m5, m6, m7, m8,
    m9, m10, h6, h10, one_dvd, true_and, ite_self, Nat.reduceEqDiff, or_self, not_false_eq_true,
    OfNat.one_ne_ofNat, zero_add]
  rcases (show Y ≤ 9 ∨ 10 ≤ Y by omega) with hY | hY
  · interval_cases Y <;> by_cases h2 : 2 ∣ r <;> by_cases h3 : 3 ∣ r <;> by_cases h5 : 5 ∣ r <;>
      by_cases h7 : 7 ∣ r <;> norm_num [h2, h3, h5, h7]
  · have : 1 ≤ Y ∧ 2 ≤ Y ∧ 3 ≤ Y ∧ 5 ≤ Y ∧ 6 ≤ Y ∧ 7 ≤ Y ∧ 10 ≤ Y := by omega
    obtain ⟨a1, a2, a3, a5, a6, a7, a10⟩ := this
    by_cases h2 : 2 ∣ r <;> by_cases h3 : 3 ∣ r <;> by_cases h5 : 5 ∣ r <;>
      by_cases h7 : 7 ∣ r <;> norm_num [h2, h3, h5, h7, a1, a2, a3, a5, a6, a7, a10]

/-- **Rung three.** Below `13` the only new channels are `11` (negative) and `12` (silent). -/
theorem abs_truncated_moebius_divisor_sum_le_three (r Y : ℕ) :
    |∑ q ∈ Icc 1 12, (if q ∣ r ∧ q ≤ Y then moebiusReal q else 0)| ≤ 3 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, m11, m12⟩ := moebius_small_values
  rw [sum_Icc_succ_top (by norm_num : 1 ≤ 11 + 1), sum_Icc_succ_top (by norm_num : 1 ≤ 10 + 1)]
  have h10 := abs_truncated_moebius_divisor_sum_le_two r Y
  have h11 : |(if 10 + 1 ∣ r ∧ 10 + 1 ≤ Y then moebiusReal (10 + 1) else 0)| ≤ 1 := by
    split_ifs <;> norm_num [m11]
  have h12 : (if 11 + 1 ∣ r ∧ 11 + 1 ≤ Y then moebiusReal (11 + 1) else 0) = 0 := by
    split_ifs <;> norm_num [m12]
  rw [h12, add_zero]
  exact (abs_add_le _ _).trans (by linarith)

/-- Below ratio `B + 1`, the truncated divisor sum only sees channels `q ≤ B`. -/
private theorem sum_filter_eq_sum_Icc_ite {N r B : ℕ} (hr0 : r ≠ 0) (hlt : r < (B + 1) * (N + 1)) :
    ∑ q ∈ r.divisors.filter (fun q => q * (N + 1) ≤ r), moebiusReal q =
      ∑ q ∈ Icc 1 B, (if q ∣ r ∧ q ≤ r / (N + 1) then moebiusReal q else 0) := by
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext q
  simp only [mem_filter, Nat.mem_divisors, mem_Icc]
  constructor
  · rintro ⟨⟨hqr, -⟩, hle⟩
    have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hqr (Nat.pos_of_ne_zero hr0)
    refine ⟨⟨hq0, ?_⟩, hqr, (Nat.le_div_iff_mul_le (by omega)).mpr hle⟩
    by_contra h
    have : (B + 1) * (N + 1) ≤ q * (N + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  · rintro ⟨-, hqr, hle⟩
    exact ⟨⟨hqr, hr0⟩, (Nat.le_div_iff_mul_le (by omega)).mp hle⟩

/-- **Envelope of magnitude two up to ratio eleven**, for every horizon. -/
theorem abs_sieveSeq_moebiusReal_le_two_of_radical_lt_eleven_succ {N k : ℕ}
    (hrN : horizonRadicalState N k < 11 * (N + 1)) :
    |sieveSeq N moebiusReal k| ≤ 2 := by
  have hsf : ∀ d : ℕ, ¬ Squarefree d → moebiusReal d = 0 := fun d hd => by
    unfold moebiusReal; rw [moebius_eq_zero_of_not_squarefree hd]; simp
  rw [← sieveSeq_horizonRadicalState N k hsf]
  set r := horizonRadicalState N k
  have hr := horizonRadicalState_squarefree N k
  have hr0 := horizonRadicalState_pos N k
  rcases (show r = 1 ∨ 2 ≤ r by omega) with h1 | h2
  · rw [h1]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [sieveSeq]
    · rw [show sieveSeq N moebiusReal 1 = 1 by
        simp [sieveSeq, Finset.sum_filter, moebiusReal,
          show Icc 1 N = insert 1 (Icc 2 N) by ext d; simp only [mem_Icc, mem_insert]; omega]]
      norm_num
  · rw [sieveSeq_moebiusReal_squarefree_eq N hr h2, abs_mul, abs_neg,
      sum_filter_eq_sum_Icc_ite (B := 10) hr0.ne' (by omega)]
    have hμr : |moebiusReal r| = 1 := by
      unfold moebiusReal; exact_mod_cast abs_moebius_eq_one_of_squarefree hr
    rw [hμr, one_mul]
    exact abs_truncated_moebius_divisor_sum_le_two r _

/-- **Envelope of magnitude three up to ratio thirteen**, for every horizon. -/
theorem abs_sieveSeq_moebiusReal_le_three_of_radical_lt_thirteen_succ {N k : ℕ}
    (hrN : horizonRadicalState N k < 13 * (N + 1)) :
    |sieveSeq N moebiusReal k| ≤ 3 := by
  have hsf : ∀ d : ℕ, ¬ Squarefree d → moebiusReal d = 0 := fun d hd => by
    unfold moebiusReal; rw [moebius_eq_zero_of_not_squarefree hd]; simp
  rw [← sieveSeq_horizonRadicalState N k hsf]
  set r := horizonRadicalState N k
  have hr := horizonRadicalState_squarefree N k
  have hr0 := horizonRadicalState_pos N k
  rcases (show r = 1 ∨ 2 ≤ r by omega) with h1 | h2
  · rw [h1]
    have : |sieveSeq N moebiusReal 1| ≤ 1 := by
      unfold sieveSeq
      rw [sum_filter]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ d ∈ Icc 1 N, |if d ∣ 1 then moebiusReal d else 0|
          ≤ ∑ d ∈ Icc 1 N, (if d = 1 then (1 : ℝ) else 0) := by
            refine sum_le_sum fun d hd => ?_
            by_cases hd1 : d = 1
            · subst hd1; simp [moebiusReal]
            · rw [if_neg (by rw [Nat.dvd_one]; exact hd1), if_neg hd1, abs_zero]
        _ ≤ 1 := by rw [sum_ite_eq']; split_ifs <;> norm_num
    linarith
  · rw [sieveSeq_moebiusReal_squarefree_eq N hr h2, abs_mul, abs_neg,
      sum_filter_eq_sum_Icc_ite (B := 12) hr0.ne' (by omega)]
    have hμr : |moebiusReal r| = 1 := by
      unfold moebiusReal; exact_mod_cast abs_moebius_eq_one_of_squarefree hr
    rw [hμr, one_mul]
    exact abs_truncated_moebius_divisor_sum_le_three r _

/-- **Defect sign up to ratio eleven.** The Möbius renormalized defect is nonpositive whenever
the radical state of `M + 1` is below `11(N+1)`, at every horizon. -/
theorem moebius_prefix_defect_nonpos_of_radical_lt_eleven_succ {N M : ℕ}
    (hrN : horizonRadicalState N (M + 1) < 11 * (N + 1)) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 :=
  moebius_prefix_defect_nonpos_of_abs_le_two (abs_sieveSeq_moebiusReal_le_two_of_radical_lt_eleven_succ hrN)

/-- A positive Möbius defect requires radical ratio at least eleven. -/
theorem moebius_positive_defect_requires_radical_ratio_eleven {N M : ℕ}
    (h : 0 < sieveRenormalizedPrefixDefect N M moebiusReal) :
    11 * (N + 1) ≤ horizonRadicalState N (M + 1) := by
  by_contra hn
  have := moebius_prefix_defect_nonpos_of_radical_lt_eleven_succ (N := N) (M := M) (by omega)
  linarith

/-! ### Prime shells -/

/-- **Prime-shell response.** Let `P` be a set of primes with largest element `Q` whose pair
products all exceed `Q`, and `ℓ > Q` a prime. Then `n = ℓ ∏P = Q(N+1)` with `N = n/Q - 1`, and
`s_{N,μ}(n) = -(-1)^{|P|} (|P| - 1)`: the divisors of `n` below the ratio are `1` and `P`. -/
theorem sieveSeq_moebiusReal_prime_shell {P : Finset ℕ} {Q ℓ : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : Q ∈ P) (hmax : ∀ p ∈ P, p ≤ Q) (hpair : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → Q < p * p')
    (hℓ : ℓ.Prime) (hQℓ : Q < ℓ) :
    ℓ * ∏ p ∈ P, p = Q * ((ℓ * ∏ p ∈ P, p) / Q - 1 + 1) ∧
      sieveSeq ((ℓ * ∏ p ∈ P, p) / Q - 1) moebiusReal (ℓ * ∏ p ∈ P, p) =
        -(-1 : ℝ) ^ P.card * ((P.card : ℝ) - 1) := by
  set n := ℓ * ∏ p ∈ P, p
  have hQp : Q.Prime := hP Q hQ
  have hℓP : ℓ ∉ P := fun h => by have := hmax ℓ h; omega
  have hsqP : Squarefree (∏ p ∈ P, p) :=
    Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp p' hp' hne =>
      Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hP p hp) (hP p' hp')).mpr hne))
      fun p hp => (hP p hp).squarefree
  have hcopℓ : Nat.Coprime ℓ (∏ p ∈ P, p) :=
    Nat.Coprime.prod_right fun p hp => (Nat.coprime_primes hℓ (hP p hp)).mpr (fun h => hℓP (h ▸ hp))
  have hn : Squarefree n := Nat.squarefree_mul_iff.mpr ⟨hcopℓ, hℓ.squarefree, hsqP⟩
  have hQdvd : Q ∣ n := dvd_mul_of_dvd_right (dvd_prod_of_mem _ hQ) ℓ
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
  have hQ0 : 0 < Q := hQp.pos
  have hNsucc : n / Q - 1 + 1 = n / Q := by
    have : Q ≤ n := Nat.le_of_dvd hn0 hQdvd
    have : 1 ≤ n / Q := (Nat.le_div_iff_mul_le hQ0).mpr (by omega)
    omega
  have hnQ : n = Q * (n / Q) := (Nat.mul_div_cancel' hQdvd).symm
  refine ⟨by rw [hNsucc]; exact hnQ, ?_⟩
  have hn2 : 2 ≤ n := by
    have : ℓ ≤ n := Nat.le_mul_of_pos_right ℓ (Finset.prod_pos fun p hp => (hP p hp).pos)
    have := hℓ.two_le; omega
  rw [sieveSeq_moebiusReal_squarefree_eq _ hn hn2, hNsucc]
  -- the divisors of `n` below the ratio `Q` are `1` and the primes of `P`
  have hset : n.divisors.filter (fun q => q * (n / Q) ≤ n) = insert 1 P := by
    ext q
    simp only [mem_filter, Nat.mem_divisors, mem_insert]
    constructor
    · rintro ⟨⟨hqn, -⟩, hle⟩
      have hpos : 0 < n / Q := Nat.div_pos (Nat.le_of_dvd hn0 hQdvd) hQ0
      have hqQ : q ≤ Q := by
        by_contra h
        have : (Q + 1) * (n / Q) ≤ q * (n / Q) := Nat.mul_le_mul_right _ (by omega)
        nlinarith
      by_cases hq1 : q = 1
      · exact Or.inl hq1
      right
      have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hqn hn0
      -- every prime factor of `q` lies in `P`
      have hfac : ∀ t, t.Prime → t ∣ q → t ∈ P := by
        intro t ht htq
        rcases (Nat.Prime.dvd_mul ht).mp (htq.trans hqn) with h | h
        · have := (Nat.prime_dvd_prime_iff_eq ht hℓ).mp h
          have := Nat.le_of_dvd hq0 htq
          omega
        · obtain ⟨p, hp, htp⟩ := (Prime.dvd_finsetProd_iff ht.prime _).mp h
          rwa [(Nat.prime_dvd_prime_iff_eq ht (hP p hp)).mp htp]
      obtain ⟨t, ht, htq⟩ := Nat.exists_prime_and_dvd hq1
      have htP := hfac t ht htq
      obtain ⟨u, rfl⟩ := htq
      by_cases hu1 : u = 1
      · rw [hu1, mul_one]; exact htP
      exfalso
      obtain ⟨t', ht', ht'u⟩ := Nat.exists_prime_and_dvd hu1
      have ht'P := hfac t' ht' (dvd_mul_of_dvd_right ht'u t)
      have hsqq : Squarefree (t * u) := hn.squarefree_of_dvd hqn
      have hne : t ≠ t' := by
        rintro rfl
        exact ht.not_isUnit (hsqq t (mul_dvd_mul_left t ht'u))
      have hu0 : 0 < u := Nat.pos_of_ne_zero fun h => by simp [h] at hq0
      have : t * t' ≤ t * u := Nat.mul_le_mul_left t (Nat.le_of_dvd hu0 ht'u)
      have := hpair t htP t' ht'P hne
      omega
    · rintro (rfl | hqP)
      · exact ⟨⟨one_dvd n, hn0.ne'⟩, by rw [one_mul]; exact Nat.div_le_self n Q⟩
      · refine ⟨⟨dvd_mul_of_dvd_right (dvd_prod_of_mem _ hqP) ℓ, hn0.ne'⟩, ?_⟩
        calc q * (n / Q) ≤ Q * (n / Q) := Nat.mul_le_mul_right _ (hmax q hqP)
          _ = n := hnQ.symm
  have h1P : (1 : ℕ) ∉ P := fun h => Nat.not_prime_one (hP 1 h)
  rw [hset, sum_insert h1P]
  have hsumP : ∑ p ∈ P, moebiusReal p = -(P.card : ℝ) := by
    rw [sum_congr rfl fun p hp => show moebiusReal p = -1 by
      unfold moebiusReal; rw [moebius_apply_prime (hP p hp)]; norm_num]
    simp
  have hμn : moebiusReal n = -(-1 : ℝ) ^ P.card := by
    unfold moebiusReal
    rw [isMultiplicative_moebius.map_mul_of_coprime hcopℓ, moebius_apply_prime hℓ,
      isMultiplicative_moebius.map_prod_of_prime P hP,
      prod_congr rfl fun p hp => moebius_apply_prime (hP p hp)]
    simp
  have h1 : moebiusReal 1 = 1 := by simp [moebiusReal]
  rw [hsumP, h1, hμn]
  ring

/-- **Exactness of rung two.** For every prime `p > 11`, at `N = 105p - 1` the integer
`k = 1155p = 11(N+1)` has response `-3`. -/
theorem sieveSeq_moebiusReal_rung_two_family {p : ℕ} (hp : p.Prime) (h11 : 11 < p) :
    sieveSeq (105 * p - 1) moebiusReal (1155 * p) = -3 := by
  have h := (sieveSeq_moebiusReal_prime_shell (P := {3, 5, 7, 11}) (Q := 11)
    (by intro q hq; simp only [mem_insert, mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> norm_num)
    (by simp) (by intro q hq; simp only [mem_insert, mem_singleton] at hq; omega)
    (by intro a ha b hb hab; simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> omega)
    hp h11).2
  have hprod : p * ∏ q ∈ ({3, 5, 7, 11} : Finset ℕ), q = 1155 * p := by
    simp; ring
  rw [hprod, show 1155 * p / 11 = 105 * p by omega] at h
  rw [h]
  simp
  norm_num

/-- **Exactness of rung three.** For every prime `p > 13`, at `N = 1155p - 1` the integer
`k = 15015p = 13(N+1)` has response `4`. -/
theorem sieveSeq_moebiusReal_rung_three_family {p : ℕ} (hp : p.Prime) (h13 : 13 < p) :
    sieveSeq (1155 * p - 1) moebiusReal (15015 * p) = 4 := by
  have h := (sieveSeq_moebiusReal_prime_shell (P := {3, 5, 7, 11, 13}) (Q := 13)
    (by intro q hq; simp only [mem_insert, mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num)
    (by simp) (by intro q hq; simp only [mem_insert, mem_singleton] at hq; omega)
    (by intro a ha b hb hab; simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl | rfl | rfl | rfl <;>
          rcases hb with rfl | rfl | rfl | rfl | rfl <;> omega)
    hp h13).2
  have hprod : p * ∏ q ∈ ({3, 5, 7, 11, 13} : Finset ℕ), q = 15015 * p := by
    simp; ring
  rw [hprod, show 15015 * p / 13 = 1155 * p by omega] at h
  rw [h]
  simp
  norm_num

/-- The **prime shell** of `Q`: the primes `p ≤ Q` with `p² > Q`. -/
def primeShell (Q : ℕ) : Finset ℕ := (Icc 1 Q).filter (fun p => p.Prime ∧ Q < p * p)

/-- **Shell responses.** For a prime `Q` and a prime `ℓ > Q`, the integer `n = ℓ ∏ primeShell Q`
sits at ratio exactly `Q` above the horizon `N = n/Q - 1` and has response of magnitude
`|primeShell Q| - 1`. -/
theorem abs_sieveSeq_moebiusReal_primeShell {Q ℓ : ℕ} (hQ : Q.Prime) (hℓ : ℓ.Prime) (hQℓ : Q < ℓ) :
    ℓ * ∏ p ∈ primeShell Q, p = Q * ((ℓ * ∏ p ∈ primeShell Q, p) / Q - 1 + 1) ∧
      |sieveSeq ((ℓ * ∏ p ∈ primeShell Q, p) / Q - 1) moebiusReal (ℓ * ∏ p ∈ primeShell Q, p)| =
        ((primeShell Q).card : ℝ) - 1 := by
  have hmem : ∀ p, p ∈ primeShell Q ↔ (1 ≤ p ∧ p ≤ Q) ∧ p.Prime ∧ Q < p * p := fun p => by
    simp [primeShell, mem_filter, mem_Icc]
  have hQmem : Q ∈ primeShell Q := (hmem Q).mpr ⟨⟨hQ.one_le, le_rfl⟩, hQ, by
    have := hQ.two_le; nlinarith⟩
  have h := sieveSeq_moebiusReal_prime_shell (P := primeShell Q) (Q := Q)
    (fun p hp => ((hmem p).mp hp).2.1) hQmem (fun p hp => ((hmem p).mp hp).1.2)
    (by
      intro a ha b hb _
      have ha' := ((hmem a).mp ha).2.2
      have hb' := ((hmem b).mp hb).2.2
      rcases le_total a b with hab | hab
      · nlinarith [Nat.mul_le_mul_left a hab]
      · nlinarith [Nat.mul_le_mul_left b hab])
    hℓ hQℓ
  refine ⟨h.1, ?_⟩
  rw [h.2, abs_mul, abs_neg, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have : (1 : ℝ) ≤ (primeShell Q).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨Q, hQmem⟩
  rw [abs_of_nonneg (by linarith)]

/-- **Near-linear growth of the shell.** Eventually the prime shell of `Q` holds at least
`⌊Q/2⌋ / (2 log ⌊Q/2⌋)` primes, so responses at ratio `Q` reach order `Q / log Q`. -/
theorem eventually_card_primeShell_ge :
    ∀ᶠ Q : ℕ in Filter.atTop,
      ((Q / 2 : ℕ) : ℝ) / (2 * Real.log (Q / 2 : ℕ)) ≤ ((primeShell Q).card : ℝ) := by
  have hdiv : Filter.Tendsto (fun Q : ℕ => Q / 2) Filter.atTop Filter.atTop :=
    Nat.tendsto_div_const_atTop (by norm_num)
  filter_upwards [hdiv.eventually eventually_card_primes_first_octave_ge,
    Filter.eventually_ge_atTop 4] with Q hQ hQ4
  refine hQ.trans ?_
  exact_mod_cast card_le_card fun p hp => by
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hpI
    simp only [primeShell, mem_filter, mem_Icc]
    refine ⟨⟨by omega, by omega⟩, hpp, ?_⟩
    have : Q / 2 + 1 ≤ p := hlo
    nlinarith [Nat.div_add_mod Q 2, Nat.mod_lt Q (show 0 < 2 by norm_num)]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
