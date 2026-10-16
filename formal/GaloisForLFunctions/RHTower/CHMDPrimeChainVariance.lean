import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic

/-!
# Exact prime-chain variance factorization of divisor cuts

Every active von Mangoldt edge between divisors belongs to exactly one prime
chain. At a logarithmic cut each chain is a complete bipartite graph, with
constant edge weight log p. Its energy is exactly the sum of the two internal
variances and the squared difference of the two means.

The reindexing is finite and exhaustive for every product index. Empty sides
and cut endpoints are retained. The companion source leaf transfers this
identity to the original absolutely convergent prime Doob source.
-/

open Set
open scoped BigOperators
noncomputable section
namespace RHTower.CHMDPrimeChain

/-- Divisors in one prime chain strictly below the logarithmic cut. -/
def chainLeft (N p b : ℕ) (u : ℝ) : Finset ℕ :=
  N.divisors.filter fun m => ordCompl[p] m = b ∧ Real.log m < u

/-- Divisors in the same chain strictly above the logarithmic cut. -/
def chainRight (N p b : ℕ) (u : ℝ) : Finset ℕ :=
  N.divisors.filter fun m => ordCompl[p] m = b ∧ u < Real.log m

/-- Arithmetic mean, with Lean's zero value on the empty set. -/
def mean (S : Finset ℕ) (a : ℕ → ℝ) : ℝ := (∑ m ∈ S, a m) / S.card

/-- Unnormalized variance within one side of a prime chain. -/
def scatter (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ m ∈ S, (a m - mean S a) ^ 2

def bipartiteEnergy (L R : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ m ∈ L, ∑ k ∈ R, (a m - a k) ^ 2

/-- Exact three-square-sector decomposition of a complete bipartite energy. -/
def varianceEnergy (L R : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  R.card * scatter L a + L.card * scatter R a +
    L.card * R.card * (mean L a - mean R a) ^ 2

theorem sum_centered (S : Finset ℕ) (a : ℕ → ℝ) :
    (∑ m ∈ S, (a m - mean S a)) = 0 := by
  by_cases hS : S = ∅
  · simp [hS]
  have hc : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mean]
  field_simp
  ring

theorem sum_eq_card_mul_mean (S : Finset ℕ) (a : ℕ → ℝ) :
    (∑ m ∈ S, a m) = S.card * mean S a := by
  have h := sum_centered S a
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, sub_eq_zero] using h

theorem scatter_eq (S : Finset ℕ) (a : ℕ → ℝ) :
    scatter S a = (∑ m ∈ S, a m ^ 2) - S.card * mean S a ^ 2 := by
  unfold scatter
  simp_rw [show ∀ m, (a m - mean S a) ^ 2 =
    a m ^ 2 - 2 * mean S a * a m + mean S a ^ 2 by intro m; ring]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, sum_eq_card_mul_mean S a]
  ring

theorem bipartiteEnergy_eq_variance (L R : Finset ℕ) (a : ℕ → ℝ) :
    bipartiteEnergy L R a = varianceEnergy L R a := by
  have he (m k : ℕ) : (a m - a k) ^ 2 = a m ^ 2 + a k ^ 2 - 2 * a m * a k := by ring
  unfold bipartiteEnergy varianceEnergy
  rw [scatter_eq, scatter_eq]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul,
    sum_eq_card_mul_mean L a, sum_eq_card_mul_mean R a]
  ring

theorem varianceEnergy_nonneg (L R : Finset ℕ) (a : ℕ → ℝ) :
    0 ≤ varianceEnergy L R a := by
  unfold varianceEnergy scatter
  positivity

theorem exists_pow_mul_of_same_chain {p m k : ℕ} (hp : p.Prime) (_hm : 0 < m)
    (hmk : m < k) (he : ordCompl[p] m = ordCompl[p] k) :
    ∃ r : ℕ, 0 < r ∧ k = m * p ^ r := by
  have hm' := Nat.ordProj_mul_ordCompl_eq_self m p
  have hk' := Nat.ordProj_mul_ordCompl_eq_self k p
  rw [← he] at hk'
  have hij : m.factorization p < k.factorization p := by
    by_contra h
    have hle : p ^ k.factorization p ≤ p ^ m.factorization p :=
      Nat.pow_le_pow_right hp.pos (Nat.le_of_not_gt h)
    have := Nat.mul_le_mul_right (ordCompl[p] m) hle
    omega
  refine ⟨k.factorization p - m.factorization p, Nat.sub_pos_of_lt hij, ?_⟩
  calc
    k = p ^ k.factorization p * (ordCompl[p] m) := hk'.symm
    _ = (p ^ m.factorization p * (ordCompl[p] m)) *
        p ^ (k.factorization p - m.factorization p) := by
      conv_lhs => rw [show k.factorization p =
        m.factorization p + (k.factorization p - m.factorization p) by omega, pow_add]
      ring
    _ = _ := by rw [hm']

theorem same_chain_of_pow_mul {p m k r : ℕ} (hp : p.Prime)
    (he : k = m * p ^ r) : ordCompl[p] m = ordCompl[p] k := by
  rw [he, Nat.ordCompl_mul, Nat.ordCompl_self_pow hp, mul_one]

theorem prime_unique_of_same_chain {p q m k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hm : 0 < m) (hmk : m < k) (hpC : ordCompl[p] m = ordCompl[p] k)
    (hqC : ordCompl[q] m = ordCompl[q] k) : p = q := by
  obtain ⟨r, hr, hpr⟩ := exists_pow_mul_of_same_chain hp hm hmk hpC
  obtain ⟨s, hs, hqs⟩ := exists_pow_mul_of_same_chain hq hm hmk hqC
  have he : p ^ r = q ^ s := Nat.eq_of_mul_eq_mul_left hm (hpr.symm.trans hqs)
  have := congrArg Nat.minFac he
  simpa only [hp.pow_minFac hr.ne', hq.pow_minFac hs.ne'] using this

/-- An ordered divisor pair receives exactly its original Mangoldt weight. -/
theorem mangoldt_edge_eq_chain_sum {N m k : ℕ} (hm : m ∈ N.divisors)
    (hk : k ∈ N.divisors) (hmk : m < k) :
    (if m ∣ k then ArithmeticFunction.vonMangoldt (k / m) else 0) =
      ∑ p ∈ N.primeFactors,
        if ordCompl[p] m = ordCompl[p] k then Real.log p else 0 := by
  have hm0 := Nat.pos_of_mem_divisors hm
  have hkN := (Nat.mem_divisors.mp hk).1
  have hN := (Nat.mem_divisors.mp hk).2
  by_cases hex : ∃ p ∈ N.primeFactors, ordCompl[p] m = ordCompl[p] k
  · obtain ⟨p, hpN, hpC⟩ := hex
    have hp := Nat.prime_of_mem_primeFactors hpN
    obtain ⟨r, hr, hkr⟩ := exists_pow_mul_of_same_chain hp hm0 hmk hpC
    have hdiv : m ∣ k := ⟨p ^ r, hkr⟩
    have hquot : k / m = p ^ r := by rw [hkr, Nat.mul_div_cancel_left _ hm0]
    rw [if_pos hdiv, hquot, ArithmeticFunction.vonMangoldt_apply_pow hr.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    symm
    rw [Finset.sum_eq_single p]
    · simp [hpC]
    · intro q hq hqp
      rw [if_neg]
      intro hqC
      exact hqp (prime_unique_of_same_chain (Nat.prime_of_mem_primeFactors hq) hp hm0 hmk hqC hpC)
    · intro hnot
      exact (hnot hpN).elim
  · have hsum : (∑ p ∈ N.primeFactors,
        if ordCompl[p] m = ordCompl[p] k then Real.log p else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      exact if_neg (fun he => hex ⟨p, hp, he⟩)
    rw [hsum]
    split_ifs with hdiv
    · apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
      intro hpow
      obtain ⟨p, r, hp, hr, hpr⟩ := hpow
      have hp : p.Prime := Nat.prime_iff.mpr hp
      have hkr : k = m * p ^ r := by rw [hpr, Nat.mul_div_cancel' hdiv]
      have hpk : p ∣ k := by
        rw [hkr]
        exact dvd_mul_of_dvd_right (dvd_pow_self p hr.ne') m
      exact hex ⟨p, hp.mem_primeFactors (hpk.trans hkN) hN, same_chain_of_pow_mul hp hkr⟩
    · rfl

def chainEnergy (N : ℕ) (u : ℝ) (a : ℕ → ℝ) : ℝ :=
  ∑ p ∈ N.primeFactors, Real.log p *
    ∑ b ∈ N.divisors, bipartiteEnergy (chainLeft N p b u) (chainRight N p b u) a

def chainVariance (N : ℕ) (u : ℝ) (a : ℕ → ℝ) : ℝ :=
  ∑ p ∈ N.primeFactors, Real.log p *
    ∑ b ∈ N.divisors, varianceEnergy (chainLeft N p b u) (chainRight N p b u) a

theorem chainEnergy_eq_variance (N : ℕ) (u : ℝ) (a : ℕ → ℝ) :
    chainEnergy N u a = chainVariance N u a := by
  simp only [chainEnergy, chainVariance, bipartiteEnergy_eq_variance]

theorem chain_bipartite_eq (N p b : ℕ) (u : ℝ) (a : ℕ → ℝ) :
      bipartiteEnergy (chainLeft N p b u) (chainRight N p b u) a =
        ∑ m ∈ N.divisors, ∑ k ∈ N.divisors,
          if b = ordCompl[p] m then
            if u ∈ Ioo (Real.log m) (Real.log k) ∧ ordCompl[p] m = ordCompl[p] k
            then (a m - a k) ^ 2 else 0
          else 0 := by
  unfold bipartiteEnergy chainLeft chainRight
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hbm : b = ordCompl[p] m
  · subst b
    by_cases hl : Real.log m < u
    · simp only [hl, and_true, if_true, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hc : ordCompl[p] k = ordCompl[p] m
      · simp [hc, hl]
      · simp [hc, Ne.symm hc, hl]
    · simp [hl]
  · simp [hbm, Ne.symm hbm]

theorem sum_chain_bipartite (N p : ℕ) (u : ℝ) (a : ℕ → ℝ) :
    (∑ b ∈ N.divisors, bipartiteEnergy (chainLeft N p b u) (chainRight N p b u) a) =
      ∑ m ∈ N.divisors, ∑ k ∈ N.divisors,
        if u ∈ Ioo (Real.log m) (Real.log k) ∧ ordCompl[p] m = ordCompl[p] k
        then (a m - a k) ^ 2 else 0 := by
  simp_rw [chain_bipartite_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hcm : ordCompl[p] m ∈ N.divisors := Nat.mem_divisors.mpr
    ⟨(Nat.ordCompl_dvd m p).trans (Nat.mem_divisors.mp hm).1,
      (Nat.mem_divisors.mp hm).2⟩
  simp [hcm]

theorem chainEnergy_eq_pairs (N : ℕ) (u : ℝ) (a : ℕ → ℝ) :
    chainEnergy N u a =
      ∑ m ∈ N.divisors, ∑ k ∈ N.divisors,
        if u ∈ Ioo (Real.log m) (Real.log k) then
          (∑ p ∈ N.primeFactors,
            if ordCompl[p] m = ordCompl[p] k then Real.log p else 0) *
            (a m - a k) ^ 2 else 0 := by
  unfold chainEnergy
  simp_rw [sum_chain_bipartite, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hcut : u ∈ Ioo (Real.log m) (Real.log k)
  · simp only [hcut, true_and, if_true, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> ring
  · simp [hcut]

/-- All divisor edges, primes, powers and chain bases are retained exactly. -/
theorem divisor_cut_eq_chainVariance (N : ℕ) (u : ℝ) (a : ℕ → ℝ) :
    (∑ k ∈ N.divisors, ∑ m ∈ k.divisors,
      if u ∈ Ioo (Real.log m) (Real.log k) then
        ArithmeticFunction.vonMangoldt (k / m) * (a m - a k) ^ 2 else 0) =
      chainVariance N u a := by
  rw [← chainEnergy_eq_variance, chainEnergy_eq_pairs, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 := Nat.pos_of_mem_divisors hk
  have hN := (Nat.mem_divisors.mp hk).2
  have hfilter : k.divisors = N.divisors.filter (fun m => m ∣ k) := by
    ext m
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hmk, _⟩
      exact ⟨⟨hmk.trans (Nat.mem_divisors.mp hk).1, hN⟩, hmk⟩
    · rintro ⟨_, hmk⟩
      exact ⟨hmk, hk0.ne'⟩
  rw [hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hcut : u ∈ Ioo (Real.log m) (Real.log k)
  · have hmk : m < k := by
      by_contra h
      have hlog : Real.log k ≤ Real.log m := Real.log_le_log
        (by exact_mod_cast hk0) (by exact_mod_cast Nat.le_of_not_gt h)
      exact (not_lt_of_ge hlog) (hcut.1.trans hcut.2)
    rw [← mangoldt_edge_eq_chain_sum hm hk hmk]
    by_cases hd : m ∣ k <;> simp [hcut, hd]
  · simp [hcut]

theorem chainVariance_nonneg (N : ℕ) (u : ℝ) (a : ℕ → ℝ) :
    0 ≤ chainVariance N u a := by
  unfold chainVariance
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (Real.log_nonneg (by exact_mod_cast
    (Nat.prime_of_mem_primeFactors hp).one_lt.le))
    (Finset.sum_nonneg fun b _ => varianceEnergy_nonneg _ _ _)

theorem varianceEnergy_zero_iff (L R : Finset ℕ) (a : ℕ → ℝ) :
    varianceEnergy L R a = 0 ↔ ∀ m ∈ L, ∀ k ∈ R, a m = a k := by
  rw [← bipartiteEnergy_eq_variance, bipartiteEnergy]
  simp only [Finset.sum_eq_zero_iff_of_nonneg
    (fun m _ => Finset.sum_nonneg fun k _ => sq_nonneg (a m - a k)),
    Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (_ - a k)),
    sq_eq_zero_iff, sub_eq_zero]

/-- Exact finite-fibre nullspace, with no connectivity or nonempty-side premise. -/
theorem chainVariance_zero_iff (N : ℕ) (u : ℝ) (a : ℕ → ℝ) :
    chainVariance N u a = 0 ↔
      ∀ p ∈ N.primeFactors, ∀ b ∈ N.divisors,
        ∀ m ∈ chainLeft N p b u, ∀ k ∈ chainRight N p b u, a m = a k := by
  have hlog (p : ℕ) (hp : p ∈ N.primeFactors) : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt)
  have hnn (p : ℕ) : 0 ≤ ∑ b ∈ N.divisors,
      varianceEnergy (chainLeft N p b u) (chainRight N p b u) a :=
    Finset.sum_nonneg fun b _ => varianceEnergy_nonneg _ _ _
  constructor
  · intro h p hp b hb
    have ht := (Finset.sum_eq_zero_iff_of_nonneg
      (fun q hq => mul_nonneg (hlog q hq).le (hnn q))).mp h p hp
    have hs := (mul_eq_zero.mp ht).resolve_left (hlog p hp).ne'
    have hv := (Finset.sum_eq_zero_iff_of_nonneg
      (fun d _ => varianceEnergy_nonneg (chainLeft N p d u) (chainRight N p d u) a)).mp hs b hb
    exact (varianceEnergy_zero_iff _ _ _).mp hv
  · intro h
    unfold chainVariance
    apply Finset.sum_eq_zero
    intro p hp
    have hs : (∑ b ∈ N.divisors,
        varianceEnergy (chainLeft N p b u) (chainRight N p b u) a) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      exact (varianceEnergy_zero_iff _ _ _).mpr (h p hp b hb)
    rw [hs, mul_zero]

theorem varianceEnergy_empty_left (R : Finset ℕ) (a : ℕ → ℝ) :
    varianceEnergy ∅ R a = 0 := by simp [varianceEnergy, scatter]

theorem varianceEnergy_empty_right (L : Finset ℕ) (a : ℕ → ℝ) :
    varianceEnergy L ∅ a = 0 := by simp [varianceEnergy, scatter]

theorem chainLeft_eq_empty_of_nonpos (N p b : ℕ) {u : ℝ} (hu : u ≤ 0) :
    chainLeft N p b u = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro m hm
  obtain ⟨hm, _, hlt⟩ := Finset.mem_filter.mp hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.pos_of_mem_divisors hm
  have hlog := Real.log_nonneg hm1
  linarith

theorem chainRight_eq_empty_of_log_le (N p b : ℕ) {u : ℝ}
    (hu : Real.log N ≤ u) : chainRight N p b u = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro m hm
  obtain ⟨hm, _, hlt⟩ := Finset.mem_filter.mp hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_mem_divisors hm
  have hmN : (m : ℝ) ≤ N := by exact_mod_cast Nat.divisor_le hm
  have hlog := Real.log_le_log hm0 hmN
  linarith

theorem chainVariance_term_zero_outside (N p b : ℕ) (u : ℝ) (a : ℕ → ℝ)
    (hu : u ∉ Ioo (0 : ℝ) (Real.log N)) :
    varianceEnergy (chainLeft N p b u) (chainRight N p b u) a = 0 := by
  by_cases hu0 : 0 < u
  · have huN : Real.log N ≤ u := by simpa only [mem_Ioo, hu0, true_and, not_lt] using hu
    rw [chainRight_eq_empty_of_log_le N p b huN, varianceEnergy_empty_right]
  · rw [chainLeft_eq_empty_of_nonpos N p b (le_of_not_gt hu0), varianceEnergy_empty_left]

end RHTower.CHMDPrimeChain
