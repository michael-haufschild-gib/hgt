import Mathlib

/-!
# The power map is a Frobenius at one prime

On the multiplicative monoid of `ℤ` the maps `F_n : x ↦ x ^ n` commute and satisfy
`F_m F_n = F_{mn}`. At a prime `q` two things can happen to `F_n`.

* `F_n` fixes every point of the fibre `𝔽_q` exactly when `q − 1 ∣ n − 1`
  (`forall_pow_eq_self_iff`), hence on at most `d(n − 1)` fibres (`ncard_fixed_fibres_le`).
* `F_n` is additive in characteristic `q`, that is a Frobenius, exactly when `n` is a power of `q`
  (`isFrobeniusAt_iff`).

Hence for `n ≥ 2` there is at most one prime at which `F_n` is a Frobenius, and counting those
primes with weight `log q` gives the von Mangoldt function
(`vonMangoldt_eq_finsum_log_isFrobeniusAt`): the prime part of the point count of `Spec ℤ` is the
weighted number of points at which `F_n` is a Frobenius.
-/

open Polynomial ArithmeticFunction

namespace GaloisForLFunctions.SignFreePurityMechanisms

/-! ### Where the power map fixes the fibre -/

/-- `x ↦ x ^ n` is the identity on `𝔽_p` exactly when `p − 1` divides `n − 1`. -/
theorem forall_pow_eq_self_iff (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) :
    (∀ x : ZMod p, x ^ n = x) ↔ (p - 1) ∣ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  constructor
  · intro h
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hord : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
    have hgm : g ^ m = 1 := by
      have hval : g ^ (m + 1) = g := Units.ext (by simpa using h (g : ZMod p))
      rw [pow_succ] at hval
      exact mul_eq_right.mp hval
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hgm
  · rintro ⟨c, rfl⟩ x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [pow_succ, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, one_mul]

/-- The `n`-th power map fixes pointwise at most `d(n − 1)` fibres of `Spec ℤ`: one for each
divisor `p − 1` of `n − 1`. -/
theorem ncard_fixed_fibres_le {n : ℕ} (hn : 2 ≤ n) :
    {p : ℕ | p.Prime ∧ ∀ x : ZMod p, x ^ n = x}.ncard ≤ (n - 1).divisors.card := by
  have hmaps : ∀ p ∈ {p : ℕ | p.Prime ∧ ∀ x : ZMod p, x ^ n = x},
      p - 1 ∈ ((n - 1).divisors : Set ℕ) := by
    rintro p ⟨hp, hfix⟩
    haveI : Fact p.Prime := ⟨hp⟩
    exact Finset.mem_coe.mpr (Nat.mem_divisors.mpr
      ⟨(forall_pow_eq_self_iff p (by omega)).mp hfix, by omega⟩)
  have hinj : Set.InjOn (fun p : ℕ => p - 1) {p : ℕ | p.Prime ∧ ∀ x : ZMod p, x ^ n = x} := by
    rintro p ⟨hp, -⟩ q ⟨hq, -⟩ hpq
    have hp1 := hp.pos
    have hq1 := hq.pos
    simp only at hpq
    omega
  have hle := Set.ncard_le_ncard_of_injOn _ hmaps hinj (Finset.finite_toSet _)
  rwa [Set.ncard_coe_finset] at hle

/-! ### Where the power map is a Frobenius -/

/-- `x ↦ x ^ n` is additive in characteristic `q`: the identity `(X + 1) ^ n = X ^ n + 1` over
`𝔽_q`. -/
def IsFrobeniusAt (n q : ℕ) : Prop :=
  (X + 1 : (ZMod q)[X]) ^ n = X ^ n + 1

/-- Powers of `q` are Frobenius maps at `q`. -/
theorem isFrobeniusAt_prime_pow (q : ℕ) [Fact q.Prime] (k : ℕ) : IsFrobeniusAt (q ^ k) q := by
  unfold IsFrobeniusAt
  rw [add_pow_char_pow, one_pow]

/-- The power map of exponent `n ≥ 1` is a Frobenius at `q` exactly when `n` is a power of `q`:
for `n = q ^ v * m` with `q ∤ m`, the coefficient of `X ^ (q ^ v)` in `(X + 1) ^ n` is `m`. -/
theorem isFrobeniusAt_iff (q : ℕ) [Fact q.Prime] {n : ℕ} (hn : 1 ≤ n) :
    IsFrobeniusAt n q ↔ ∃ k, n = q ^ k := by
  have hq : q.Prime := Fact.out
  constructor
  · intro h
    obtain ⟨v, m, hqm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) q hq.ne_one
    refine ⟨v, ?_⟩
    by_contra hne
    have hm1 : m ≠ 1 := fun h1 => hne (by rw [h1, mul_one])
    have hqv : 0 < q ^ v := pow_pos hq.pos v
    have hL : ((X + 1 : (ZMod q)[X]) ^ (q ^ v * m)).coeff (q ^ v) = (m : ZMod q) := by
      have hexp : (X ^ q ^ v + 1 : (ZMod q)[X]) = expand (ZMod q) (q ^ v) (X + 1) := by simp
      have hc := coeff_expand_mul hqv ((X + 1 : (ZMod q)[X]) ^ m) 1
      rw [one_mul] at hc
      rw [pow_mul, add_pow_char_pow, one_pow, hexp, ← map_pow, hc, coeff_X_add_one_pow,
        Nat.choose_one_right]
    have hR : ((X : (ZMod q)[X]) ^ (q ^ v * m) + 1).coeff (q ^ v) = 0 := by
      have h1 : q ^ v ≠ q ^ v * m := fun e => hm1 (by
        have := Nat.eq_of_mul_eq_mul_left hqv (e.symm.trans (mul_one _).symm)
        exact this)
      rw [coeff_add, coeff_X_pow, coeff_one, if_neg h1, if_neg hqv.ne', add_zero]
    have hcoeff := congrArg (fun P : (ZMod q)[X] => P.coeff (q ^ v)) h
    simp only [hL, hR] at hcoeff
    exact hqm ((ZMod.natCast_eq_zero_iff m q).mp hcoeff)
  · rintro ⟨k, rfl⟩
    exact isFrobeniusAt_prime_pow q k

/-- For `n ≥ 2` the power map is a Frobenius at no more than one prime. -/
theorem eq_of_isFrobeniusAt {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hn : 2 ≤ n)
    (h₁ : IsFrobeniusAt n p) (h₂ : IsFrobeniusAt n q) : p = q := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, rfl⟩ := (isFrobeniusAt_iff p (by omega)).mp h₁
  obtain ⟨j, hj⟩ := (isFrobeniusAt_iff q (by omega)).mp h₂
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hn
  have hdvd : p ∣ q ^ j := hj ▸ dvd_pow_self p hk
  exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd)

/-- The von Mangoldt function counts, with weight `log q`, the primes at which the `n`-th power
map is a Frobenius. -/
theorem vonMangoldt_eq_finsum_log_isFrobeniusAt {n : ℕ} (hn : 2 ≤ n) :
    Λ n = ∑ᶠ q ∈ {q : ℕ | q.Prime ∧ IsFrobeniusAt n q}, Real.log q := by
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    haveI : Fact p.Prime := ⟨hp⟩
    have hset : {q : ℕ | q.Prime ∧ IsFrobeniusAt (p ^ k) q} = {p} := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hq, hF⟩
        exact eq_of_isFrobeniusAt hq hp hn hF (isFrobeniusAt_prime_pow p k)
      · rintro rfl
        exact ⟨hp, isFrobeniusAt_prime_pow q k⟩
    rw [hset, finsum_mem_singleton, vonMangoldt_apply_pow hk.ne', vonMangoldt_apply_prime hp]
  · have hset : {q : ℕ | q.Prime ∧ IsFrobeniusAt n q} = ∅ := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hq hF
      haveI : Fact q.Prime := ⟨hq⟩
      obtain ⟨k, rfl⟩ := (isFrobeniusAt_iff q (by omega)).mp hF
      refine hpp ((isPrimePow_nat_iff _).mpr ⟨q, k, hq, ?_, rfl⟩)
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hn
      · exact hk
    rw [hset, finsum_mem_empty, vonMangoldt_eq_zero_iff.mpr hpp]

#print axioms forall_pow_eq_self_iff
#print axioms ncard_fixed_fibres_le
#print axioms isFrobeniusAt_iff
#print axioms vonMangoldt_eq_finsum_log_isFrobeniusAt

end GaloisForLFunctions.SignFreePurityMechanisms
