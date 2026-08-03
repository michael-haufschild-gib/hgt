import GaloisForLFunctions.RHTower.Sieve.ShiuSharp

/-!
# The Hardy–Ramanujan recursion in an interval

Counting pairs `(n, p)` with `n` in an interval, `ω n = j`, and `p` a prime factor of `n` gives
`j` times the count of such `n`.  Splitting off the maximal prime power `p ^ v_p(n)` sends the pair
to a prime power `q ≤ b` together with an integer of the rescaled interval `(a/q, b/q]` carrying one
fewer prime factor, and the map is injective: the prime power and the complementary factor
reconstruct both `n` and `p`.

Hence

`j · #{n ∈ (a,b] : ω n = j} ≤ ∑_{q ≤ b prime power} #{m ∈ (a/q, b/q] : ω m = j - 1}`.

This is the recursion behind every Hardy–Ramanujan style bound.  The interval version is
unconditional and needs no size hypothesis; the analytic content enters only when the inner counts
are estimated.
-/

namespace RHTower.Sieve

open Finset Nat

/-- The set of integers of an interval with exactly `j` distinct prime factors. -/
def omegaLevel (a b j : ℕ) : Finset ℕ := {n ∈ Finset.Ioc a b | n.primeFactors.card = j}

/-- Every integer of `Ioc a b` is `b`-smooth. -/
theorem mem_smoothUpTo_self {a b n : ℕ} (hn : n ∈ Finset.Ioc a b) :
    n ∈ smoothUpTo (Nat.primesLE b) b := by
  obtain ⟨han, hnb⟩ := Finset.mem_Ioc.1 hn
  have hn0 : n ≠ 0 := by omega
  refine mem_smoothUpTo.2 ⟨⟨by omega, hnb⟩, ?_⟩
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hple : p ≤ n := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
  exact Nat.mem_primesLE.2 ⟨le_trans hple hnb, hprime⟩

/-- Splitting off a maximal prime power drops the distinct prime count by one. -/
theorem card_primeFactors_ordCompl {n p : ℕ} (hn : n ≠ 0) (hp : p ∈ n.primeFactors) :
    (n / p ^ n.factorization p).primeFactors.card + 1 = n.primeFactors.card := by
  classical
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have he : 0 < n.factorization p :=
    Nat.Prime.factorization_pos_of_dvd hprime hn (Nat.dvd_of_mem_primeFactors hp)
  have hrecon : p ^ n.factorization p * (n / p ^ n.factorization p) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n p
  have hq0 : p ^ n.factorization p ≠ 0 := pow_ne_zero _ hprime.pos.ne'
  have hm0 : n / p ^ n.factorization p ≠ 0 := (Nat.ordCompl_pos p hn).ne'
  have hfac : n.primeFactors
      = (p ^ n.factorization p).primeFactors ∪ (n / p ^ n.factorization p).primeFactors := by
    conv_lhs => rw [← hrecon]
    exact Nat.primeFactors_mul hq0 hm0
  have hpow : (p ^ n.factorization p).primeFactors = {p} := by
    rw [Nat.primeFactors_pow p he.ne', hprime.primeFactors]
  have hdisj : Disjoint ({p} : Finset ℕ) (n / p ^ n.factorization p).primeFactors := by
    refine Finset.disjoint_singleton_left.2 ?_
    intro hcon
    exact Nat.not_dvd_ordCompl hprime hn (Nat.dvd_of_mem_primeFactors hcon)
  rw [hfac, hpow, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
  omega

/-- **Hardy–Ramanujan recursion.**  Each of the `j` prime factors of an integer with `ω n = j`
splits it into a prime power and an integer of the rescaled interval with one fewer prime factor,
injectively. -/
theorem card_omegaLevel_mul_le (a b j : ℕ) :
    j * (omegaLevel a b j).card
      ≤ ∑ q ∈ primePowerSet b b, (omegaLevel (a / q) (b / q) (j - 1)).card := by
  classical
  set A : Finset ℕ := omegaLevel a b j with hA
  set S1 : Finset ((_ : ℕ) × ℕ) := A.sigma fun n => n.primeFactors with hS1
  set B : Finset ((_ : ℕ) × ℕ) :=
    (primePowerSet b b).sigma fun q => omegaLevel (a / q) (b / q) (j - 1) with hB
  have hcardS : S1.card = j * A.card := by
    rw [hS1, Finset.card_sigma]
    have : ∀ n ∈ A, n.primeFactors.card = j := by
      intro n hn
      exact (Finset.mem_filter.1 hn).2
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]
  have hcardB : B.card = ∑ q ∈ primePowerSet b b, (omegaLevel (a / q) (b / q) (j - 1)).card := by
    rw [hB, Finset.card_sigma]
  set f : ((_ : ℕ) × ℕ) → ((_ : ℕ) × ℕ) :=
    fun x => ⟨x.2 ^ x.1.factorization x.2, x.1 / x.2 ^ x.1.factorization x.2⟩ with hf
  have hmaps : ∀ x ∈ S1, f x ∈ B := by
    rintro ⟨n, p⟩ hx
    simp only [hf]
    simp only [hS1, Finset.mem_sigma] at hx
    obtain ⟨hnA, hp⟩ := hx
    obtain ⟨hnmem, hncard⟩ := Finset.mem_filter.1 hnA
    obtain ⟨han, hnb⟩ := Finset.mem_Ioc.1 hnmem
    have hn0 : n ≠ 0 := by omega
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have he : 0 < n.factorization p :=
      Nat.Prime.factorization_pos_of_dvd hprime hn0 (Nat.dvd_of_mem_primeFactors hp)
    set q : ℕ := p ^ n.factorization p with hq
    have hqpos : 0 < q := pow_pos hprime.pos _
    have hrecon : q * (n / q) = n := Nat.ordProj_mul_ordCompl_eq_self n p
    have hqmem : q ∈ primePowerSet b b :=
      maxPrimePow_mem_primePowerSet (mem_smoothUpTo_self hnmem) hp
    refine Finset.mem_sigma.2 ⟨hqmem, ?_⟩
    dsimp only
    unfold omegaLevel
    refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨?_, ?_⟩, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hqpos]
      have : n / q * q = n := by rw [mul_comm] at hrecon; exact hrecon
      omega
    · rw [Nat.le_div_iff_mul_le hqpos]
      have : n / q * q = n := by rw [mul_comm] at hrecon; exact hrecon
      omega
    · have h2 := card_primeFactors_ordCompl hn0 hp
      rw [hncard, ← hq] at h2
      omega
  have hinj : ∀ x ∈ S1, ∀ y ∈ S1, f x = f y → x = y := by
    rintro ⟨n, p⟩ hx ⟨n', p'⟩ hy hxy
    simp only [hS1, Finset.mem_sigma] at hx hy
    obtain ⟨hnA, hp⟩ := hx
    obtain ⟨hnA', hp'⟩ := hy
    obtain ⟨hnmem, -⟩ := Finset.mem_filter.1 hnA
    obtain ⟨hnmem', -⟩ := Finset.mem_filter.1 hnA'
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Ioc.1 hnmem).1; omega
    have hn0' : n' ≠ 0 := by
      have := (Finset.mem_Ioc.1 hnmem').1; omega
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hprime' : p'.Prime := Nat.prime_of_mem_primeFactors hp'
    have he : 0 < n.factorization p :=
      Nat.Prime.factorization_pos_of_dvd hprime hn0 (Nat.dvd_of_mem_primeFactors hp)
    have he' : 0 < n'.factorization p' :=
      Nat.Prime.factorization_pos_of_dvd hprime' hn0' (Nat.dvd_of_mem_primeFactors hp')
    have hq : p ^ n.factorization p = p' ^ n'.factorization p' := congrArg Sigma.fst hxy
    have hm : n / p ^ n.factorization p = n' / p' ^ n'.factorization p' := by
      have := congrArg Sigma.snd hxy
      simpa [hf] using this
    have hpp : p = p' := by
      have hdvd : p ∣ p' ^ n'.factorization p' := by
        rw [← hq]
        exact dvd_pow_self p he.ne'
      exact (Nat.prime_dvd_prime_iff_eq hprime hprime').1 (hprime.dvd_of_dvd_pow hdvd)
    have hnn : n = n' := by
      have h1 : p ^ n.factorization p * (n / p ^ n.factorization p) = n :=
        Nat.ordProj_mul_ordCompl_eq_self n p
      have h2 : p' ^ n'.factorization p' * (n' / p' ^ n'.factorization p') = n' :=
        Nat.ordProj_mul_ordCompl_eq_self n' p'
      calc n = p ^ n.factorization p * (n / p ^ n.factorization p) := h1.symm
        _ = p' ^ n'.factorization p' * (n' / p' ^ n'.factorization p') := by rw [hm, hq]
        _ = n' := h2
    subst hnn
    subst hpp
    rfl
  have := Finset.card_le_card_of_injOn f hmaps hinj
  omega

end RHTower.Sieve
