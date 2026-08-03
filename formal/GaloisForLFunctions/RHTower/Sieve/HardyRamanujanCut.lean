import GaloisForLFunctions.RHTower.Sieve.PrimePowerSum

/-!
# The Hardy–Ramanujan recursion with a cut

The plain recursion sums over every prime power up to `b`, and in a short interval each such term
carries an unavoidable `+1` of sieve remainder, so the total error is proportional to the number of
prime powers below `b` — far larger than the interval.

Cutting the recursion at a level `Q` repairs this.  The maximal prime powers of `n` multiply to `n`,
so at most `log b / log Q` of them can exceed `Q`; if `b < Q ^ (R+1)` then at most `R` do.  Hence at
least `j - R` of the `j` splittings of an integer with `ω n = j` land below the cut, and

`(j - R) · #{n ∈ (a,b] : ω n = j} ≤ ∑_{q ≤ Q prime power} #{m ∈ (a/q, b/q] : ω m = j - 1}`.

The error is now proportional to `Q`, which may be taken subpolynomial in `b` while `R` stays a
small fraction of `j`; the recursion then loses only a factor `1 + R/j` per step.
-/

namespace RHTower.Sieve

open Finset Nat

/-- The primes of `n` whose maximal prime power exceeds `Q`. -/
def bigPowSet (Q n : ℕ) : Finset ℕ := {p ∈ n.primeFactors | ¬ p ^ n.factorization p ≤ Q}

/-- The maximal prime powers exceeding the cut multiply to a divisor of `n`, so there are few of
them. -/
theorem pow_card_bigPowSet_le {n : ℕ} (hn : n ≠ 0) (Q : ℕ) :
    Q ^ (bigPowSet Q n).card ≤ n := by
  classical
  have hsub : bigPowSet Q n ⊆ n.primeFactors := Finset.filter_subset _ _
  have hprod_dvd : (∏ p ∈ bigPowSet Q n, p ^ n.factorization p) ∣ n := by
    refine dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ hsub) ?_
    have h := Nat.prod_factorization_pow_eq_self hn
    rw [Finsupp.prod, Nat.support_factorization] at h
    exact ⟨1, by rw [mul_one, h]⟩
  have hle : Q ^ (bigPowSet Q n).card ≤ ∏ p ∈ bigPowSet Q n, p ^ n.factorization p := by
    have hterm : ∀ p ∈ bigPowSet Q n, Q ≤ p ^ n.factorization p := by
      intro p hp
      exact le_of_lt (not_le.1 (Finset.mem_filter.1 hp).2)
    calc Q ^ (bigPowSet Q n).card = ∏ _p ∈ bigPowSet Q n, Q := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ bigPowSet Q n, p ^ n.factorization p := Finset.prod_le_prod' hterm
  exact le_trans hle (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hprod_dvd)

/-- With `b < Q ^ (R+1)` no integer of `Ioc a b` has more than `R` maximal prime powers above the
cut. -/
theorem card_bigPowSet_le {n Q R b : ℕ} (hn : n ≠ 0) (hnb : n ≤ b) (hQ : 2 ≤ Q)
    (hR : b < Q ^ (R + 1)) : (bigPowSet Q n).card ≤ R := by
  by_contra hcon
  have hlt : R + 1 ≤ (bigPowSet Q n).card := by omega
  have h1 : Q ^ (R + 1) ≤ Q ^ (bigPowSet Q n).card := Nat.pow_le_pow_right (by omega) hlt
  have h2 : Q ^ (bigPowSet Q n).card ≤ n := pow_card_bigPowSet_le hn Q
  omega

/-- The primes of `n` whose maximal prime power lies at or below `Q`. -/
def smallPowSet (Q n : ℕ) : Finset ℕ := {p ∈ n.primeFactors | p ^ n.factorization p ≤ Q}

/-- At least `j - R` of the `j` maximal prime powers lie below the cut. -/
theorem card_smallPowSet_ge {n Q R b j : ℕ} (hn : n ≠ 0) (hnb : n ≤ b) (hQ : 2 ≤ Q)
    (hR : b < Q ^ (R + 1)) (hj : n.primeFactors.card = j) :
    j - R ≤ (smallPowSet Q n).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := n.primeFactors)
    (p := fun p => p ^ n.factorization p ≤ Q)
  have hbig : (bigPowSet Q n).card ≤ R := card_bigPowSet_le hn hnb hQ hR
  unfold bigPowSet at hbig
  unfold smallPowSet
  omega

/-- **Cut Hardy–Ramanujan recursion.**  At least `j - R` of the `j` maximal prime powers of an
integer with `ω n = j` lie below the cut, and each of those splittings is injective. -/
theorem card_omegaLevel_mul_le_cut (a b j Q R : ℕ) (hQ : 2 ≤ Q) (hR : b < Q ^ (R + 1)) :
    (j - R) * (omegaLevel a b j).card
      ≤ ∑ q ∈ {q ∈ primePowerSet b b | q ≤ Q}, (omegaLevel (a / q) (b / q) (j - 1)).card := by
  classical
  set A : Finset ℕ := omegaLevel a b j with hA
  set S1 : Finset ((_ : ℕ) × ℕ) := A.sigma (smallPowSet Q) with hS1
  set B : Finset ((_ : ℕ) × ℕ) :=
    ({q ∈ primePowerSet b b | q ≤ Q}).sigma
      fun q => omegaLevel (a / q) (b / q) (j - 1) with hB
  have hlow : ∀ n ∈ A, j - R ≤ (smallPowSet Q n).card := by
    intro n hn
    obtain ⟨hnmem, hncard⟩ := Finset.mem_filter.1 hn
    obtain ⟨han, hnb⟩ := Finset.mem_Ioc.1 hnmem
    have hn0 : n ≠ 0 := by omega
    exact card_smallPowSet_ge hn0 hnb hQ hR hncard
  have hcardS : (j - R) * A.card ≤ S1.card := by
    rw [hS1, Finset.card_sigma]
    calc (j - R) * A.card = ∑ _n ∈ A, (j - R) := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ n ∈ A, (smallPowSet Q n).card := Finset.sum_le_sum hlow
  have hcardB : B.card
      = ∑ q ∈ {q ∈ primePowerSet b b | q ≤ Q}, (omegaLevel (a / q) (b / q) (j - 1)).card := by
    rw [hB, Finset.card_sigma]
  set f : ((_ : ℕ) × ℕ) → ((_ : ℕ) × ℕ) :=
    fun x => ⟨x.2 ^ x.1.factorization x.2, x.1 / x.2 ^ x.1.factorization x.2⟩ with hf
  have hmaps : ∀ x ∈ S1, f x ∈ B := by
    rintro ⟨n, p⟩ hx
    simp only [hf]
    simp only [hS1, Finset.mem_sigma] at hx
    obtain ⟨hnA, hp'⟩ := hx
    rw [smallPowSet] at hp'
    obtain ⟨hp, hpQ⟩ := Finset.mem_filter.1 hp'
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
    refine Finset.mem_sigma.2 ⟨Finset.mem_filter.2 ⟨hqmem, hpQ⟩, ?_⟩
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
    obtain ⟨hnA, hp'⟩ := hx
    obtain ⟨hnA', hp''⟩ := hy
    rw [smallPowSet] at hp' hp''
    have hp := (Finset.mem_filter.1 hp').1
    have hp2 := (Finset.mem_filter.1 hp'').1
    obtain ⟨hnmem, -⟩ := Finset.mem_filter.1 hnA
    obtain ⟨hnmem', -⟩ := Finset.mem_filter.1 hnA'
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Ioc.1 hnmem).1; omega
    have hn0' : n' ≠ 0 := by
      have := (Finset.mem_Ioc.1 hnmem').1; omega
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hprime' : p'.Prime := Nat.prime_of_mem_primeFactors hp2
    have he : 0 < n.factorization p :=
      Nat.Prime.factorization_pos_of_dvd hprime hn0 (Nat.dvd_of_mem_primeFactors hp)
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
  have hfin := Finset.card_le_card_of_injOn f hmaps hinj
  omega

end RHTower.Sieve
