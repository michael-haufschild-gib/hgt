import GaloisForLFunctions.RHTower.Sieve.ElementaryHarmonicBounds

/-!
# The unsigned squarefree harmonic estimates

The Route E cofactor card's `(7)` and `(9)` need a *lower* bound for the harmonic and square-root
mass of the squarefree integers below `M` that avoid a prescribed set of primes.  Both follow from
one elementary inclusion–exclusion, provided the excluded primes carry less than the full mass:

* every `n` not coprime to `Q` is a multiple of a prime factor of `Q`, and the multiples of `p`
  carry at most `1/p` of the mass;
* every non-squarefree `n` coprime to an even `Q` is a multiple of the square of an odd prime, and
  the odd reciprocal squares sum to at most `1/4`.

With `∑_{p ∣ Q} 1/p ≤ 5/8` — one half from the prime `2`, the rest from the card's polylogarithmic
band, whose Mertens mass is `o(1)` — the two残 constants are positive:

```text
∑_{n ≤ M, (n,Q)=1, μ²(n)=1} 1/n     ≥ (log M)/8 − 7/8 ,
∑_{n ≤ M, (n,Q)=1, μ²(n)=1} n^{-1/2} ≥ √M/4 − 2 .
```

No sieve and no prime-counting theorem is used.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- A nonnegative sum over a union of fibres is at most the sum of the fibre sums. -/
theorem sum_biUnion_le_of_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → Finset ℕ)
    (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s.biUnion t, f i ≤ ∑ p ∈ s, ∑ i ∈ t p, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hun : ∑ i ∈ t a ∪ s.biUnion t, f i
        ≤ ∑ i ∈ t a, f i + ∑ i ∈ s.biUnion t, f i := by
      have h := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
      have hnn : (0 : ℝ) ≤ ∑ i ∈ t a ∩ s.biUnion t, f i :=
        Finset.sum_nonneg fun i _ => hf i
      linarith
    linarith [hun, ih]

/-- Every integer that is not coprime to `Q` is a multiple of a prime factor of `Q`. -/
theorem notCoprime_subset_biUnion {M Q : ℕ} (hQ : Q ≠ 0) :
    (Finset.Icc 1 M).filter (fun n => ¬ Nat.Coprime n Q)
      ⊆ Q.primeFactors.biUnion (fun p => (Finset.Icc 1 M).filter (fun n => p ∣ n)) := by
  classical
  intro n hn
  rw [Finset.mem_filter] at hn
  obtain ⟨hmem, hcop⟩ := hn
  have hg : Nat.gcd n Q ≠ 1 := hcop
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
  have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_left n Q)
  have hpQ : p ∣ Q := hpg.trans (Nat.gcd_dvd_right n Q)
  refine Finset.mem_biUnion.2 ⟨p, ?_, ?_⟩
  · exact Nat.mem_primeFactors.2 ⟨hp, hpQ, hQ⟩
  · exact Finset.mem_filter.2 ⟨hmem, hpn⟩

/-- **The coprime part of a nonnegative sum, from below.** -/
theorem sum_coprime_ge {M Q : ℕ} (hQ : Q ≠ 0) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ n ∈ Finset.Icc 1 M, f n
        - ∑ p ∈ Q.primeFactors, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => p ∣ n), f n
      ≤ ∑ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.Coprime n Q), f n := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M)
    (fun n => Nat.Coprime n Q) f
  have hbad : ∑ n ∈ (Finset.Icc 1 M).filter (fun n => ¬ Nat.Coprime n Q), f n
      ≤ ∑ p ∈ Q.primeFactors, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => p ∣ n), f n := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (notCoprime_subset_biUnion hQ)
      (fun i _ _ => hf i)) ?_
    exact sum_biUnion_le_of_nonneg _ _ f hf
  linarith [hsplit, hbad]

/-- Every non-squarefree integer coprime to an even modulus is a multiple of the square of an odd
prime below the range. -/
theorem notSquarefree_subset_biUnion {M Q : ℕ} (hQ2 : 2 ∣ Q) :
    (Finset.Icc 1 M).filter (fun n => Nat.Coprime n Q ∧ ¬ Squarefree n)
      ⊆ ((Finset.Icc 3 M).filter Nat.Prime).biUnion
          (fun p => (Finset.Icc 1 M).filter (fun n => p * p ∣ n)) := by
  classical
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hn1, hnM⟩, hcop, hsq⟩ := hn
  have hex : ∃ p, Nat.Prime p ∧ p * p ∣ n := by
    by_contra hcon
    push Not at hcon
    exact hsq (Nat.squarefree_iff_prime_squarefree.2 fun x hx => hcon x hx)
  obtain ⟨p, hp, hpp⟩ := hex
  have hpn : p ∣ n := dvd_trans (Dvd.intro p rfl) hpp
  have hp2 : p ≠ 2 := by
    intro hp2'
    subst hp2'
    have hdvd : (2 : ℕ) ∣ Nat.gcd n Q := Nat.dvd_gcd hpn hQ2
    have h1 : (2 : ℕ) ∣ 1 := hcop ▸ hdvd
    omega
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpM : p ≤ M := by
    have hple : p * p ≤ n := Nat.le_of_dvd (by omega) hpp
    nlinarith [hp.two_le, hnM, hple]
  refine Finset.mem_biUnion.2 ⟨p, ?_, ?_⟩
  · exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hp3, hpM⟩, hp⟩
  · exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hn1, hnM⟩, hpp⟩

/-- The odd primes of the covering carry at most `1/4` of the reciprocal squares. -/
theorem sum_inv_sq_coveringPrimes_le (M : ℕ) :
    ∑ p ∈ (Finset.Icc 3 M).filter Nat.Prime, 1 / ((p : ℝ)) ^ 2 ≤ 1 / 4 := by
  classical
  refine sum_inv_sq_odd_le ?_
  intro d hd
  rw [Finset.mem_filter, Finset.mem_Icc] at hd
  refine ⟨hd.1.1, ?_⟩
  intro h2
  have hd2 : d = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hd.2).1 h2).symm
  omega

/-- The non-squarefree part of a nonnegative sum, from above. -/
theorem sum_notSquarefree_le {M Q : ℕ} (hQ2 : 2 ∣ Q) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.Coprime n Q ∧ ¬ Squarefree n), f n
      ≤ ∑ p ∈ (Finset.Icc 3 M).filter Nat.Prime,
          ∑ n ∈ (Finset.Icc 1 M).filter (fun n => p * p ∣ n), f n := by
  classical
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (notSquarefree_subset_biUnion hQ2)
    (fun i _ _ => hf i)) ?_
  exact sum_biUnion_le_of_nonneg _ _ f hf

/-- **`(9)`: the harmonic mass of the squarefree integers coprime to `Q`.** -/
theorem sum_inv_coprime_squarefree_ge {M Q : ℕ} (hQ0 : Q ≠ 0) (hQ2 : 2 ∣ Q) (hM : 1 ≤ M)
    (hQsum : ∑ p ∈ Q.primeFactors, 1 / (p : ℝ) ≤ 5 / 8) :
    (1 / 8 : ℝ) * Real.log (M : ℝ) - 7 / 8
      ≤ ∑ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.Coprime n Q ∧ Squarefree n),
          1 / (n : ℝ) := by
  classical
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlogM : (0 : ℝ) ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
  have hf : ∀ i : ℕ, (0 : ℝ) ≤ 1 / (i : ℝ) := fun i => by positivity
  -- the full harmonic sum from below
  have hfull : Real.log (M : ℝ) ≤ ∑ n ∈ Finset.Icc 1 M, 1 / (n : ℝ) := by
    have h := Aux.log_le_sum_inv (M : ℝ) hM1
    rw [Nat.floor_natCast] at h
    simpa [one_div] using h
  -- the mass removed by the prime factors of `Q`
  have hbad : ∑ p ∈ Q.primeFactors, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => p ∣ n), 1 / (n : ℝ)
      ≤ (1 + Real.log (M : ℝ)) * (5 / 8) := by
    have hterm : ∀ p ∈ Q.primeFactors,
        ∑ n ∈ (Finset.Icc 1 M).filter (fun n => p ∣ n), 1 / (n : ℝ)
          ≤ (1 + Real.log (M : ℝ)) * (1 / (p : ℝ)) := by
      intro p hp
      have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le.trans' (by norm_num)
      have := sum_inv_dvd_le (M := M) (p := p) hp1 hM
      have heq : (1 + Real.log (M : ℝ)) / (p : ℝ) = (1 + Real.log (M : ℝ)) * (1 / (p : ℝ)) := by
        ring
      linarith [this, heq.le, heq.ge]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hQsum (by linarith)
  have hcop := sum_coprime_ge (M := M) (Q := Q) hQ0 (fun n => 1 / (n : ℝ)) hf
  -- the non-squarefree part
  have hnsq : ∑ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.Coprime n Q ∧ ¬ Squarefree n),
        1 / (n : ℝ)
      ≤ (1 + Real.log (M : ℝ)) * (1 / 4) := by
    refine le_trans (sum_notSquarefree_le hQ2 (fun n => 1 / (n : ℝ)) hf) ?_
    have hterm : ∀ p ∈ (Finset.Icc 3 M).filter Nat.Prime,
        ∑ n ∈ (Finset.Icc 1 M).filter (fun n => p * p ∣ n), 1 / (n : ℝ)
          ≤ (1 + Real.log (M : ℝ)) * (1 / ((p : ℝ)) ^ 2) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      have hpp1 : 1 ≤ p * p := by nlinarith [hp.1.1]
      have hstep := sum_inv_dvd_le (M := M) (p := p * p) hpp1 hM
      have hcast : (((p * p : ℕ)) : ℝ) = ((p : ℝ)) ^ 2 := by push_cast; ring
      rw [hcast] at hstep
      have heq : (1 + Real.log (M : ℝ)) / ((p : ℝ)) ^ 2
          = (1 + Real.log (M : ℝ)) * (1 / ((p : ℝ)) ^ 2) := by ring
      linarith [hstep, heq.le, heq.ge]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_inv_sq_coveringPrimes_le M) (by linarith)
  -- split the coprime sum by squarefreeness
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 M).filter (fun n => Nat.Coprime n Q)) (fun n => Squarefree n)
    (fun n => 1 / (n : ℝ))
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  linarith [hfull, hbad, hcop, hnsq, hsplit]

/-- **`(7)`: the square-root mass of the squarefree integers coprime to `Q`.** -/
theorem sum_inv_sqrt_coprime_squarefree_ge {M Q : ℕ} (hQ0 : Q ≠ 0) (hQ2 : 2 ∣ Q)
    (hQsum : ∑ p ∈ Q.primeFactors, 1 / (p : ℝ) ≤ 5 / 8) :
    (1 / 4 : ℝ) * Real.sqrt (M : ℝ) - 2
      ≤ ∑ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.Coprime n Q ∧ Squarefree n),
          1 / Real.sqrt (n : ℝ) := by
  classical
  have hsM : (0 : ℝ) ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
  have hf : ∀ i : ℕ, (0 : ℝ) ≤ 1 / Real.sqrt (i : ℝ) := fun i => by positivity
  -- the full square-root sum from below
  have hfull : 2 * Real.sqrt (M : ℝ) - 2 ≤ ∑ n ∈ Finset.Icc 1 M, 1 / Real.sqrt (n : ℝ) := by
    have h := two_mul_sqrt_succ_sub_two_le_sum M
    have hmono : Real.sqrt (M : ℝ) ≤ Real.sqrt ((M : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith [h, hmono]
  -- the mass removed by the prime factors of `Q`
  have hbad : ∑ p ∈ Q.primeFactors,
        ∑ n ∈ (Finset.Icc 1 M).filter (fun n => p ∣ n), 1 / Real.sqrt (n : ℝ)
      ≤ (2 * Real.sqrt (M : ℝ)) * (5 / 8) := by
    have hterm : ∀ p ∈ Q.primeFactors,
        ∑ n ∈ (Finset.Icc 1 M).filter (fun n => p ∣ n), 1 / Real.sqrt (n : ℝ)
          ≤ (2 * Real.sqrt (M : ℝ)) * (1 / (p : ℝ)) := by
      intro p hp
      have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le.trans' (by norm_num)
      have hstep := sum_inv_sqrt_dvd_le (M := M) (p := p) hp1
      have heq : 2 * Real.sqrt (M : ℝ) / (p : ℝ) = (2 * Real.sqrt (M : ℝ)) * (1 / (p : ℝ)) := by
        ring
      linarith [hstep, heq.le, heq.ge]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hQsum (by positivity)
  have hcop := sum_coprime_ge (M := M) (Q := Q) hQ0 (fun n => 1 / Real.sqrt (n : ℝ)) hf
  -- the non-squarefree part
  have hnsq : ∑ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.Coprime n Q ∧ ¬ Squarefree n),
        1 / Real.sqrt (n : ℝ)
      ≤ (2 * Real.sqrt (M : ℝ)) * (1 / 4) := by
    refine le_trans (sum_notSquarefree_le hQ2 (fun n => 1 / Real.sqrt (n : ℝ)) hf) ?_
    have hterm : ∀ p ∈ (Finset.Icc 3 M).filter Nat.Prime,
        ∑ n ∈ (Finset.Icc 1 M).filter (fun n => p * p ∣ n), 1 / Real.sqrt (n : ℝ)
          ≤ (2 * Real.sqrt (M : ℝ)) * (1 / ((p : ℝ)) ^ 2) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      have hpp1 : 1 ≤ p * p := by nlinarith [hp.1.1]
      have hstep := sum_inv_sqrt_dvd_le (M := M) (p := p * p) hpp1
      have hcast : (((p * p : ℕ)) : ℝ) = ((p : ℝ)) ^ 2 := by push_cast; ring
      rw [hcast] at hstep
      have heq : 2 * Real.sqrt (M : ℝ) / ((p : ℝ)) ^ 2
          = (2 * Real.sqrt (M : ℝ)) * (1 / ((p : ℝ)) ^ 2) := by ring
      linarith [hstep, heq.le, heq.ge]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_inv_sq_coveringPrimes_le M) (by positivity)
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 M).filter (fun n => Nat.Coprime n Q)) (fun n => Squarefree n)
    (fun n => 1 / Real.sqrt (n : ℝ))
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  linarith [hfull, hbad, hcop, hnsq, hsplit]

end

end RHTower.Sieve
