import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiDivergentCapacityAntichainPackets

/-!
# Prime-capacity classification of native Fermi observability on dyadic antichains

For a set `Π` of odd primes, consider every coefficient packet seen through a
finite horizon whose active indices form a dyadic antichain (no odd part at two
valuations) and whose active odd parts have all prime factors in `Π`. With the
native reciprocal-pronic sieve energy `P` and selected Fermi energy `Q`, the
following are equivalent:

1. one constant `C` gives `P ≤ C Q` for every such packet;
2. one constant `C` gives `P ≤ C Q` for every nonnegative such packet;
3. `∑_{p ∈ Π} 1/p` converges;
4. the finite reciprocal subsums of `Π` are bounded.

The bounded case uses the explicit constant `8 exp(6M)`. In the divergent case,
disjoint prime banks give nonnegative antichain packets with `P ≥ (L-1)/2` and
`0 < Q < 5/6` for every `L ≥ 2`. A final version needs no hypothesis on the
allowed set: only its odd primes are visible to the odd parts.
-/

open scoped BigOperators
open Finset GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

/-- For a set of naturals, bounded finite reciprocal subsums are equivalent to summability. -/
theorem summable_reciprocal_iff_bounded_finite_subsums (A : Set ℕ) :
    Summable (fun p : A => 1 / (p : ℝ)) ↔
      ∃ M : ℝ, ∀ P : Finset ℕ, (∀ p ∈ P, p ∈ A) → ∑ p ∈ P, 1 / (p : ℝ) ≤ M := by
  classical
  constructor
  · intro hs
    refine ⟨∑' p : A, 1 / (p : ℝ), fun P hP => ?_⟩
    rw [← Finset.sum_subtype_of_mem (fun p : ℕ => 1 / (p : ℝ)) hP]
    exact hs.sum_le_tsum _ (fun p _ => by positivity)
  · rintro ⟨M, hM⟩
    refine summable_of_sum_le (c := M) (fun p => by positivity) (fun u => ?_)
    have h := hM (u.map (Function.Embedding.subtype _)) (fun p hp => by
      obtain ⟨q, -, rfl⟩ := Finset.mem_map.mp hp
      exact q.2)
    rwa [Finset.sum_map] at h

/-- Unbounded reciprocal capacity forbids a uniform bound even on nonnegative packets. -/
theorem fermiDyadicAntichain_bounded_capacity_of_nonneg_bound (Pi : Set ℕ)
    (hPi : ∀ p ∈ Pi, p.Prime ∧ Odd p) {C : ℝ}
    (hC : ∀ (N : ℕ) (c : ℕ → ℝ), fermiDyadicAntichainAdmissible Pi N c → (∀ n, 0 ≤ c n) →
      sieveTotalPronicEnergy N c ≤ C * fermiSelectedTotalPronicEnergy N c) :
    ∃ M : ℝ, ∀ P : Finset ℕ, (∀ p ∈ P, p ∈ Pi) → ∑ p ∈ P, 1 / (p : ℝ) ≤ M := by
  by_contra hcap
  have hdiv : ∀ M : ℝ, ∃ P : Finset ℕ, (∀ p ∈ P, p ∈ Pi) ∧ M < ∑ p ∈ P, 1 / (p : ℝ) := by
    intro M
    by_contra h
    exact hcap ⟨M, fun P hP => not_lt.mp (fun hlt => h ⟨P, hP, hlt⟩)⟩
  set m := max C 0
  set L := ⌈2 * m⌉₊ + 2
  obtain ⟨N, c, hadm, hnn, hP, hQ0, hQ1⟩ :=
    exists_fermiDyadicAntichain_divergentCapacity_packet Pi hPi hdiv (L := L) (by omega)
  have hL : 2 * m + 2 ≤ (L : ℝ) := by
    have := Nat.le_ceil (2 * m)
    simp only [L, Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hm0 : 0 ≤ m := le_max_right C 0
  have hCQ : C * fermiSelectedTotalPronicEnergy N c ≤ m * (5 / 6) :=
    calc
      C * fermiSelectedTotalPronicEnergy N c ≤ m * fermiSelectedTotalPronicEnergy N c :=
        mul_le_mul_of_nonneg_right (le_max_left C 0) hQ0.le
      _ ≤ m * (5 / 6) := mul_le_mul_of_nonneg_left hQ1.le hm0
  have := hC N c hadm hnn
  linarith

/-- **Theorem A.** Native Fermi observability on dyadic antichains over a set `Π` of
odd primes is uniform exactly when `Π` has finite reciprocal capacity. -/
theorem fermiDyadicAntichain_primeCapacity_classification (Pi : Set ℕ)
    (hPi : ∀ p ∈ Pi, p.Prime ∧ Odd p) :
    List.TFAE
      [∃ C : ℝ, ∀ (N : ℕ) (c : ℕ → ℝ), fermiDyadicAntichainAdmissible Pi N c →
          sieveTotalPronicEnergy N c ≤ C * fermiSelectedTotalPronicEnergy N c,
        ∃ C : ℝ, ∀ (N : ℕ) (c : ℕ → ℝ), fermiDyadicAntichainAdmissible Pi N c →
          (∀ n, 0 ≤ c n) → sieveTotalPronicEnergy N c ≤ C * fermiSelectedTotalPronicEnergy N c,
        Summable (fun p : Pi => 1 / (p : ℝ)),
        ∃ M : ℝ, ∀ P : Finset ℕ, (∀ p ∈ P, p ∈ Pi) → ∑ p ∈ P, 1 / (p : ℝ) ≤ M] := by
  tfae_have 1 → 2 := fun ⟨C, hC⟩ => ⟨C, fun N c hc _ => hC N c hc⟩
  tfae_have 2 → 4 := fun ⟨C, hC⟩ =>
    fermiDyadicAntichain_bounded_capacity_of_nonneg_bound Pi hPi hC
  tfae_have 4 → 1 := fun ⟨M, hM⟩ =>
    ⟨8 * Real.exp (6 * M), fun N c hc =>
      fermiDyadicAntichainAdmissible_boundedCapacity_physical_bound Pi hPi M hM N c hc⟩
  tfae_have 3 ↔ 4 := summable_reciprocal_iff_bounded_finite_subsums Pi
  tfae_finish

private theorem odd_part_prime_factor {n p : ℕ} (hn : n ≠ 0)
    (hp : p ∈ (n / 2 ^ n.factorization 2).primeFactors) : p.Prime ∧ Odd p := by
  obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  refine ⟨hpp, hpp.odd_of_ne_two (fun h2 => ?_)⟩
  subst h2
  exact Nat.not_dvd_ordCompl Nat.prime_two hn hdvd

/-- Only the odd primes of an allowed set are visible to admissible odd parts. -/
theorem fermiDyadicAntichainAdmissible_iff_oddPrimes (A : Set ℕ) (N : ℕ) (c : ℕ → ℝ) :
    fermiDyadicAntichainAdmissible A N c ↔
      fermiDyadicAntichainAdmissible {p | p ∈ A ∧ p.Prime ∧ Odd p} N c := by
  constructor
  · rintro ⟨hanti, hprime⟩
    refine ⟨hanti, fun n hn hc p hp => ⟨hprime n hn hc p hp, odd_part_prime_factor ?_ hp⟩⟩
    have := (Finset.mem_Icc.mp hn).1
    omega
  · rintro ⟨hanti, hprime⟩
    exact ⟨hanti, fun n hn hc p hp => (hprime n hn hc p hp).1⟩

/-- **Theorem A for an arbitrary allowed set.** Uniform native observability on admissible
dyadic antichains, signed or nonnegative, holds exactly when the reciprocals of the odd
primes of the allowed set are summable. -/
theorem fermiDyadicAntichain_oddPrimeCapacity_classification (A : Set ℕ) :
    List.TFAE
      [∃ C : ℝ, ∀ (N : ℕ) (c : ℕ → ℝ), fermiDyadicAntichainAdmissible A N c →
          sieveTotalPronicEnergy N c ≤ C * fermiSelectedTotalPronicEnergy N c,
        ∃ C : ℝ, ∀ (N : ℕ) (c : ℕ → ℝ), fermiDyadicAntichainAdmissible A N c →
          (∀ n, 0 ≤ c n) → sieveTotalPronicEnergy N c ≤ C * fermiSelectedTotalPronicEnergy N c,
        Summable (fun p : {p : ℕ | p ∈ A ∧ p.Prime ∧ Odd p} => 1 / (p : ℝ))] := by
  have h := fermiDyadicAntichain_primeCapacity_classification {p | p ∈ A ∧ p.Prime ∧ Odd p}
    (fun p hp => hp.2)
  simp only [← fermiDyadicAntichainAdmissible_iff_oddPrimes] at h
  tfae_have 1 ↔ 3 := h.out 0 2
  tfae_have 2 ↔ 3 := h.out 1 2
  tfae_finish

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
