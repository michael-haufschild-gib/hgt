import GaloisForLFunctions.RHTower.Sieve.SelbergTail

/-!
# Integers with a large smooth part

The fibring of an interval over the `z`-smooth part costs one sieve error per fibre, so it is only
affordable while the smooth part stays small.  This module bounds the complementary set — the
integers of `Ioc a b` whose `z`-smooth part exceeds a cut `M` — without fibring.

The mechanism is a divisor window.  A `z`-smooth number exceeding `M` has a divisor in `(M, M z]`:
take the least divisor above `M`; dividing it by any of its prime factors lands at or below `M`,
so the divisor itself is at most `M` times a prime `≤ z`.  Hence every integer with a large smooth
part is a multiple of one member of the finite window set, and the count is the number of window
divisors times the number of multiples of each, which is at most `(b-a)/M + 1`.

Because the window divisors are smooth and inherit the prime-count restriction, their number is
governed by the same counting bound `card_smoothUpTo_card_primeFactors_le` used for the fibre index.
-/

namespace RHTower.Sieve

open Finset Nat

/-- **Divisor window.**  A number all of whose prime factors are at most `z` and which exceeds `M`
has a divisor in `(M, M z]`. -/
theorem exists_divisor_mem_Ioc_of_smooth {z M σ : ℕ} (hM : 1 ≤ M) (hσ : 0 < σ)
    (hsub : σ.primeFactors ⊆ Nat.primesLE z) (hlt : M < σ) :
    ∃ d, d ∣ σ ∧ M < d ∧ d ≤ M * z := by
  classical
  set S : Finset ℕ := {d ∈ σ.divisors | M < d} with hS
  have hσS : σ ∈ S := Finset.mem_filter.2 ⟨Nat.mem_divisors_self σ hσ.ne', hlt⟩
  have hne : S.Nonempty := ⟨σ, hσS⟩
  set d : ℕ := S.min' hne with hd
  have hdS : d ∈ S := S.min'_mem hne
  obtain ⟨hdmem, hdM⟩ := Finset.mem_filter.1 hdS
  have hdvd : d ∣ σ := Nat.dvd_of_mem_divisors hdmem
  have hd1 : 1 < d := by omega
  obtain ⟨p, hp⟩ := (Nat.nonempty_primeFactors (n := d)).2 hd1
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
  have hpσ : p ∈ σ.primeFactors :=
    Nat.mem_primeFactors.2 ⟨hpprime, hpd.trans hdvd, hσ.ne'⟩
  have hpz : p ≤ z := (Nat.mem_primesLE.1 (hsub hpσ)).1
  have hquot : d / p ∣ σ := (Nat.div_dvd_of_dvd hpd).trans hdvd
  have hqlt : d / p < d := Nat.div_lt_self (by omega) hpprime.one_lt
  have hqM : d / p ≤ M := by
    by_contra hcon
    have hqS : d / p ∈ S :=
      Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨hquot, hσ.ne'⟩, by omega⟩
    have := S.min'_le _ hqS
    omega
  refine ⟨d, hdvd, hdM, ?_⟩
  have hrecon : p * (d / p) = d := Nat.mul_div_cancel' hpd
  calc d = p * (d / p) := hrecon.symm
    _ ≤ z * M := Nat.mul_le_mul hpz hqM
    _ = M * z := by ring

/-- The window divisor set: smooth numbers in `(M, M z]` with at most `k` distinct prime factors. -/
def divisorWindow (z M k : ℕ) : Finset ℕ :=
  {d ∈ smoothUpTo (Nat.primesLE z) (M * z) | d.primeFactors.card ≤ k ∧ M < d}

theorem card_divisorWindow_le (z M k : ℕ) :
    (divisorWindow z M k).card
      ≤ ∑ j ∈ Finset.range (k + 1), ((Nat.primesLE z).card * Nat.log 2 (M * z)).choose j := by
  classical
  refine le_trans (Finset.card_le_card ?_) (card_smoothUpTo_card_primeFactors_le z (M * z) k)
  intro d hd
  obtain ⟨hmem, hcard, -⟩ := Finset.mem_filter.1 hd
  exact Finset.mem_filter.2 ⟨hmem, hcard⟩

/-- An integer with a large smooth part is a multiple of a window divisor. -/
theorem exists_window_divisor {z M k n : ℕ} (hM : 1 ≤ M) (hn : n ≠ 0)
    (hcard : n.primeFactors.card ≤ k) (hlt : M < smoothPart z n) :
    ∃ d ∈ divisorWindow z M k, d ∣ n := by
  classical
  set σ : ℕ := smoothPart z n with hσdef
  have hσpos : 0 < σ := smoothPart_pos z n
  have hσfac : σ.primeFactors = {p ∈ n.primeFactors | p ≤ z} := primeFactors_smoothPart hn z
  have hσsub : σ.primeFactors ⊆ Nat.primesLE z := by
    rw [hσfac]
    intro p hp
    obtain ⟨hpn, hpz⟩ := Finset.mem_filter.1 hp
    exact Nat.mem_primesLE.2 ⟨hpz, Nat.prime_of_mem_primeFactors hpn⟩
  obtain ⟨d, hdvd, hdM, hdle⟩ := exists_divisor_mem_Ioc_of_smooth hM hσpos hσsub hlt
  have hdn : d ∣ n := hdvd.trans (smoothPart_dvd z n)
  have hdsub : d.primeFactors ⊆ σ.primeFactors := Nat.primeFactors_mono hdvd hσpos.ne'
  have hσn : σ.primeFactors ⊆ n.primeFactors := by
    rw [hσfac]
    exact Finset.filter_subset _ _
  refine ⟨d, Finset.mem_filter.2 ⟨mem_smoothUpTo.2 ⟨⟨by omega, hdle⟩, hdsub.trans hσsub⟩,
    ?_, hdM⟩, hdn⟩
  exact le_trans (Finset.card_le_card (hdsub.trans hσn)) hcard

/-- **Large smooth part is rare.**  The integers of `Ioc a b` with at most `k` distinct prime
factors whose `z`-smooth part exceeds `M` number at most the size of the divisor window times the
number of multiples of a single window divisor. -/
theorem card_large_smoothPart_le (a b z k M : ℕ) (hM : 1 ≤ M) (hab : a ≤ b) :
    ((#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k ∧ M < smoothPart z n} : ℕ) : ℝ)
      ≤ (((b : ℝ) - a) / M + 1)
          * ∑ j ∈ Finset.range (k + 1),
              (((Nat.primesLE z).card * Nat.log 2 (M * z)).choose j : ℝ) := by
  classical
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hcover : {n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k ∧ M < smoothPart z n}
      ⊆ (divisorWindow z M k).biUnion fun d => {n ∈ Finset.Ioc a b | d ∣ n} := by
    intro n hn
    obtain ⟨hmem, hcard, hlt⟩ := Finset.mem_filter.1 hn
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Ioc.1 hmem).1
      omega
    obtain ⟨d, hdW, hdn⟩ := exists_window_divisor hM hn0 hcard hlt
    exact Finset.mem_biUnion.2 ⟨d, hdW, Finset.mem_filter.2 ⟨hmem, hdn⟩⟩
  have hnat : (#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k ∧ M < smoothPart z n})
      ≤ ∑ d ∈ divisorWindow z M k, (#{n ∈ Finset.Ioc a b | d ∣ n}) :=
    le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
  have hstart : ((#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k ∧ M < smoothPart z n} : ℕ) : ℝ)
      ≤ ∑ d ∈ divisorWindow z M k, ((#{n ∈ Finset.Ioc a b | d ∣ n} : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hterm : ∀ d ∈ divisorWindow z M k,
      ((#{n ∈ Finset.Ioc a b | d ∣ n} : ℕ) : ℝ) ≤ ((b : ℝ) - a) / M + 1 := by
    intro d hd
    obtain ⟨-, -, hdM⟩ := Finset.mem_filter.1 hd
    have hdpos : 0 < d := by omega
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have hMd : (M : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdM.le
    have habs := abs_card_filter_dvd_Ioc_sub_lt d a b hdpos hab
    have hle : ((b : ℝ) - a) / d ≤ ((b : ℝ) - a) / M :=
      div_le_div_of_nonneg_left hlen hMR hMd
    have := (abs_lt.1 habs).2
    linarith
  refine le_trans hstart (le_trans (Finset.sum_le_sum hterm) ?_)
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hpos : (0 : ℝ) ≤ ((b : ℝ) - a) / M + 1 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpos
  have := card_divisorWindow_le z M k
  exact_mod_cast this

end RHTower.Sieve
