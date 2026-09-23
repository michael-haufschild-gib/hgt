import GaloisForLFunctions.RHTower.Sieve.MertensFirstBlock
import GaloisForLFunctions.RHTower.Sieve.SquarefreeHarmonic

/-!
# The tail sum `∑_p 1/(p log p)` is bounded

Grouping the primes by dyadic size, `k = Nat.log 2 p`, the fibre at `k` satisfies `2^k ≤ p < 2^{k+1}`, so
`log p ≥ k log 2` and

`1/(p log p) ≤ ((log p)/p)/(k log 2)²`.

For `k ≥ 2` the fibre sits inside the dyadic block `(2^k, 2^{k+1}]` — the endpoint `2^k` is not prime —
whose mass is bounded by `mertensBlockConst` uniformly in `k`; for `k = 1` the fibre sits inside
`primesLE 4`, whose mass is at most `2 log 4` by Mertens' upper bound.  Summing `1/k²` over the fibres
gives an absolute bound.

This is the quantity that made the frequency-average error of `UniformDistanceAverage` read
`O(logLog z/T)` instead of `O(1/T)`; with it the average of the distance over `[0,T]` is
`∑_{p ∈ P}1/p + O(1/T)`, so the uniform distance is the prime mass up to an error that vanishes with the
height.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- The absolute bound for the tail sum. -/
noncomputable def primeInvLogConst : ℝ :=
  2 * (max mertensBlockConst (2 * Real.log 4)) / (Real.log 2) ^ (2 : ℕ)

/-- **One dyadic fibre of the tail sum.** -/
theorem sum_fiber_inv_mul_log_le {x : ℕ} {k : ℕ} (hk : 1 ≤ k) :
    ∑ p ∈ Finset.filter (fun p => Nat.log 2 p = k) (Nat.primesLE x),
        1 / ((p : ℝ) * Real.log (p : ℝ))
      ≤ (max mertensBlockConst (2 * Real.log 4)) / ((k : ℝ) * Real.log 2) ^ (2 : ℕ) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) * Real.log 2 := by positivity
  -- the pointwise comparison on the fibre
  have hpt : ∀ p ∈ Finset.filter (fun p => Nat.log 2 p = k) (Nat.primesLE x),
      1 / ((p : ℝ) * Real.log (p : ℝ))
        ≤ (Real.log (p : ℝ) / (p : ℝ)) / ((k : ℝ) * Real.log 2) ^ (2 : ℕ) := by
    intro p hp
    rw [Finset.mem_filter, Nat.mem_primesLE] at hp
    have hprime := hp.1.2
    have hp2 : 2 ≤ p := hprime.two_le
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp : (0 : ℝ) < Real.log (p : ℝ) := Real.log_pos (by linarith)
    have hpow : 2 ^ k ≤ p := by
      have := Nat.pow_log_le_self 2 (show p ≠ 0 by omega)
      rwa [hp.2] at this
    have hklog : (k : ℝ) * Real.log 2 ≤ Real.log (p : ℝ) := by
      have hcast : ((2 ^ k : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpow
      have hlogle : Real.log ((2 ^ k : ℕ) : ℝ) ≤ Real.log (p : ℝ) :=
        Real.log_le_log (by positivity) hcast
      have hval : Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      rwa [hval] at hlogle
    have hsq : ((k : ℝ) * Real.log 2) ^ (2 : ℕ) ≤ (Real.log (p : ℝ)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hkpos.le hklog 2
    have hrhs : (Real.log (p : ℝ) / (p : ℝ)) / (((k : ℝ) * Real.log 2) ^ (2 : ℕ))
        = Real.log (p : ℝ) / ((p : ℝ) * (((k : ℝ) * Real.log 2) ^ (2 : ℕ))) := by
      rw [div_div]
    rw [hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsq, hp0, hlogp]
  refine le_trans (Finset.sum_le_sum hpt) ?_
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  -- the mass of the fibre
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · have hk1' : k = 1 := by omega
    have hsubset : Finset.filter (fun p => Nat.log 2 p = k) (Nat.primesLE x)
        ⊆ Nat.primesLE 4 := by
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primesLE] at hp
      rw [Nat.mem_primesLE]
      refine ⟨?_, hp.1.2⟩
      have hlt := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) p
      rw [hp.2, hk1'] at hlt
      omega
    have hnn : ∀ p ∈ Nat.primesLE 4,
        p ∉ Finset.filter (fun p => Nat.log 2 p = k) (Nat.primesLE x) →
        0 ≤ Real.log (p : ℝ) / (p : ℝ) := by
      intro p hp _
      rw [Nat.mem_primesLE] at hp
      have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.one_lt.le
      positivity
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset hnn) ?_
    refine le_trans (mertensFirst_upper (n := 4) (by norm_num)) ?_
    have hval : Real.log ((4 : ℕ) : ℝ) + Real.log 4 = 2 * Real.log 4 := by
      norm_num
      ring
    rw [hval]
    exact le_max_right _ _
  · have hsubset : Finset.filter (fun p => Nat.log 2 p = k) (Nat.primesLE x)
        ⊆ Nat.primesLE (2 ^ (k + 1)) \ Nat.primesLE (2 ^ k) := by
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primesLE] at hp
      have hprime := hp.1.2
      have hp2 : 2 ≤ p := hprime.two_le
      have hpow : 2 ^ k ≤ p := by
        have := Nat.pow_log_le_self 2 (show p ≠ 0 by omega)
        rwa [hp.2] at this
      have hlt := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) p
      rw [hp.2] at hlt
      have hne : p ≠ 2 ^ k := by
        intro heq
        have h4 : 4 ≤ p := by
          have : (4 : ℕ) = 2 ^ (2 : ℕ) := by norm_num
          rw [heq, this]
          exact Nat.pow_le_pow_right (by norm_num) hk2
        have hdvd : 2 ∣ p := by
          rw [heq]
          exact dvd_pow_self 2 (by omega)
        have := (Nat.Prime.eq_one_or_self_of_dvd hprime 2 hdvd)
        omega
      rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
      refine ⟨⟨by omega, hprime⟩, ?_⟩
      intro hmem
      exact hne (le_antisymm hmem.1 hpow)
    have hnn : ∀ p ∈ Nat.primesLE (2 ^ (k + 1)) \ Nat.primesLE (2 ^ k),
        p ∉ Finset.filter (fun p => Nat.log 2 p = k) (Nat.primesLE x) →
        0 ≤ Real.log (p : ℝ) / (p : ℝ) := by
      intro p hp _
      rw [Finset.mem_sdiff, Nat.mem_primesLE] at hp
      have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1.2.one_lt.le
      positivity
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset hnn)
      (le_trans (sum_prime_log_div_block_le k) (le_max_left _ _))

/-- **The tail sum is bounded by an absolute constant.**  Summing the dyadic fibres against `1/k²`. -/
theorem sum_prime_inv_mul_log_le (x : ℕ) :
    ∑ p ∈ Nat.primesLE x, 1 / ((p : ℝ) * Real.log (p : ℝ)) ≤ primeInvLogConst := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set C : ℝ := max mertensBlockConst (2 * Real.log 4) with hC
  have hC0 : (0 : ℝ) ≤ C := le_trans mertensBlockConst_nonneg (le_max_left _ _)
  set K : ℕ := Nat.log 2 x with hK
  -- every prime in the range lands in a fibre indexed by `[1, K]`
  have hmaps : ∀ p ∈ Nat.primesLE x, Nat.log 2 p ∈ Finset.Icc 1 K := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    rw [Finset.mem_Icc]
    have hp2 : 2 ≤ p := hp.2.two_le
    refine ⟨?_, ?_⟩
    · have h := Nat.log_mono_right (b := 2) hp2
      have hone : Nat.log 2 2 = 1 := by
        decide
      rw [hone] at h
      exact h
    · exact Nat.log_mono_right hp.1
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun p => 1 / ((p : ℝ) * Real.log (p : ℝ)))
  rw [← hfib]
  -- each fibre against `1/k²`
  have hterm : ∀ k ∈ Finset.Icc 1 K,
      ∑ p ∈ Finset.filter (fun p => Nat.log 2 p = k) (Nat.primesLE x),
          1 / ((p : ℝ) * Real.log (p : ℝ))
        ≤ (C / (Real.log 2) ^ (2 : ℕ)) * (1 / (k : ℝ) ^ (2 : ℕ)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hb := sum_fiber_inv_mul_log_le (x := x) hk.1
    refine le_trans hb (le_of_eq ?_)
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    have hk0 : (k : ℝ) ≠ 0 := by linarith
    rw [hC]
    field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsq := sum_inv_sq_le_two K
  have hcoef : (0 : ℝ) ≤ C / (Real.log 2) ^ (2 : ℕ) := by positivity
  have hstep := mul_le_mul_of_nonneg_left hsq hcoef
  rw [primeInvLogConst, hC]
  calc (C / (Real.log 2) ^ (2 : ℕ)) * ∑ k ∈ Finset.Icc 1 K, 1 / (k : ℝ) ^ (2 : ℕ)
      ≤ (C / (Real.log 2) ^ (2 : ℕ)) * 2 := hstep
    _ = 2 * C / (Real.log 2) ^ (2 : ℕ) := by ring

end RHTower.Sieve
end
