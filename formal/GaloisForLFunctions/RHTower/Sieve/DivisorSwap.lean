import Mathlib

/-!
# The divisor swap, and Halász's recursion

Reindexing a divisor sum by the quotient:

`∑_{m ≤ N} ∑_{d ∣ m} G(d, m/d) = ∑_{d ≤ N} ∑_{k ≤ N/d} G(d, k)`,

the bijection being `(m, d) ↦ (d, m/d)` with inverse `(d, k) ↦ (dk, d)`.  This is the general form
of the counting swap; the constant-summand case is the one that gives `∑_{m ≤ n} log m =
∑_{d ≤ n} Λ(d)⌊n/d⌋`.

Applied to `Λ(d) f(d) f(k)` with `f` completely multiplicative it gives Halász's recursion

`∑_{m ≤ N} f(m) log m = ∑_{d ≤ N} Λ(d) f(d) ∑_{k ≤ N/d} f(k)`,

which expresses the log-weighted sum of `f` through the unweighted sums of `f` on the shorter ranges
`N/d`.  This is the identity the whole mean-value theory turns on: it is what converts a bound on
`f` at primes into a recursion for its partial sums.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **The divisor swap.** -/
theorem sum_divisors_swap {M : Type*} [AddCommMonoid M] (N : ℕ) (G : ℕ → ℕ → M) :
    ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ m.divisors, G d (m / d)
      = ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 (N / d), G d k := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1 / x.2⟩) (fun x => ⟨x.1 * x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, d⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hm1, hmN⟩, hdm, _⟩ := hx
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdm (by omega)
    refine ⟨⟨hd0, le_trans (Nat.le_of_dvd (by omega) hdm) hmN⟩, ?_, ?_⟩
    · exact (Nat.one_le_div_iff hd0).mpr (Nat.le_of_dvd (by omega) hdm)
    · exact Nat.div_le_div_right hmN
  · rintro ⟨d, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hd1, hdN⟩, hk1, hkN⟩ := hx
    have hd0 : 0 < d := hd1
    have hdk : d * k ≤ N := by
      have h := (Nat.le_div_iff_mul_le hd0).mp hkN
      rwa [Nat.mul_comm] at h
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), hdk⟩, Dvd.intro k rfl, by positivity⟩
  · rintro ⟨m, d⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
    obtain ⟨⟨hm1, _⟩, hdm, _⟩ := hx
    simp [Nat.mul_div_cancel' hdm]
  · rintro ⟨d, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx
    obtain ⟨⟨hd1, _⟩, _, _⟩ := hx
    simp [Nat.mul_div_cancel_left k (show 0 < d from hd1)]
  · rintro ⟨m, d⟩ _
    rfl

/-- **Halász's recursion for a completely multiplicative function.** -/
theorem sum_mul_log_eq_vonMangoldt {f : ℕ → ℂ} (hf : ∀ a b : ℕ, f (a * b) = f a * f b) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, f m * (Real.log m : ℂ)
      = ∑ d ∈ Finset.Icc 1 N, ((Λ d : ℝ) : ℂ) * f d * ∑ k ∈ Finset.Icc 1 (N / d), f k := by
  have hpt : ∀ m ∈ Finset.Icc 1 N,
      f m * (Real.log m : ℂ) = ∑ d ∈ m.divisors, ((Λ d : ℝ) : ℂ) * f d * f (m / d) := by
    intro m hm
    have hlog : ∑ d ∈ m.divisors, Λ d = Real.log m := vonMangoldt_sum
    calc f m * (Real.log m : ℂ)
        = f m * ((∑ d ∈ m.divisors, Λ d : ℝ) : ℂ) := by rw [hlog]
      _ = ∑ d ∈ m.divisors, ((Λ d : ℝ) : ℂ) * f m := by
          push_cast
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun d _ => by ring
      _ = ∑ d ∈ m.divisors, ((Λ d : ℝ) : ℂ) * f d * f (m / d) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          rw [Nat.mem_divisors] at hd
          rw [mul_assoc, ← hf d (m / d), Nat.mul_div_cancel' hd.1]
  calc ∑ m ∈ Finset.Icc 1 N, f m * (Real.log m : ℂ)
      = ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ m.divisors, ((Λ d : ℝ) : ℂ) * f d * f (m / d) :=
        Finset.sum_congr rfl hpt
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 (N / d), ((Λ d : ℝ) : ℂ) * f d * f k :=
        sum_divisors_swap N fun d k => ((Λ d : ℝ) : ℂ) * f d * f k
    _ = ∑ d ∈ Finset.Icc 1 N, ((Λ d : ℝ) : ℂ) * f d * ∑ k ∈ Finset.Icc 1 (N / d), f k :=
        Finset.sum_congr rfl fun d _ => (Finset.mul_sum _ _ _).symm

end RHTower.Sieve
