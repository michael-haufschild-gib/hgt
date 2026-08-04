import GaloisForLFunctions.RHTower.Sieve.ConstructedMatching
import GaloisForLFunctions.RHTower.Sieve.SharedPrimeTail

/-!
# The block count as a sum over markers

Bounding every cell by the smallest one costs a factor of the marker range: the cells of a window
have size about `H/p`, and `∑_{M < p ≤ QM} H/p` is about `H·log(log QM / log M)`, whereas `#P` times
the smallest cell is only about `H(log Q)/(Q log M)`.

The block count is an exact sum over markers, so no such loss is necessary.  This module states the
matching with the sum, and evaluates it for the window cells using Mertens' second theorem.
-/

namespace RHTower.Sieve

open Finset Nat

/-- **The reciprocal sum of a window of primes, from below.** -/
theorem sum_inv_bigPrimeSet_ge {z b : ℕ} (hz : 2 ≤ z) (hzb : z ≤ b) :
    logLog b - logLog z - (mertensSecondLowerConst + mertensSecondUpperConst)
      ≤ ∑ p ∈ bigPrimeSet z b, 1 / (p : ℝ) := by
  have hb : 2 ≤ b := le_trans hz hzb
  have hlow := le_mertensS hb
  have hup := mertensS_le hz
  rw [sum_inv_bigPrimeSet z b hzb]
  linarith

/-- **The Hall injection with the block counted as a sum over markers.** -/
theorem exists_hall_injection_sum {X H : ℕ} (P : Finset ℕ) (C : ℕ → Finset ℕ) (sources : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hposC : ∀ p ∈ P, ∀ a ∈ C p, 0 < a)
    (hsmall : ∀ p ∈ P, ∀ a ∈ C p, ∀ r ∈ P, a < r)
    (hsrc : ((sources.card : ℕ) : ℝ) ≤ ∑ p ∈ P, (((C p).card : ℕ) : ℝ))
    (hw : ∀ p ∈ P, ∀ a ∈ C p, X < a * p ∧ a * p ≤ X + H)
    (hswin : ∀ n ∈ sources, X < n ∧ n ≤ X + H) :
    ∃ f : ℕ → ℕ, Set.InjOn f ↑sources
      ∧ (∀ x ∈ sources, f x ∈ RHTower.markerBlockTargets P C)
      ∧ ∀ x ∈ sources, |(f x : ℤ) - (x : ℤ)| ≤ (H : ℤ) := by
  classical
  have hexact : ((RHTower.markerBlockTargets P C).card : ℕ) = ∑ p ∈ P, (C p).card :=
    RHTower.card_markerBlockTargets P C hprime hposC hsmall
  have hcast : ((∑ p ∈ P, (C p).card : ℕ) : ℝ) = ∑ p ∈ P, (((C p).card : ℕ) : ℝ) := by
    push_cast
    ring
  have hcard : sources.card ≤ (RHTower.markerBlockTargets P C).card := by
    have hR : ((sources.card : ℕ) : ℝ)
        ≤ (((RHTower.markerBlockTargets P C).card : ℕ) : ℝ) := by
      rw [hexact, hcast]
      exact hsrc
    exact_mod_cast hR
  exact exists_injOn_displacement_le (X := X) (H := H) hcard hswin
    (markerBlockTargets_mem_window hw)

/-- **The window cells of a marker family, summed.** -/
theorem sum_card_windowCell_ge {X H : ℕ} (P : Finset ℕ) :
    (H : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) - (P.card : ℝ)
      ≤ ∑ p ∈ P, (((windowCell X H p).card : ℕ) : ℝ) := by
  classical
  have hterm : ∀ p ∈ P, (H : ℝ) / (p : ℝ) - 1
      ≤ (((windowCell X H p).card : ℕ) : ℝ) := by
    intro p _
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · rw [Nat.cast_zero, div_zero]
      have hnn : (0:ℝ) ≤ (((windowCell X H 0).card : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · exact le_of_lt (card_windowCell_gt X H p hp)
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hterm)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun p _ => by rw [mul_one_div]

/-- **The matching criterion with the block counted by Mertens' second theorem.**  The target
count is the reciprocal sum over the marker window, not the marker count times the smallest cell. -/
theorem exists_hall_injection_mertens {X H M Q z Y : ℕ}
    (hM : 3 ≤ M) (hQ : 1 ≤ Q) (hXH : X + H ≤ M * M)
    (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y)
    (hnum : 2 * (H : ℝ) / Real.log Y
        + ((Y * Y : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ))
      ≤ (H : ℝ) * (logLog ((Q * M : ℕ)) - logLog M
            - (mertensSecondLowerConst + mertensSecondUpperConst))
          - ((Q * M : ℕ) : ℝ)) :
    ∃ f : ℕ → ℕ,
      Set.InjOn f ↑{p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p}
      ∧ (∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          f x ∈ RHTower.markerBlockTargets (bigPrimeSet M (Q * M)) (windowCell X H))
      ∧ ∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          |(f x : ℤ) - (x : ℤ)| ≤ (H : ℤ) := by
  classical
  have hppos : ∀ p ∈ bigPrimeSet M (Q * M), 0 < p := fun p hp =>
    (prime_of_mem_bigPrimeSet hp).pos
  have hMQM : M ≤ Q * M := Nat.le_mul_of_pos_left M (by omega)
  refine exists_hall_injection_sum (X := X) (H := H) (bigPrimeSet M (Q * M)) (windowCell X H) _
    (fun p hp => prime_of_mem_bigPrimeSet hp)
    (fun p hp a ha => pos_of_mem_windowCell (hppos p hp) ha) ?_ ?_
    (fun p hp a ha => (mem_windowCell_iff (hppos p hp)).1 ha) ?_
  · intro p hp a ha r hr
    have hprod := ((mem_windowCell_iff (hppos p hp)).1 ha).2
    have hMp : M < p := lt_of_mem_bigPrimeSet hp
    have hMr : M < r := lt_of_mem_bigPrimeSet hr
    have haM : a ≤ M := by
      by_contra hcon
      have h1 : M + 1 ≤ a := by omega
      have h2 : M + 1 ≤ p := by omega
      have h3 : (M + 1) * (M + 1) ≤ a * p := Nat.mul_le_mul h1 h2
      have h4 : a * p ≤ M * M := le_trans hprod hXH
      nlinarith
    omega
  · -- the source bound falls below the summed block count
    have hlen : ((X + H : ℕ) : ℝ) - (X : ℝ) = (H : ℝ) := by push_cast; ring
    have hbt := card_primes_Ioc_le_explicit X (X + H) z Y (Nat.le_add_right X H) hY hYz hz hlog
    rw [hlen] at hbt
    refine le_trans hbt (le_trans hnum ?_)
    refine le_trans ?_ (sum_card_windowCell_ge (X := X) (H := H) (bigPrimeSet M (Q * M)))
    have hsum := sum_inv_bigPrimeSet_ge (z := M) (b := Q * M) (by omega) hMQM
    have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    have hmul := mul_le_mul_of_nonneg_left hsum hHnn
    have hcard := card_bigPrimeSet_le M (Q * M)
    linarith
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    exact hn.1

end RHTower.Sieve
