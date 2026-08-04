import GaloisForLFunctions.RHTower.Sieve.MertensSecondSharp
import GaloisForLFunctions.RHTower.Sieve.SumCellMatching

/-!
# The reciprocal sum of a prime window, with decaying error

Subtracting two one-sided Mertens bounds adds their additive constants, which is fatal for a window
of bounded ratio.  With the sharp form the two errors are separate decaying terms:

`|∑_{z < p ≤ b} 1/p − (logLog b − logLog z)| ≤ C/log b + C/log z`,  `C = 2·mertensFirstConst + 1/2`.

Feeding this into the matching criterion replaces the fixed loss by one that vanishes as the marker
scale grows.
-/

namespace RHTower.Sieve

open Finset Nat

/-- **The reciprocal sum of a prime window, with decaying error.** -/
theorem abs_sum_inv_bigPrimeSet_sub_le {z b : ℕ} (hz : 2 ≤ z) (hzb : z ≤ b) :
    |∑ p ∈ bigPrimeSet z b, 1 / (p : ℝ) - (logLog b - logLog z)|
      ≤ (2 * mertensFirstConst + 1 / 2) / Real.log b
        + (2 * mertensFirstConst + 1 / 2) / Real.log z := by
  have hb : 2 ≤ b := le_trans hz hzb
  have hub := abs_mertensS_sub_logLog_sub_const_le hb
  have huz := abs_mertensS_sub_logLog_sub_const_le hz
  rw [sum_inv_bigPrimeSet z b hzb]
  have hrw : mertensS b - mertensS z - (logLog b - logLog z)
      = (mertensS b - logLog b - meisselMertensConst)
        - (mertensS z - logLog z - meisselMertensConst) := by ring
  rw [hrw]
  exact le_trans (abs_sub _ _) (add_le_add hub huz)

/-- **The reciprocal sum of a prime window, from below with decaying error.** -/
theorem sum_inv_bigPrimeSet_ge_sharp {z b : ℕ} (hz : 2 ≤ z) (hzb : z ≤ b) :
    logLog b - logLog z
        - ((2 * mertensFirstConst + 1 / 2) / Real.log b
          + (2 * mertensFirstConst + 1 / 2) / Real.log z)
      ≤ ∑ p ∈ bigPrimeSet z b, 1 / (p : ℝ) := by
  have h := abs_le.1 (abs_sum_inv_bigPrimeSet_sub_le hz hzb)
  linarith [h.1]

/-- **The matching criterion with the reciprocal sum as a parameter.** -/
theorem exists_hall_injection_recip {X H M Q z Y : ℕ} {S : ℝ}
    (hM : 3 ≤ M) (hXH : X + H ≤ M * M)
    (hS : S ≤ ∑ p ∈ bigPrimeSet M (Q * M), 1 / (p : ℝ))
    (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y)
    (hnum : 2 * (H : ℝ) / Real.log Y
        + ((Y * Y : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ))
      ≤ (H : ℝ) * S - ((Q * M : ℕ) : ℝ)) :
    ∃ f : ℕ → ℕ,
      Set.InjOn f ↑{p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p}
      ∧ (∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          f x ∈ RHTower.markerBlockTargets (bigPrimeSet M (Q * M)) (windowCell X H))
      ∧ ∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          |(f x : ℤ) - (x : ℤ)| ≤ (H : ℤ) := by
  classical
  have hppos : ∀ p ∈ bigPrimeSet M (Q * M), 0 < p := fun p hp =>
    (prime_of_mem_bigPrimeSet hp).pos
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
  · have hlen : ((X + H : ℕ) : ℝ) - (X : ℝ) = (H : ℝ) := by push_cast; ring
    have hbt := card_primes_Ioc_le_explicit X (X + H) z Y (Nat.le_add_right X H) hY hYz hz hlog
    rw [hlen] at hbt
    refine le_trans hbt (le_trans hnum ?_)
    refine le_trans ?_ (sum_card_windowCell_ge (X := X) (H := H) (bigPrimeSet M (Q * M)))
    have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    have hmul := mul_le_mul_of_nonneg_left hS hHnn
    have hcard := card_bigPrimeSet_le M (Q * M)
    linarith
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    exact hn.1

/-- **The matching criterion with a decaying Mertens loss.**  The constant obstruction of the
fixed-error form is replaced by `C/log(QM) + C/log M`, which vanishes as the marker scale grows. -/
theorem exists_hall_injection_sharp {X H M Q z Y : ℕ}
    (hM : 3 ≤ M) (hQ : 1 ≤ Q) (hXH : X + H ≤ M * M)
    (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y)
    (hnum : 2 * (H : ℝ) / Real.log Y
        + ((Y * Y : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ))
      ≤ (H : ℝ) * (logLog ((Q * M : ℕ)) - logLog M
            - ((2 * mertensFirstConst + 1 / 2) / Real.log ((Q * M : ℕ))
              + (2 * mertensFirstConst + 1 / 2) / Real.log M))
          - ((Q * M : ℕ) : ℝ)) :
    ∃ f : ℕ → ℕ,
      Set.InjOn f ↑{p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p}
      ∧ (∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          f x ∈ RHTower.markerBlockTargets (bigPrimeSet M (Q * M)) (windowCell X H))
      ∧ ∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          |(f x : ℤ) - (x : ℤ)| ≤ (H : ℤ) := by
  have hMQM : M ≤ Q * M := Nat.le_mul_of_pos_left M (by omega)
  exact exists_hall_injection_recip hM hXH
    (sum_inv_bigPrimeSet_ge_sharp (by omega) hMQM) hY hYz hz hlog hnum

end RHTower.Sieve
