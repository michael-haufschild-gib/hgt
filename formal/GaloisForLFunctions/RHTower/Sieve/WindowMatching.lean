import GaloisForLFunctions.RHTower.Sieve.HallInjection
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowUpper

/-!
# Matching the primes of a window into a marker block

Both sides of the matching step are now sieve statements about the same window `(X, X + H]`: the
primes above `z` are bounded above by Brun–Titchmarsh, and the marker block is bounded below by
unique decoding.  When the first bound falls below the second, the primes inject into the block
without moving further than `H`.

Only the numerical comparison between the two bounds is left as a hypothesis; everything else is
proved.
-/

namespace RHTower.Sieve

open Finset Nat BoundingSieve

/-- **The primes of a window match into a marker block.** -/
theorem exists_hall_injection_primes {X H z Y : ℕ} (P : Finset ℕ) (C : ℕ → Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hposC : ∀ p ∈ P, ∀ a ∈ C p, 0 < a)
    (hsmall : ∀ p ∈ P, ∀ a ∈ C p, ∀ r ∈ P, a < r)
    {c : ℝ} (hc : ∀ p ∈ P, c ≤ (((C p).card : ℕ) : ℝ))
    (hY : 1 ≤ Y) (hYz : Y ≤ z) (hlog : 0 < Real.log Y)
    (hnum : 2 * (H : ℝ) / Real.log Y
        + ∑ d ∈ (primorial z).divisors,
            |lambdaSquared (selbergTruncWeight (intervalSieve X (X + H) z) Y) d|
      ≤ (P.card : ℝ) * c)
    (htwin : ∀ n ∈ RHTower.markerBlockTargets P C, X < n ∧ n ≤ X + H) :
    ∃ f : ℕ → ℕ,
      Set.InjOn f ↑{p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p}
      ∧ (∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          f x ∈ RHTower.markerBlockTargets P C)
      ∧ ∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          |(f x : ℤ) - (x : ℤ)| ≤ (H : ℤ) := by
  classical
  have hlen : ((X + H : ℕ) : ℝ) - (X : ℝ) = (H : ℝ) := by push_cast; ring
  have hsrc : ((({p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p}).card : ℕ) : ℝ)
      ≤ (P.card : ℝ) * c := by
    refine le_trans ?_ hnum
    have hbt := card_primes_Ioc_le_log X (X + H) z Y (Nat.le_add_right X H) hY hYz hlog
    rwa [hlen] at hbt
  refine exists_hall_injection (X := X) (H := H) P C _ hprime hposC hsmall hc hsrc htwin ?_
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
  exact hn.1

/-- **The matching criterion in elementary terms.**  The only hypothesis about sizes compares two
elementary functions of the parameters: the Brun–Titchmarsh bound on the primes of the window, and
the block bound `#P · c` on the targets. -/
theorem exists_hall_injection_primes_explicit {X H z Y : ℕ} (P : Finset ℕ) (C : ℕ → Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hposC : ∀ p ∈ P, ∀ a ∈ C p, 0 < a)
    (hsmall : ∀ p ∈ P, ∀ a ∈ C p, ∀ r ∈ P, a < r)
    {c : ℝ} (hc : ∀ p ∈ P, c ≤ (((C p).card : ℕ) : ℝ))
    (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y)
    (hnum : 2 * (H : ℝ) / Real.log Y
        + ((Y * Y : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ))
      ≤ (P.card : ℝ) * c)
    (htwin : ∀ n ∈ RHTower.markerBlockTargets P C, X < n ∧ n ≤ X + H) :
    ∃ f : ℕ → ℕ,
      Set.InjOn f ↑{p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p}
      ∧ (∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          f x ∈ RHTower.markerBlockTargets P C)
      ∧ ∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          |(f x : ℤ) - (x : ℤ)| ≤ (H : ℤ) := by
  classical
  have hlen : ((X + H : ℕ) : ℝ) - (X : ℝ) = (H : ℝ) := by push_cast; ring
  have hsrc : ((({p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p}).card : ℕ) : ℝ)
      ≤ (P.card : ℝ) * c := by
    refine le_trans ?_ hnum
    have hbt := card_primes_Ioc_le_explicit X (X + H) z Y (Nat.le_add_right X H) hY hYz hz hlog
    rwa [hlen] at hbt
  refine exists_hall_injection (X := X) (H := H) P C _ hprime hposC hsmall hc hsrc htwin ?_
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
  exact hn.1

/-- **The matching criterion on construction data alone.**  Every hypothesis is a condition on the
marker family `P` and the cofactor cells `C` that a construction can verify directly: the markers
are prime, the cofactors are positive, smaller than every marker, at least `c` in number, and each
product lands in the window. -/
theorem exists_hall_injection_primes_of_cells {X H z Y : ℕ} (P : Finset ℕ) (C : ℕ → Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hposC : ∀ p ∈ P, ∀ a ∈ C p, 0 < a)
    (hsmall : ∀ p ∈ P, ∀ a ∈ C p, ∀ r ∈ P, a < r)
    {c : ℝ} (hc : ∀ p ∈ P, c ≤ (((C p).card : ℕ) : ℝ))
    (hw : ∀ p ∈ P, ∀ a ∈ C p, X < a * p ∧ a * p ≤ X + H)
    (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y)
    (hnum : 2 * (H : ℝ) / Real.log Y
        + ((Y * Y : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ))
      ≤ (P.card : ℝ) * c) :
    ∃ f : ℕ → ℕ,
      Set.InjOn f ↑{p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p}
      ∧ (∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          f x ∈ RHTower.markerBlockTargets P C)
      ∧ ∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          |(f x : ℤ) - (x : ℤ)| ≤ (H : ℤ) :=
  exists_hall_injection_primes_explicit P C hprime hposC hsmall hc hY hYz hz hlog hnum
    (markerBlockTargets_mem_window hw)

end RHTower.Sieve
