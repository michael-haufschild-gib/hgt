import GaloisForLFunctions.RHTower.Sieve.WindowMatching
import GaloisForLFunctions.RHTower.Sieve.PrimeWindow

/-!
# The matching criterion with the marker supply supplied internally

Taking the markers to be all primes of a ratio window `(M, QM]` makes the marker count itself a
consequence of Mertens' first theorem rather than a hypothesis.  Two further conditions become
elementary: every marker exceeds `M`, so cofactors bounded by `M` are automatically smaller than
every marker.

What is left is a single inequality between elementary functions of `H, Y, z, M, Q` and the cell
size `c`.
-/

namespace RHTower.Sieve

open Finset Nat BoundingSieve

/-- Every member of a big-prime set exceeds the cut. -/
theorem lt_of_mem_bigPrimeSet {z b p : ℕ} (hp : p ∈ bigPrimeSet z b) : z < p := by
  rw [bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
  omega

/-- **The matching criterion with the markers taken to be a whole ratio window of primes.** -/
theorem exists_hall_injection_bigPrime {X H M Q z Y : ℕ} (C : ℕ → Finset ℕ)
    (hM : 3 ≤ M) (hQ : 1 ≤ Q)
    (hposC : ∀ p ∈ bigPrimeSet M (Q * M), ∀ a ∈ C p, 0 < a)
    (hleC : ∀ p ∈ bigPrimeSet M (Q * M), ∀ a ∈ C p, a ≤ M)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ p ∈ bigPrimeSet M (Q * M), c ≤ (((C p).card : ℕ) : ℝ))
    (hw : ∀ p ∈ bigPrimeSet M (Q * M), ∀ a ∈ C p, X < a * p ∧ a * p ≤ X + H)
    (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y)
    (hnum : 2 * (H : ℝ) / Real.log Y
        + ((Y * Y : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ))
      ≤ (Real.log Q - 2 * mertensFirstConst) * (M : ℝ) / Real.log M * c) :
    ∃ f : ℕ → ℕ,
      Set.InjOn f ↑{p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p}
      ∧ (∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          f x ∈ RHTower.markerBlockTargets (bigPrimeSet M (Q * M)) C)
      ∧ ∀ x ∈ {p ∈ Finset.Ioc X (X + H) | p.Prime ∧ z < p},
          |(f x : ℤ) - (x : ℤ)| ≤ (H : ℤ) := by
  classical
  have hsupply := card_bigPrimeSet_ratio_ge hM hQ
  have hnum' : 2 * (H : ℝ) / Real.log Y
      + ((Y * Y : ℕ) : ℝ)
          * (Real.exp (4 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ))
      ≤ (((bigPrimeSet M (Q * M)).card : ℕ) : ℝ) * c :=
    le_trans hnum (mul_le_mul_of_nonneg_right hsupply hc0)
  refine exists_hall_injection_primes_of_cells (bigPrimeSet M (Q * M)) C
    (fun p hp => prime_of_mem_bigPrimeSet hp) hposC ?_ hc hw hY hYz hz hlog hnum'
  intro p hp a ha r hr
  exact lt_of_le_of_lt (hleC p hp a ha) (lt_of_mem_bigPrimeSet hr)

end RHTower.Sieve
