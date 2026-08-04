import GaloisForLFunctions.RHTower.Sieve.TotientSquareSum

/-!
# The distinct-product bound for balanced pairs

Specialising the Cauchy–Schwarz image bound to a family of balanced pairs.  A pair `(d, e)` with
`d ∈ [y, 2y]` is determined by its product `m = de` together with `d`, and `d ∣ m`, so each fibre
injects into the balanced divisors of `m`:

`#{p ∈ S : p₁p₂ = m} ≤ #{d ∣ m : y ≤ d ≤ 2y}`.

Hence the second moment of the fibre sizes is at most the second moment of the balanced divisor
count, and

`#{distinct products} ≥ (#S)² / V`

for any `V` bounding that second moment.  With `V = O(X log y)` from the preceding modules this is
the passage from a representation count to a physical-product count.
-/

namespace RHTower.Sieve

open Finset

/-- Each product fibre injects into the balanced divisors of the product. -/
theorem card_fibre_le_card_divisors {y : ℕ} (hy : 1 ≤ y) (S : Finset (ℕ × ℕ))
    (hd : ∀ p ∈ S, p.1 ∈ Finset.Icc y (2 * y)) (m : ℕ) :
    ((S.filter (fun p => p.1 * p.2 = m)).card)
      ≤ (((Finset.Icc y (2 * y)).filter (fun d => d ∣ m)).card) := by
  classical
  refine Finset.card_le_card_of_injOn (fun p => p.1) ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter] at hp ⊢
    exact ⟨hd p hp.1, ⟨p.2, hp.2.symm⟩⟩
  · intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
    simp only at hpq
    obtain ⟨hpS, hpm⟩ := hp
    obtain ⟨hqS, hqm⟩ := hq
    have hp1 : 0 < p.1 := by
      have := hd p hpS
      rw [Finset.mem_Icc] at this
      omega
    have hprod : p.1 * p.2 = q.1 * q.2 := by rw [hpm, hqm]
    rw [hpq] at hprod hp1
    have : p.2 = q.2 := Nat.eq_of_mul_eq_mul_left hp1 hprod
    exact Prod.ext hpq this

/-- **The distinct-product bound for balanced pairs.** -/
theorem card_image_mul_ge {y X : ℕ} (hy : 1 ≤ y) (S : Finset (ℕ × ℕ)) {V : ℝ} (hV : 0 < V)
    (hd : ∀ p ∈ S, p.1 ∈ Finset.Icc y (2 * y))
    (himg : ∀ p ∈ S, p.1 * p.2 ∈ Finset.Icc 1 X)
    (hbound : ∑ m ∈ Finset.Icc 1 X,
        ((((Finset.Icc y (2 * y)).filter (fun d => d ∣ m)).card : ℕ) : ℝ) ^ 2 ≤ V) :
    ((S.card : ℕ) : ℝ) ^ 2 / V
      ≤ (((S.image (fun p => p.1 * p.2)).card : ℕ) : ℝ) := by
  classical
  refine card_image_ge_of_sum_sq_le S (fun p => p.1 * p.2) hV ?_
  have hsub : S.image (fun p => p.1 * p.2) ⊆ Finset.Icc 1 X := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨p, hp, rfl⟩ := hm
    exact himg p hp
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => by positivity) ?_
  refine le_trans (Finset.sum_le_sum ?_) hbound
  intro m _
  have hcard := card_fibre_le_card_divisors hy S hd m
  have hcast : (((S.filter (fun p => p.1 * p.2 = m)).card : ℕ) : ℝ)
      ≤ ((((Finset.Icc y (2 * y)).filter (fun d => d ∣ m)).card : ℕ) : ℝ) := by
    exact_mod_cast hcard
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcast 2

end RHTower.Sieve
