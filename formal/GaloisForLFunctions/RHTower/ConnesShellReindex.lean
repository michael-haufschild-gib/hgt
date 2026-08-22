import GaloisForLFunctions.RHTower.ConnesShellWindowMass

/-!
# §V (30) at a non-archimedean place: the substitution `u = xξ` is a shell reindexing

§V (29)-(30) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Step (30) substitutes `u = xξ` in the double integral of (29) and collects the resulting weight,
which at the archimedean place is `2 log' Λ − log|u|`.  At a non-archimedean place the module is
`q^{-n}`, so multiplication *adds* shell indices, and the substitution becomes the reindexing of a
double sum by the total index `k = n + m`.  The weight attached to `k` is then the number of ways
of splitting it inside the window — the exact discrete counterpart of `2 log' Λ − log|u|`.

Both halves are proved: the grouping of the double sum by total index, and the evaluation of the
splitting count as an interval of integers.
-/

open Finset

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The number of ways to write `k = n + m` with both parts in the window `[A, K]`. -/
theorem connes_shell_split_card (A K k : ℤ) :
    (((Finset.Icc A K) ×ˢ (Finset.Icc A K)).filter (fun p : ℤ × ℤ => p.1 + p.2 = k)).card
      = (Finset.Icc (max A (k - K)) (min K (k - A))).card := by
  refine Finset.card_bij' (fun p _ => p.1) (fun n _ => (n, k - n)) ?_ ?_ ?_ ?_
  · rintro ⟨n, m⟩ hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hp
    rw [Finset.mem_Icc, max_le_iff, le_min_iff]
    exact ⟨⟨h1, by omega⟩, h2, by omega⟩
  · intro n hn
    rw [Finset.mem_Icc, max_le_iff, le_min_iff] at hn
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hn
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨⟨h1, h3⟩, by omega, by omega⟩, by ring⟩
  · rintro ⟨n, m⟩ hp
    rw [Finset.mem_filter] at hp
    have : m = k - n := by omega
    simp [this]
  · intro n _
    rfl

/-- **§V (30) at a non-archimedean place.**  Grouping the product window by the total shell index
attaches to each `k` the number of ways of splitting it. -/
theorem connes_shell_product_window_sum (w : ℤ → ℂ) (A K : ℤ) :
    (∑ n ∈ Finset.Icc A K, ∑ m ∈ Finset.Icc A K, w (n + m))
      = ∑ k ∈ Finset.Icc (2 * A) (2 * K),
          ((Finset.Icc (max A (k - K)) (min K (k - A))).card : ℂ) * w k := by
  have hmaps : ∀ p ∈ (Finset.Icc A K) ×ˢ (Finset.Icc A K),
      p.1 + p.2 ∈ Finset.Icc (2 * A) (2 * K) := by
    rintro ⟨n, m⟩ hp
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
    rw [Finset.mem_Icc]
    omega
  have hprod : (∑ n ∈ Finset.Icc A K, ∑ m ∈ Finset.Icc A K, w (n + m))
      = ∑ p ∈ (Finset.Icc A K) ×ˢ (Finset.Icc A K), w (p.1 + p.2) :=
    (Finset.sum_product (s := Finset.Icc A K) (t := Finset.Icc A K)
      (f := fun p : ℤ × ℤ => w (p.1 + p.2))).symm
  rw [hprod, ← Finset.sum_fiberwise_of_maps_to hmaps (fun p : ℤ × ℤ => w (p.1 + p.2))]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hconst : (∑ p ∈ ((Finset.Icc A K) ×ˢ (Finset.Icc A K)).filter
      (fun p : ℤ × ℤ => p.1 + p.2 = k), w (p.1 + p.2))
      = ∑ _p ∈ ((Finset.Icc A K) ×ˢ (Finset.Icc A K)).filter
          (fun p : ℤ × ℤ => p.1 + p.2 = k), w k := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [hp.2]
  rw [hconst, Finset.sum_const, nsmul_eq_mul, connes_shell_split_card]

/-- The symmetric window `[-N, N]`: the splitting count at total index `k` is
`2N + 1 − |k|`, the discrete form of `2 log' Λ − log|u|`. -/
theorem connes_shell_split_card_symmetric (N : ℕ) {k : ℤ} (hk : |k| ≤ 2 * (N : ℤ)) :
    ((Finset.Icc (max (-(N : ℤ)) (k - N)) (min (N : ℤ) (k + N))).card : ℤ)
      = 2 * (N : ℤ) + 1 - |k| := by
  rw [Int.card_Icc]
  rcases abs_cases k with ⟨hkk, _⟩ | ⟨hkk, _⟩ <;> rw [hkk] <;>
    rcases le_total k 0 with h | h <;> simp only [max_def, min_def] <;> split_ifs <;> omega

end

end GaloisForLFunctions.RHTower
