import GaloisForLFunctions.RHTower.Deninger.DeningerStepEmbed

/-!
# Unique roots pass to a union of a chain

A group covered by an increasing chain of subgroups, each with unique roots, has unique roots: two
elements with the same power lie in a common member of the chain, where the property applies.  The
chain is presented by a compatible family of injections, which is what a colimit of the tower
supplies.

* `deningerChain_le` : the images of the chain increase.
* `deningerUniqueRoots_of_chain` : unique roots pass to the union.
-/

namespace RHTower

universe u

variable {K : Type u} [Group K] {C : ℕ → Type u} [∀ n, Group (C n)]

/-- **The images of the chain increase.** -/
theorem deningerChain_le (f : ∀ n, C n →* K)
    (hstep : ∀ (n : ℕ) (x : C n), ∃ y : C (n + 1), f (n + 1) y = f n x)
    (n m : ℕ) (hnm : n ≤ m) (x : C n) : ∃ y : C m, f m y = f n x := by
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨x, rfl⟩
  | succ m hm ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨z, hz⟩ := hstep m y
    exact ⟨z, by rw [hz, hy]⟩

/-- **Unique roots pass to the union of a chain.** -/
theorem deningerUniqueRoots_of_chain (f : ∀ n, C n →* K)
    (hstep : ∀ (n : ℕ) (x : C n), ∃ y : C (n + 1), f (n + 1) y = f n x)
    (hinj : ∀ n, Function.Injective (f n))
    (hcover : ∀ x : K, ∃ (n : ℕ) (a : C n), f n a = x)
    (hU : ∀ (n : ℕ) (a b : C n) (k : ℕ), 0 < k → a ^ k = b ^ k → a = b)
    (x y : K) (k : ℕ) (hk : 0 < k) (h : x ^ k = y ^ k) : x = y := by
  obtain ⟨n₁, a, ha⟩ := hcover x
  obtain ⟨n₂, b, hb⟩ := hcover y
  obtain ⟨a', ha'⟩ := deningerChain_le f hstep n₁ (max n₁ n₂) (le_max_left _ _) a
  obtain ⟨b', hb'⟩ := deningerChain_le f hstep n₂ (max n₁ n₂) (le_max_right _ _) b
  have hx : f (max n₁ n₂) a' = x := by rw [ha', ha]
  have hy : f (max n₁ n₂) b' = y := by rw [hb', hb]
  have hpow : a' ^ k = b' ^ k := by
    refine hinj (max n₁ n₂) ?_
    rw [map_pow, map_pow, hx, hy]
    exact h
  rw [← hx, ← hy, hU (max n₁ n₂) a' b' k hk hpow]

end RHTower
