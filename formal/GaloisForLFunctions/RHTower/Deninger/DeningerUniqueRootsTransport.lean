import GaloisForLFunctions.RHTower.Deninger.DeningerFreeProductTorsion

/-!
# Unique roots transport along an isomorphism

Unique roots, torsion freeness and divisibility are properties of the isomorphism class of a group.
Transporting them is what identifies a group given by a construction with one given by a universal
property.

* `deningerUniqueRoots_of_mulEquiv` : unique roots transport.
* `deningerTorsionFree_of_mulEquiv` : torsion freeness transports.
* `deningerDivisible_of_mulEquiv` : divisibility transports.
-/

namespace RHTower

universe u v

variable {G : Type u} {K : Type v} [Group G] [Group K]

/-- **Unique roots transport along an isomorphism.** -/
theorem deningerUniqueRoots_of_mulEquiv (e : G ≃* K)
    (hG : ∀ (a b : G) (n : ℕ), 0 < n → a ^ n = b ^ n → a = b)
    (x y : K) (n : ℕ) (hn : 0 < n) (h : x ^ n = y ^ n) : x = y := by
  have hxy : (e.symm x) ^ n = (e.symm y) ^ n := by
    rw [← map_pow, ← map_pow, h]
  have := hG _ _ n hn hxy
  simpa using congrArg e this

/-- **Torsion freeness transports along an isomorphism.** -/
theorem deningerTorsionFree_of_mulEquiv (e : G ≃* K)
    (hG : ∀ (a : G) (n : ℕ), 0 < n → a ^ n = 1 → a = 1)
    (x : K) (n : ℕ) (hn : 0 < n) (h : x ^ n = 1) : x = 1 := by
  have hx : (e.symm x) ^ n = 1 := by
    rw [← map_pow, h, map_one]
  have := hG _ n hn hx
  simpa using congrArg e this

/-- **Divisibility transports along an isomorphism.** -/
theorem deningerDivisible_of_mulEquiv (e : G ≃* K)
    (hG : ∀ (a : G) (N : ℤ), N ≠ 0 → ∃ b : G, b ^ N = a)
    (x : K) (N : ℤ) (hN : N ≠ 0) : ∃ y : K, y ^ N = x := by
  obtain ⟨b, hb⟩ := hG (e.symm x) N hN
  refine ⟨e b, ?_⟩
  rw [← map_zpow, hb]
  simp

end RHTower
