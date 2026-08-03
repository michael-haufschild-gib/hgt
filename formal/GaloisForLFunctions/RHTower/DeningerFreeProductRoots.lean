import GaloisForLFunctions.RHTower.DeningerRootFactor

/-!
# Roots in a free product

Over the trivial base group, isolation is exactly torsion freeness: an element with a power in the
trivial subgroup is trivial.  So in a free product of torsion free groups with unique roots, the
elements of the factors have unique roots.

* `deningerPow_eq_of_factors_freeProduct` : uniqueness of roots for elements of the factors of a
  free product.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

variable {ι : Type u} {G : ι → Type u} [∀ i, Group (G i)]
  {φ : ∀ i, PUnit.{u + 1} →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **Uniqueness of roots for elements of the factors of a free product** of torsion free groups
with unique roots. -/
theorem deningerPow_eq_of_factors_freeProduct (hφ : ∀ i, Function.Injective (φ i))
    (htf : ∀ (i : ι) (x : G i) (n : ℕ), 0 < n → x ^ n = 1 → x = 1)
    (hG : ∀ (i : ι) (a b : G i) (n : ℕ), 0 < n → a ^ n = b ^ n → a = b)
    (i j : ι) (a : G i) (b : G j) (n : ℕ) (hn : 0 < n)
    (h : (PushoutI.of (φ := φ) i a) ^ n = (PushoutI.of (φ := φ) j b) ^ n) :
    PushoutI.of (φ := φ) i a = PushoutI.of (φ := φ) j b := by
  classical
  refine deningerPow_eq_of_factors (d := d) hφ ?_ ?_ hG i j a b n hn h
  · intro l x m hm hx
    obtain ⟨u, hu⟩ := hx
    refine ⟨1, ?_⟩
    have hx1 : x ^ m = 1 := by
      rw [← hu]
      exact congrArg (φ l) (Subsingleton.elim u 1) |>.trans (map_one (φ l))
    rw [htf l x m hm hx1, map_one]
  · intro s t m _ _
    exact Subsingleton.elim s t

end RHTower
