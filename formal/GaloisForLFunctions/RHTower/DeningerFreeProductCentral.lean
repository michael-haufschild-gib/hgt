import GaloisForLFunctions.RHTower.DeningerFreeProductUniqueRoots

/-!
# Centralizers and isolation in a free product

Over the trivial base group the escape clause of the centralizer criterion says that the element
conjugates to the identity, so it is trivial.  Hence the centralizer of a nontrivial element of a
factor lies in that factor, and a cyclic subgroup isolated in a factor stays isolated in the free
product.

* `deningerFreeProduct_centralizer` : the centralizer of a factor element.
* `deningerFreeProduct_isolated` : isolation in a free product.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

variable {ι : Type u} {G : ι → Type u} {H : Type u} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- **The centralizer of a nontrivial element of a factor lies in that factor.** -/
theorem deningerFreeProduct_centralizer [Subsingleton H] (hφ : ∀ i, Function.Injective (φ i))
    (i : ι) (v : G i) (hv : v ≠ 1) (w : PushoutI φ)
    (hcomm : w * PushoutI.of (φ := φ) i v = PushoutI.of (φ := φ) i v * w) :
    ∃ x : G i, w = PushoutI.of (φ := φ) i x := by
  classical
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty φ hφ
  have hvr : v ∉ (φ i).range := by
    rintro ⟨k, hk⟩
    refine hv ?_
    rw [← hk, Subsingleton.elim k 1, map_one]
  obtain ⟨x, hx⟩ | ⟨x', k, hk⟩ := deningerCentralizer_factor (d := d) i v hvr w hcomm
  · exact ⟨x, hx⟩
  · exfalso
    refine hv ?_
    have h1 : x'⁻¹ * v * x' = 1 := by
      rw [hk, Subsingleton.elim k 1, map_one]
    have h2 : v = x' * 1 * x'⁻¹ := by
      rw [← h1]
      group
    rw [h2]
    group

/-- **Isolation in a free product.** -/
theorem deningerFreeProduct_isolated [Subsingleton H] (hφ : ∀ i, Function.Injective (φ i))
    (htor : ∀ (g : PushoutI φ) (m : ℕ), 0 < m → g ^ m = 1 → g = 1)
    (i : ι) (v : G i)
    (hvtor : ∀ c : ℤ, v ^ c = 1 → c = 0)
    (hiso : ∀ (y : G i) (m : ℕ), 0 < m → y ^ m ∈ Subgroup.zpowers v → y ∈ Subgroup.zpowers v)
    (y : PushoutI φ) (n : ℕ) (hn : 0 < n)
    (hy : y ^ n ∈ Subgroup.zpowers (PushoutI.of (φ := φ) i v)) :
    y ∈ Subgroup.zpowers (PushoutI.of (φ := φ) i v) := by
  classical
  obtain ⟨c, hc'⟩ := hy
  have hc : (PushoutI.of (φ := φ) i v) ^ c = y ^ n := hc'
  have hcof : PushoutI.of (φ := φ) i (v ^ c) = y ^ n := by
    rw [← hc]
    exact map_zpow (PushoutI.of (φ := φ) i) v c
  by_cases hc0 : c = 0
  · subst hc0
    rw [zpow_zero, map_one] at hcof
    exact ⟨0, by simp [htor y n hn hcof.symm]⟩
  · have hvc : v ^ c ≠ 1 := fun h => hc0 (hvtor c h)
    obtain ⟨x, hx⟩ := deningerFreeProduct_centralizer hφ i (v ^ c) hvc y (by
      rw [hcof]
      exact (Commute.refl y).pow_right n)
    have hxn : x ^ n = v ^ c := by
      refine PushoutI.of_injective hφ i ?_
      rw [map_pow, ← hx, ← hcof]
    obtain ⟨e, he⟩ := hiso x n hn ⟨c, hxn.symm⟩
    refine ⟨e, ?_⟩
    show (PushoutI.of (φ := φ) i v) ^ e = y
    rw [← map_zpow, hx]
    exact congrArg (PushoutI.of (φ := φ) i) he

end RHTower
