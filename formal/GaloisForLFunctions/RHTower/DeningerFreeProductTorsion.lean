import GaloisForLFunctions.RHTower.DeningerFreeProductCentral
import GaloisForLFunctions.RHTower.DeningerPushoutTorsion

/-!
# Free products of groups with unique roots

Unique roots imply torsion freeness, comparing an element with the identity, and the trivial base
group is torsion free, so an amalgam over it of groups with unique roots is torsion free.  The
hypothesis of torsion freeness can therefore be dropped from the theorem on unique roots in a free
product.

* `deningerFreeProduct_torsionFree` : a free product of groups with unique roots is torsion free.
* `deningerFreeProduct_uniqueRoots_of_factors` : free products preserve unique roots.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

variable {ι : Type u} {G : ι → Type u} {H : Type u} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
/-- **A free product of groups with unique roots is torsion free.** -/
theorem deningerFreeProduct_torsionFree [Subsingleton H] (hφ : ∀ i, Function.Injective (φ i))
    (hG : ∀ (i : ι) (a b : G i) (m : ℕ), 0 < m → a ^ m = b ^ m → a = b)
    (g : PushoutI φ) (n : ℕ) (hn : 0 < n) (hg : g ^ n = 1) : g = 1 :=
  deningerPushout_torsionFree hφ
    (fun i x m hm hx => hG i x 1 m hm (by rw [one_pow]; exact hx))
    (fun h m _ _ => Subsingleton.elim h 1) g n hn hg

/-- **Free products preserve unique roots**, with no further hypothesis. -/
theorem deningerFreeProduct_uniqueRoots_of_factors [Subsingleton H]
    (hφ : ∀ i, Function.Injective (φ i))
    (hG : ∀ (i : ι) (a b : G i) (m : ℕ), 0 < m → a ^ m = b ^ m → a = b)
    (x y : PushoutI φ) (n : ℕ) (h : x ^ (n + 1) = y ^ (n + 1)) : x = y :=
  deningerFreeProduct_uniqueRoots hφ hG
    (fun g m hm hgm => deningerFreeProduct_torsionFree hφ hG g m hm hgm) x y n h

end RHTower
