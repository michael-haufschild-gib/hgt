import GaloisForLFunctions.RHTower.Deninger.DeningerFactorEltDisjoint
import GaloisForLFunctions.RHTower.Deninger.DeningerAmalgamRoots

/-!
# A free product of groups with unique roots has unique roots

A free product is an amalgam over the trivial group, and every hypothesis the amalgam theorem places
on the base group is automatic there: the trivial group is abelian, torsion free, has unique roots,
is not moved by conjugation, and has no nontrivial element to be centralized.  So a torsion free
free product of groups with unique roots has unique roots — not only on the elements of the factors,
but on all of them.

* `deningerFreeProduct_uniqueRoots` : unique roots in a free product.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

variable {ι : Type u} {G : ι → Type u} {H : Type u} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- **Unique roots in a free product.** -/
theorem deningerFreeProduct_uniqueRoots [Subsingleton H] (hφ : ∀ i, Function.Injective (φ i))
    (hG : ∀ (i : ι) (a b : G i) (m : ℕ), 0 < m → a ^ m = b ^ m → a = b)
    (htor : ∀ (g : PushoutI φ) (m : ℕ), 0 < m → g ^ m = 1 → g = 1)
    (x y : PushoutI φ) (n : ℕ) (h : x ^ (n + 1) = y ^ (n + 1)) : x = y := by
  classical
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty φ hφ
  exact deningerAmalgam_pow_inj (d := d) hφ (fun _ _ u v _ => Subsingleton.elim v u)
    (fun _ _ v hv _ => absurd (Subsingleton.elim v 1) hv)
    (fun _ _ => Subsingleton.elim _ _)
    (fun u _ _ _ => Subsingleton.elim u 1)
    (fun a b _ _ _ => Subsingleton.elim a b) hG htor x y n h

end RHTower
