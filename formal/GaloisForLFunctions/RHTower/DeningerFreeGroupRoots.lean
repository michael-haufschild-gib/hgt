import GaloisForLFunctions.RHTower.DeningerFreeGroupAmalgam

/-!
# A free group has unique roots

Transporting the theorem on free products along the identification of a free group with an amalgam
of infinite cyclic groups over the trivial group gives the classical fact that a free group has
unique roots, and with it torsion freeness.

* `deningerFreeGroup_uniqueRoots` : a free group has unique roots.
* `deningerFreeGroup_torsionFree` : a free group is torsion free.
-/

namespace RHTower

open Monoid Monoid.PushoutI RootAdjunction

universe u

/-- **A free group has unique roots.** -/
theorem deningerFreeGroup_uniqueRoots (ι : Type u) (x y : FreeGroup ι) (n : ℕ) (hn : 0 < n)
    (h : x ^ n = y ^ n) : x = y := by
  classical
  refine deningerUniqueRoots_of_mulEquiv (deningerFreeGroupEquiv ι).symm ?_ x y n hn h
  intro a b k hk hab
  exact deningerFreeProduct_uniqueRoots_of_factors
    (fun _ p q _ => Subsingleton.elim p q)
    (fun _ p q j hj hpq => deningerUliftInt_pow_inj p q j hj hpq)
    a b (k - 1) (by rw [show k - 1 + 1 = k by omega]; exact hab)

/-- **A free group is torsion free.** -/
theorem deningerFreeGroup_torsionFree (ι : Type u) (x : FreeGroup ι) (n : ℕ) (hn : 0 < n)
    (h : x ^ n = 1) : x = 1 :=
  deningerFreeGroup_uniqueRoots ι x 1 n hn (by rw [one_pow]; exact h)

end RHTower
