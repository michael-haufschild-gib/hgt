import GaloisForLFunctions.RHTower.DeningerFreeGroupRoots

/-!
# The centralizer of a basis element of a free group

Under the identification of a free group with an amalgam of infinite cyclic groups, a basis element
is the generator of its factor, which is nontrivial, so the centralizer criterion for free products
places anything commuting with it inside that factor — the powers of the basis element.

* `deningerRootGen_ne_one` : the generator is nontrivial.
* `deningerFreeGroup_centralizer` : the centralizer of a basis element.
-/

namespace RHTower

open Monoid Monoid.PushoutI RootAdjunction

universe u

/-- **The generator of the infinite cyclic group is nontrivial.** -/
theorem deningerRootGen_ne_one : deningerRootGen.{u} ≠ 1 := by
  intro h
  have h1 : Multiplicative.toAdd (MulEquiv.ulift deningerRootGen.{u}) = 0 := by
    rw [h]
    simp
  rw [deningerRootGen] at h1
  simp at h1

/-- **The centralizer of a basis element of a free group is the cyclic subgroup it generates.** -/
theorem deningerFreeGroup_centralizer (ι : Type u) (i : ι) (w : FreeGroup ι)
    (hcomm : w * FreeGroup.of i = FreeGroup.of i * w) :
    w ∈ Subgroup.zpowers (FreeGroup.of i) := by
  classical
  have hEq : deningerFreeGroupEquiv ι (FreeGroup.of i) =
      PushoutI.of (φ := deningerFreeMap ι) i deningerRootGen.{u} :=
    deningerFreeToPushout_of ι i
  have hcomm' : deningerFreeGroupEquiv ι w *
      PushoutI.of (φ := deningerFreeMap ι) i deningerRootGen.{u} =
      PushoutI.of (φ := deningerFreeMap ι) i deningerRootGen.{u} *
      deningerFreeGroupEquiv ι w := by
    rw [← hEq, ← map_mul, ← map_mul, hcomm]
  obtain ⟨x, hx⟩ := deningerFreeProduct_centralizer
    (φ := deningerFreeMap ι) (fun _ p q _ => Subsingleton.elim p q) i deningerRootGen.{u}
    deningerRootGen_ne_one (deningerFreeGroupEquiv ι w) hcomm'
  obtain ⟨c, hc⟩ : ∃ c : ℤ, deningerRootGen.{u} ^ c = x :=
    ⟨Multiplicative.toAdd (MulEquiv.ulift x), deningerFreeFactor_zpow ι i x⟩
  refine ⟨c, ?_⟩
  show (FreeGroup.of i) ^ c = w
  refine (deningerFreeGroupEquiv ι).injective ?_
  rw [map_zpow, hEq, hx, ← map_zpow]
  exact congrArg (PushoutI.of (φ := deningerFreeMap ι) i) hc

end RHTower
