import GaloisForLFunctions.RHTower.Deninger.DeningerRootAdjunction

/-!
# A single root adjunction destroys unique roots

Adjoining an `n`-th root to an element that already has one creates two distinct `n`-th roots.
Concretely, in the amalgam obtained from the free group on two generators by adjoining a square root
`t` of `a²`, both `t` and `a` are square roots of `a²`, and they are distinct — a homomorphism onto
`ℤ/2` sending `a` to `1` and `t` to `0` separates them.

So the naive tower of root adjunctions does not converge to the rationalization: its stages are not
groups with unique roots, and they do not embed in one.  Any construction of `Bau(G)` as a colimit
of amalgams has to adjoin roots more carefully, or quotient at each stage.

* `deningerRootAdjoinSeparator` : the separating homomorphism.
* `deningerRootAdjoin_root_ne_of` : the two square roots are distinct.
* `deningerRootAdjoin_not_uniquelyDivisible` : the amalgam does not have unique roots.
-/

namespace RHTower

open Monoid

section RootAdjunctionNoGo

/-- The generator that is squared. -/
abbrev deningerNoGoGen : FreeGroup Bool := FreeGroup.of true

/-- The values of the separating homomorphism on the two factors. -/
noncomputable def deningerNoGoFactorMap :
    ∀ b : Bool, DeningerRootFactor (FreeGroup Bool) b →* Multiplicative (ZMod 2)
  | false => FreeGroup.lift (fun i : Bool => if i then Multiplicative.ofAdd (1 : ZMod 2) else 1)
  | true => 1

theorem deningerNoGoCompat (i : Bool) :
    (deningerNoGoFactorMap i).comp
        (deningerRootBaseMap (deningerNoGoGen * deningerNoGoGen) 2 i) = 1 := by
  cases i with
  | false =>
    refine MonoidHom.ext fun x => ?_
    show (FreeGroup.lift (fun i : Bool => if i then Multiplicative.ofAdd (1 : ZMod 2) else 1))
      ((deningerNoGoGen * deningerNoGoGen) ^ (Multiplicative.toAdd x)) = 1
    rw [map_zpow, map_mul, FreeGroup.lift_apply_of]
    show (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2)) ^
      (Multiplicative.toAdd x) = 1
    rw [show (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2)) = 1 by decide,
      one_zpow]
  | true => exact MonoidHom.ext fun _ => rfl

/-- The separating homomorphism onto `ℤ/2`: it sends the square root inside the free group to `1`
and the adjoined root to `0`. -/
noncomputable def deningerRootAdjoinSeparator :
    DeningerRootAdjoin (deningerNoGoGen * deningerNoGoGen) 2 →*
      Multiplicative (ZMod 2) :=
  Monoid.PushoutI.lift deningerNoGoFactorMap 1 deningerNoGoCompat

@[simp]
theorem deningerRootAdjoinSeparator_of :
    deningerRootAdjoinSeparator
        (deningerRootAdjoinOf (deningerNoGoGen * deningerNoGoGen) 2 deningerNoGoGen) =
      Multiplicative.ofAdd (1 : ZMod 2) := by
  show Monoid.PushoutI.lift deningerNoGoFactorMap 1 deningerNoGoCompat
      (Monoid.PushoutI.of (φ := deningerRootBaseMap (deningerNoGoGen * deningerNoGoGen) 2) false
        (deningerNoGoGen : DeningerRootFactor (FreeGroup Bool) false)) = _
  rw [Monoid.PushoutI.lift_of]
  exact FreeGroup.lift_apply_of

@[simp]
theorem deningerRootAdjoinSeparator_root :
    deningerRootAdjoinSeparator
        (deningerRootAdjoinRoot (deningerNoGoGen * deningerNoGoGen) 2) = 1 := by
  show Monoid.PushoutI.lift deningerNoGoFactorMap 1 deningerNoGoCompat
      (Monoid.PushoutI.of (φ := deningerRootBaseMap (deningerNoGoGen * deningerNoGoGen) 2) true
        (Multiplicative.ofAdd (1 : ℤ))) = _
  rw [Monoid.PushoutI.lift_of]
  rfl

/-- **The adjoined root and the existing one are distinct.** -/
theorem deningerRootAdjoin_root_ne_of :
    deningerRootAdjoinRoot (deningerNoGoGen * deningerNoGoGen) 2 ≠
      deningerRootAdjoinOf (deningerNoGoGen * deningerNoGoGen) 2 deningerNoGoGen := by
  intro h
  have := congrArg deningerRootAdjoinSeparator h
  rw [deningerRootAdjoinSeparator_root, deningerRootAdjoinSeparator_of] at this
  exact absurd this (by decide)

/-- **A single root adjunction destroys unique roots.**  Both the adjoined root and the generator
square to the same element. -/
theorem deningerRootAdjoin_not_uniquelyDivisible :
    ¬ DeningerUniquelyDivisible (DeningerRootAdjoin (deningerNoGoGen * deningerNoGoGen) 2) := by
  intro h
  obtain ⟨x, -, huniq⟩ := h 2 (by norm_num)
    (deningerRootAdjoinOf (deningerNoGoGen * deningerNoGoGen) 2
      (deningerNoGoGen * deningerNoGoGen))
  have h1 : deningerRootAdjoinRoot (deningerNoGoGen * deningerNoGoGen) 2 = x :=
    huniq _ (deningerRootAdjoin_root_pow _ 2)
  have h2 : deningerRootAdjoinOf (deningerNoGoGen * deningerNoGoGen) 2 deningerNoGoGen = x := by
    refine huniq _ ?_
    show (deningerRootAdjoinOf (deningerNoGoGen * deningerNoGoGen) 2 deningerNoGoGen) ^ 2 =
      deningerRootAdjoinOf (deningerNoGoGen * deningerNoGoGen) 2
        (deningerNoGoGen * deningerNoGoGen)
    rw [← map_pow, ← pow_two]
  exact deningerRootAdjoin_root_ne_of (h1.trans h2.symm)

end RootAdjunctionNoGo

end RHTower
