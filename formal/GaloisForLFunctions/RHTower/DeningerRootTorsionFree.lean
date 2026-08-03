import GaloisForLFunctions.RHTower.DeningerAmalgamCyclic
import GaloisForLFunctions.RHTower.DeningerPushoutTorsion

/-!
# A root adjunction preserves torsion freeness

Adjoining a root to a torsion free group leaves a torsion free group: the amalgam of torsion free
groups over a torsion free base is torsion free, and both the infinite cyclic factor and the
infinite cyclic base are torsion free.  So every stage of a tower of root adjunctions is torsion
free, and every nontrivial element of a stage has infinite order — which is what the next stage
needs of the element whose root it adjoins.

* `deningerRootAdjunction_torsionFree` : the step.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

theorem deningerMultiplicativeInt_torsionFree (x : Multiplicative ℤ) (n : ℕ) (hn : 0 < n)
    (h : x ^ n = 1) : x = 1 := by
  have h2 : n • Multiplicative.toAdd x = 0 := by
    have := congrArg Multiplicative.toAdd h
    simpa using this
  have h3 : Multiplicative.toAdd x = 0 := by
    simp only [nsmul_eq_mul, mul_eq_zero, Nat.cast_eq_zero] at h2
    omega
  exact Multiplicative.toAdd.injective h3

theorem deningerUliftInt_torsionFree (x : ULift.{u} (Multiplicative ℤ)) (n : ℕ) (hn : 0 < n)
    (h : x ^ n = 1) : x = 1 := by
  have h1 : (MulEquiv.ulift x : Multiplicative ℤ) ^ n = 1 := by
    rw [← map_pow, h, map_one]
  exact MulEquiv.ulift.injective (by rw [deningerMultiplicativeInt_torsionFree _ n hn h1, map_one])

/-- **Adjoining a root preserves torsion freeness.** -/
theorem deningerRootAdjunction_torsionFree (A : Type u) [Group A] (a : A) (m : ℤ) (hm : m ≠ 0)
    (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (hA : ∀ (x : A) (n : ℕ), 0 < n → x ^ n = 1 → x = 1)
    (g : PushoutI (deningerRootMap A a m)) (n : ℕ) (hn : 0 < n) (hg : g ^ n = 1) : g = 1 := by
  refine deningerPushout_torsionFree (deningerRootMap_injective A a m hm ha) ?_
    (fun h k hk hh => deningerUliftInt_torsionFree h k hk hh) g n hn hg
  rintro ⟨b⟩
  cases b
  · exact fun x k hk hx => deningerUliftInt_torsionFree x k hk hx
  · exact fun x k hk hx => hA x k hk hx

end RootAdjunction

end RHTower
