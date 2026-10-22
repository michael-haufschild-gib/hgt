import GaloisForLFunctions.RHTower.Deninger.DeningerAmalgamRootsOne
import GaloisForLFunctions.RHTower.Deninger.DeningerRootCentral
import GaloisForLFunctions.RHTower.Deninger.DeningerRootTorsionFree

/-!
# A root adjunction preserves unique roots

Adjoining a root to an element of infinite order whose cyclic subgroup is isolated and
self-centralizing, in a torsion free group with unique roots, gives a group with unique roots.  The
hypotheses are exactly those the general amalgam theorem consumes, the infinite cyclic factor being
the one exempted from the centralizer condition.

* `deningerRootAdjunction_uniqueRoots` : the root adjunction step.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

/-- **A root adjunction preserves unique roots.** -/
theorem deningerRootAdjunction_uniqueRoots (A : Type u) [Group A] (a : A) (m : ℤ) (hm : m ≠ 0)
    (ha : ∀ n : ℤ, a ^ n = 1 → n = 0)
    (hA : ∀ (x y : A) (n : ℕ), 0 < n → x ^ n = y ^ n → x = y)
    (hiso : ∀ (y : A) (n : ℕ), 0 < n → y ^ n ∈ Subgroup.zpowers a → y ∈ Subgroup.zpowers a)
    (hcentA : ∀ (x : A) (c : ℤ), c ≠ 0 → x * a ^ c * x⁻¹ = a ^ c → x ∈ Subgroup.zpowers a)
    (htorA : ∀ (x : A) (n : ℕ), 0 < n → x ^ n = 1 → x = 1)
    (x y : PushoutI (deningerRootMap A a m)) (n : ℕ)
    (h : x ^ (n + 1) = y ^ (n + 1)) : x = y := by
  classical
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty (deningerRootMap A a m)
    (deningerRootMap_injective A a m hm ha)
  refine deningerAmalgam_pow_inj_one (d := d) (deningerRootMap_injective A a m hm ha)
    (deningerRootHcent A a m hm ha hA hiso) (ULift.up false) ?_ ?_ ?_ ?_ ?_ ?_ x y n h
  · rintro ⟨b⟩ z v hi hv hz
    cases b
    · exact absurd rfl hi
    · have hne : Multiplicative.toAdd (MulEquiv.ulift v) ≠ 0 := by
        intro hzero
        refine hv ?_
        apply MulEquiv.ulift.injective
        apply Multiplicative.toAdd.injective
        simpa using hzero
      exact (deningerRootMap_true_mem_iff A a m z).2
        (hcentA z (Multiplicative.toAdd (MulEquiv.ulift v)) hne hz)
  · exact fun p q r hr hpq => deningerRootFactorFalse_pow_inj A p q r hr hpq
  · intro u v
    apply MulEquiv.ulift.injective
    simp [mul_comm]
  · exact fun u k hk hu => deningerUliftInt_torsionFree u k hk hu
  · rintro ⟨b⟩ p q r hr hpq
    cases b
    · exact deningerRootFactorFalse_pow_inj A p q r hr hpq
    · exact hA p q r hr hpq
  · exact fun g k hk hg => deningerRootAdjunction_torsionFree A a m hm ha htorA g k hk hg

end RootAdjunction

end RHTower
