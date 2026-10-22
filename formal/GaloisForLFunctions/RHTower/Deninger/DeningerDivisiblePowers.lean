import GaloisForLFunctions.RHTower.Deninger.DeningerFamilyRoot

/-!
# Divisibility passes to powers

A root of an element gives a root of each of its powers, by taking the same power of the root.  So
in a colimit where the images of the family members are divisible, every power of such an image is
divisible too.

* `deningerDivisible_zpow` : a root of an element gives a root of its powers.
* `deningerFamilyColimit_divisible_of_mem` : divisibility at powers of a family member.
-/

namespace RHTower

universe u

/-- **A root of an element gives a root of each of its powers.** -/
theorem deningerDivisible_zpow {G : Type u} [Group G] (x y : G) (N c : ℤ) (h : y ^ N = x) :
    (y ^ c) ^ N = x ^ c := by
  rw [← zpow_mul, mul_comm, zpow_mul, h]

namespace RootAdjunction

/-- **Divisibility at powers of a family member.** -/
theorem deningerFamilyColimit_divisible_of_mem (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ)
    (n q : ℕ) (N : ℤ) (x : deningerFamilyColimit S₀ sched)
    (hx : ∃ c : ℤ, (deningerFamilyIota S₀ sched n ((deningerFamilyTower S₀ sched n).fam q)) ^ c
      = x)
    (hroot : ∃ z : deningerFamilyColimit S₀ sched,
      z ^ N = deningerFamilyIota S₀ sched n ((deningerFamilyTower S₀ sched n).fam q)) :
    ∃ y : deningerFamilyColimit S₀ sched, y ^ N = x := by
  obtain ⟨c, hc⟩ := hx
  obtain ⟨z, hz⟩ := hroot
  refine ⟨z ^ c, ?_⟩
  rw [deningerDivisible_zpow _ _ N c hz, hc]

end RootAdjunction

end RHTower
