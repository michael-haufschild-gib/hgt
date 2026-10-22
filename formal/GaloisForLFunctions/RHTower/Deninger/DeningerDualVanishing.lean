import GaloisForLFunctions.RHTower.Deninger.DeningerUniquelyDivisibleProd

/-!
# A vector space vanishes when its dual does

Over a field a vector space is determined by its dual to the extent of vanishing: a nonzero vector
carries a functional not vanishing on it.  This is the linear algebra behind transferring vanishing
statements between homology and cohomology, the cochain complex being the dual of the chain complex.

* `deningerEq_zero_of_dual_eq_zero` : the vanishing.
-/

namespace RHTower

universe u

/-- **A vector space whose dual vanishes is zero.** -/
theorem deningerEq_zero_of_dual_eq_zero (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
    (h : ∀ f : Module.Dual k V, f = 0) (x : V) : x = 0 := by
  refine (Module.forall_dual_apply_eq_zero_iff k x).1 (fun f => ?_)
  rw [h f]
  rfl

/-- Conversely the dual of a zero space vanishes. -/
theorem deningerDual_eq_zero_of_eq_zero (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
    (h : ∀ x : V, x = 0) (f : Module.Dual k V) : f = 0 := by
  ext x
  rw [h x, map_zero, LinearMap.zero_apply]

end RHTower
