import GaloisForLFunctions.HTGeometry.HermitianLocalSpectralObserverLaw
import Mathlib.Algebra.BigOperators.Fin

/-!
# Separation of configurations by the total on-site energy

The local-spectral observer layer carries, in more than a hundred statements, the hypothesis that
the total energy `x ↦ ∑ v, onsite v (x v)` separates configurations, and nothing in the corpus
exhibits such an energy.  Three facts settle it.

Complexifying changes nothing: the complex total energy is the cast of the real one, so the two
separation hypotheses are equivalent and the complex layer inherits every real witness.
Separation is inherited sitewise, so it is a strengthening of injectivity at each site.  And it is
attained: reading the configuration as a base-`m` numeral gives a real on-site energy whose total
separates.

* **`injective_onsiteProductEnergy_complexOnsite_iff`** — the complex hypothesis is the real one;
* `injective_onsite_of_injective_onsiteProductEnergy` — separation is sitewise injective;
* **`injective_onsiteProductEnergy_digitOnsite`** — the base-`m` energy separates.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-! ## Complexification is inert -/

/-- The complexified total energy is the complex cast of the real total energy. -/
theorem onsiteProductEnergy_complexOnsite {V : Type*} [Fintype V] {A : V → Type*}
    (onsite : ∀ v, A v → ℝ) (x : ∀ v, A v) :
    onsiteProductEnergy (complexOnsite onsite) x =
      ((onsiteProductEnergy onsite x : ℝ) : ℂ) := by
  simp [onsiteProductEnergy, complexOnsite]

/-- **The complex separation hypothesis is the real one.**  Complexification neither creates nor
destroys separation of configurations. -/
theorem injective_onsiteProductEnergy_complexOnsite_iff {V : Type*} [Fintype V] {A : V → Type*}
    (onsite : ∀ v, A v → ℝ) :
    Function.Injective (onsiteProductEnergy (complexOnsite onsite)) ↔
      Function.Injective (onsiteProductEnergy onsite) := by
  constructor
  · intro h x y hxy
    refine h ?_
    rw [onsiteProductEnergy_complexOnsite, onsiteProductEnergy_complexOnsite, hxy]
  · intro h x y hxy
    rw [onsiteProductEnergy_complexOnsite, onsiteProductEnergy_complexOnsite] at hxy
    exact h (by exact_mod_cast hxy)

/-! ## Separation is sitewise -/

/-- A total energy that separates configurations is injective at every site: change one coordinate
and only its summand moves. -/
theorem injective_onsite_of_injective_onsiteProductEnergy {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Nonempty (A v)] {R : Type*} [AddCommMonoid R]
    {onsite : ∀ v, A v → R} (h : Function.Injective (onsiteProductEnergy onsite)) (v : V) :
    Function.Injective (onsite v) := by
  classical
  intro a b hab
  set base : ∀ w, A w := fun w => Classical.arbitrary (A w) with hbase
  have hsum : onsiteProductEnergy onsite (Function.update base v a) =
      onsiteProductEnergy onsite (Function.update base v b) := by
    simp only [onsiteProductEnergy]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ v), Function.update_self,
      Function.update_self, hab]
    refine congrArg _ (Finset.sum_congr rfl fun w hw => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hw),
      Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  have hupd := h hsum
  have := congrFun hupd v
  rwa [Function.update_self, Function.update_self] at this

/-! ## The separating energy exists -/

/-- Reading a configuration of `n` sites with `m` states as a base-`m` numeral. -/
def digitOnsite (n m : ℕ) : ∀ _v : Fin n, Fin m → ℝ :=
  fun v a => (a : ℝ) * (m : ℝ) ^ (v : ℕ)

/-- **The base-`m` on-site energy separates configurations.**  Its total energy is the numeral of
the configuration, and distinct numerals name distinct configurations. -/
theorem injective_onsiteProductEnergy_digitOnsite (n m : ℕ) :
    Function.Injective (onsiteProductEnergy (digitOnsite n m)) := by
  intro x y hxy
  have hxy' : ((finFunctionFinEquiv x : ℕ) : ℝ) = ((finFunctionFinEquiv y : ℕ) : ℝ) := by
    rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
    push_cast
    simpa [onsiteProductEnergy, digitOnsite] using hxy
  exact finFunctionFinEquiv.injective
    (Fin.ext (Nat.cast_injective (R := ℝ) hxy'))

/-- The complexified base-`m` energy separates as well. -/
theorem injective_onsiteProductEnergy_complexOnsite_digitOnsite (n m : ℕ) :
    Function.Injective (onsiteProductEnergy (complexOnsite (digitOnsite n m))) :=
  (injective_onsiteProductEnergy_complexOnsite_iff (digitOnsite n m)).2
    (injective_onsiteProductEnergy_digitOnsite n m)

end GaloisForLFunctions.HTGeometry
