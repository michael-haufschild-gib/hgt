import GaloisForLFunctions.RHTower.DeningerAmalgamTwo

/-!
# Vanishing for a free product of two infinite cyclic groups

Amalgamating over the trivial group is a free product, and the tree of such a product has trivial
edge stabilizers.  So the homology of a free product of two infinite cyclic groups vanishes in
degrees at least two.

* `deningerFreeProduct_isZero_of_factors` : vanishing passes from the factors to a free product.
* `deningerFreeProduct_isZero` : the vanishing for two infinite cyclic factors.
-/

namespace RHTower

open Monoid Monoid.PushoutI CategoryTheory CategoryTheory.Limits

universe u

variable {G : ULift.{u} Bool → Type u} [∀ i, Group (G i)]
  {φ : ∀ i, PUnit.{u + 1} →* G i}

/-- **Vanishing passes from the factors to a free product.**  Amalgamating over the trivial group
leaves nothing on the edges of the tree, so a degree at least two in which both factors vanish
vanishes for the product. -/
theorem deningerFreeProduct_isZero_of_factors (k : Type u) [CommRing k]
    [DecidableEq (PushoutI φ)] (hφ : ∀ i, Function.Injective (φ i)) (n : ℕ)
    (h₀ : IsZero (groupHomology (Rep.trivial k (G (ULift.up true)) k) (n + 2)))
    (h₁ : IsZero (groupHomology (Rep.trivial k (G (ULift.up false)) k) (n + 2))) :
    IsZero (groupHomology (Rep.trivial k (PushoutI φ) k) (n + 2)) := by
  classical
  have hbase : (PushoutI.base φ).range ≃* PUnit.{u + 1} :=
    (MonoidHom.ofInjective (PushoutI.base_injective hφ)).symm
  have htrue : (PushoutI.of (φ := φ) (ULift.up true)).range ≃* G (ULift.up true) :=
    (MonoidHom.ofInjective (PushoutI.of_injective hφ _)).symm
  have hfalse : (PushoutI.of (φ := φ) (ULift.up false)).range ≃* G (ULift.up false) :=
    (MonoidHom.ofInjective (PushoutI.of_injective hφ _)).symm
  haveI : Subsingleton ((PushoutI.base φ).range) := hbase.toEquiv.subsingleton
  refine deningerAmalgam_isZero k hφ (n + 2) (n + 1) rfl ?_ ?_ ?_ ?_
  · exact isZero_groupHomology_succ_of_subsingleton _ (n + 1)
  · exact IsZero.of_iso h₀ (deningerTrivialHomologyIso htrue k (n + 2))
  · exact IsZero.of_iso h₁ (deningerTrivialHomologyIso hfalse k (n + 2))
  · exact isZero_groupHomology_succ_of_subsingleton _ n

/-- **Vanishing for a free product of two infinite cyclic groups.** -/
theorem deningerFreeProduct_isZero (k : Type u) [CommRing k] [DecidableEq (PushoutI φ)]
    (hφ : ∀ i, Function.Injective (φ i))
    (e₀ : G (ULift.up true) ≃* Multiplicative ℤ) (e₁ : G (ULift.up false) ≃* Multiplicative ℤ)
    (n : ℕ) :
    IsZero (groupHomology (Rep.trivial k (PushoutI φ) k) (n + 2)) := by
  classical
  exact deningerFreeProduct_isZero_of_factors k hφ n (deningerZ_isZero k e₀ n)
    (deningerZ_isZero k e₁ n)

end RHTower
