import GaloisForLFunctions.GaloisTheoryOfZeros.Actions.SignedChoiceInvolutions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Common root choices for odd-order signed actions

The product of all signs gives a common fixed root choice for every finite
odd-order group acting by signed permutations. Conjugating by that choice
removes every sign simultaneously, even when the set of pair labels is infinite.

This explicit splitting extends the product-action and coprime-complement
mechanisms used by Ding et al., arXiv:2611.21555, Theorem 3.1 and Lemma 5.3.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.GaloisTheoryOfZeros.FibreSignedPerm
variable {α H : Type*} [Group H] [Fintype H]

/-- Product of the signs over a finite subgroup, taken separately at each pair label. -/
def normChoice (ρ : H →* FibreSignedPerm α) : α → ℤˣ :=
  fun i => ∏ g : H, (ρ g).sign i

attribute [-instance] Int.instUnitsPow in
private theorem odd_power_sign {n : ℕ} (hn : Odd n) (u : ℤˣ) : u ^ n = u := by
  have hu : u * u = 1 := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> rfl
  obtain ⟨k, hk⟩ := hn
  rw [hk, pow_add, pow_mul, pow_two, hu, one_pow, pow_one, one_mul]

/-- Odd cardinality makes the product of signs a common fixed root choice. -/
theorem normChoice_fixed (ρ : H →* FibreSignedPerm α) (hodd : Odd (Fintype.card H))
    (h : H) : choiceAction (ρ h) (normChoice ρ) = normChoice ρ := by
  funext i
  change (ρ h).sign i * (∏ g : H, (ρ g).sign ((ρ h).perm⁻¹ i)) =
    ∏ g : H, (ρ g).sign i
  have hm (g : H) : (ρ (h * g)).sign i =
      (ρ h).sign i * (ρ g).sign ((ρ h).perm⁻¹ i) := by
    rw [map_mul]
    rfl
  calc
    (ρ h).sign i * (∏ g : H, (ρ g).sign ((ρ h).perm⁻¹ i)) =
        (∏ g : H, (ρ h).sign i * (ρ g).sign ((ρ h).perm⁻¹ i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      rw [odd_power_sign hodd ((ρ h).sign i)]
    _ = ∏ g : H, (ρ (h * g)).sign i := by
      apply Finset.prod_congr rfl
      intro g _
      exact (hm g).symm
    _ = ∏ g : H, (ρ g).sign i :=
      Equiv.prod_comp (Equiv.mulLeft h) (fun g : H => (ρ g).sign i)

/-- One base-group conjugation removes every sign in a finite odd-order action. -/
theorem odd_action_simultaneously_unsigned (ρ : H →* FibreSignedPerm α)
    (hodd : Odd (Fintype.card H)) (h : H) :
    (choiceGauge (normChoice ρ))⁻¹ * ρ h * choiceGauge (normChoice ρ) =
      unsigned (ρ h).perm :=
  (fixed_choice_iff_gauge (ρ h) (normChoice ρ)).mp (normChoice_fixed ρ hodd h)

/-- Odd-order actions on conjugate pairs admit a common root choice, even for infinite pair sets. -/
theorem odd_action_has_fixed_choice (ρ : H →* FibreSignedPerm α)
    (hodd : Odd (Fintype.card H)) :
    ∃ f : α → ℤˣ, ∀ h : H, choiceAction (ρ h) f = f :=
  ⟨normChoice ρ, normChoice_fixed ρ hodd⟩

#print axioms odd_action_simultaneously_unsigned
#print axioms odd_action_has_fixed_choice
end GaloisForLFunctions.GaloisTheoryOfZeros.FibreSignedPerm
