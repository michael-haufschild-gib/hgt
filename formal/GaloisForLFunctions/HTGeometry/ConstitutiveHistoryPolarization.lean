import Mathlib.CategoryTheory.Groupoid
import Mathlib.Data.Complex.Basic

/-!
# Reversible phase and irreversible cost must polarize

Every nonnegative additive real cost on a groupoid vanishes.  The real part of an additive complex
groupoid weight therefore vanishes whenever it is nonnegative.  By contrast, the directed additive
monoid of natural-number histories carries a nonzero additive cost.  This closes both the no-go and
its strongest elementary positive survivor without a project postulate or computation proof.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory

universe u v

/-- Every nonnegative additive cost on a reversible history groupoid is identically zero. -/
theorem constitutiveGroupoid_nonnegativeAdditiveCost_eq_zero
    {C : Type u} [Groupoid.{v} C]
    (A : ∀ {X Y : C}, (X ⟶ Y) → ℝ)
    (h_id : ∀ X : C, A (𝟙 X) = 0)
    (h_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), A (f ≫ g) = A f + A g)
    (h_nonneg : ∀ {X Y : C} (f : X ⟶ Y), 0 ≤ A f) :
    ∀ {X Y : C} (f : X ⟶ Y), A f = 0 := by
  intro X Y f
  have hsum : A f + A (inv f) = 0 := by
    rw [← h_comp f (inv f), IsIso.hom_inv_id, h_id]
  exact (add_eq_zero_iff_of_nonneg (h_nonneg f) (h_nonneg (inv f))).mp hsum |>.1

/-- One additive complex groupoid weight cannot carry a nonzero nonnegative real cost. -/
theorem constitutiveGroupoid_complexWeight_nonnegativeRealPart_eq_zero
    {C : Type u} [Groupoid.{v} C]
    (W : ∀ {X Y : C}, (X ⟶ Y) → ℂ)
    (h_id : ∀ X : C, W (𝟙 X) = 0)
    (h_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), W (f ≫ g) = W f + W g)
    (h_nonneg : ∀ {X Y : C} (f : X ⟶ Y), 0 ≤ (W f).re) :
    ∀ {X Y : C} (f : X ⟶ Y), (W f).re = 0 := by
  apply constitutiveGroupoid_nonnegativeAdditiveCost_eq_zero
      (A := fun f ↦ (W f).re)
  · intro X
    rw [h_id]
    rfl
  · intro X Y Z f g
    rw [h_comp]
    rfl
  · exact h_nonneg

/-- Irreversible directed histories do support a nonzero nonnegative additive cost. -/
theorem constitutiveDirectedHistory_nontrivialAdditiveCost_exists :
    ∃ A : ℕ → ℕ,
      A 0 = 0 ∧
      (∀ m n : ℕ, A (m + n) = A m + A n) ∧
      A 1 ≠ 0 := by
  exact ⟨id, rfl, fun _ _ ↦ rfl, Nat.one_ne_zero⟩

end GaloisForLFunctions.HTGeometry
