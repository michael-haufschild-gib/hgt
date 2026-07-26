import GaloisForLFunctions.HTGeometry.FiniteGeometricLayerDAResonance

/-!
# Explicit finite geometric layer towers

The layer tower is an inductive family, so it is realized by its own constructors; what is missing is
explicit inhabitants above the empty tower.  A single positive geometric layer is a tower over the
zero residual, and a strictly decreasing pair of ratios stacks into a two-layer tower.  The
comparison used at each step is only that a smaller geometric ratio is little-o of a larger one.
-/

open Asymptotics Filter

namespace GaloisForLFunctions

noncomputable section

/-- Convenience form of the tower step with the layer sum already in normal form. -/
theorem finiteGeometricLayerTower_cons {layers : List (ℝ × ℝ)} {mid h : ℕ → ℝ} {A lam : ℝ}
    (hA : 0 < A) (hlam : 1 < lam)
    (hsmall : mid =o[atTop] fun n : ℕ => lam ^ n)
    (htail : FiniteGeometricLayerTower layers mid h) :
    FiniteGeometricLayerTower ((A, lam) :: layers) (fun n => A * lam ^ n + mid n) h :=
  FiniteGeometricLayerTower.cons hA hlam rfl hsmall htail

/-- A single positive geometric layer is a tower over the zero residual. -/
theorem finiteGeometricLayerTower_singleton {A lam : ℝ} (hA : 0 < A) (hlam : 1 < lam) :
    FiniteGeometricLayerTower [(A, lam)] (fun n => A * lam ^ n) (fun _ => 0) := by
  refine FiniteGeometricLayerTower.cons hA hlam ?_ ?_
    (FiniteGeometricLayerTower.nil (fun _ => 0))
  · funext n
    simp
  · simp

/-- A strictly decreasing pair of geometric ratios stacks into a two-layer tower. -/
theorem finiteGeometricLayerTower_pair {A₁ A₂ lam₁ lam₂ : ℝ}
    (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hlam₂ : 1 < lam₂) (hlam : lam₂ < lam₁) :
    FiniteGeometricLayerTower [(A₁, lam₁), (A₂, lam₂)]
      (fun n => A₁ * lam₁ ^ n + A₂ * lam₂ ^ n) (fun _ => 0) := by
  have hlam₁ : 1 < lam₁ := lt_trans hlam₂ hlam
  have hratio : (fun n : ℕ => lam₂ ^ n) =o[atTop] fun n : ℕ => lam₁ ^ n :=
    isLittleO_pow_pow_of_lt_left (le_of_lt (lt_trans zero_lt_one hlam₂)) hlam
  exact finiteGeometricLayerTower_cons hA₁ hlam₁ (hratio.const_mul_left A₂)
    (finiteGeometricLayerTower_singleton hA₂ hlam₂)

end

end GaloisForLFunctions
