import Mathlib.Tactic

/-!
# Affine collision modes and off-line quartet curvature

This module formalizes the exact algebraic core of the phase-cancellation diagnosis.

* affine scaling and translation preserve every strict root order and scale every gap by the same
  positive factor;
* the normalized displacement difference of an affine mode is the constant `-δa`;
* a functional-equation conjugate pair has the stated reciprocal-square curvature;
* doubling to the full quartet gives the sharp positive window `|τ| < a`.

No statement about RH, a limiting zero expansion, or the completeness of a proposed class of proof
methods is assumed here.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- An affine map scales every ordered gap by its slope. -/
theorem affineRootGap_exact :
    ∀ a b x y : ℝ, (a * y + b) - (a * x + b) = a * (y - x) := by
  intros
  ring

/-- Translation contributes zero to every displacement difference. -/
theorem translationDisplacement_gap_zero :
    ∀ δb _x _y : ℝ, δb - δb = 0 := by
  intros
  ring

/-- With the card's conventions
`Δε = ε(x) - ε(y)` and `Δ = y - x`, an affine displacement has normalized difference `-δa`. -/
theorem affineDisplacement_normalizedGap :
    ∀ δa δb x y : ℝ, x ≠ y →
      ((δa * x + δb) - (δa * y + δb)) / (y - x) = -δa := by
  intro δa δb x y hxy
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  field_simp [hyx]
  ring

/-- A positive-slope affine map preserves strict order exactly. -/
theorem affineRootOrder_iff :
    ∀ a b x y : ℝ, 0 < a → (a * x + b < a * y + b ↔ x < y) := by
  intro a b x y ha
  constructor <;> intro h <;> nlinarith

/-- A positive-slope affine deformation cannot collide two distinct real roots. -/
theorem affineRootCollision_iff :
    ∀ a b x y : ℝ, 0 < a → (a * x + b = a * y + b ↔ x = y) := by
  intro a b x y ha
  constructor
  · intro h
    nlinarith
  · exact congrArg fun r => a * r + b

/-- Exact reciprocal-square contribution of the horizontally reflected pair
`-a + iτ`, `a + iτ`. -/
theorem conjugatePair_reciprocalSq :
    ∀ a τ : ℝ, a ^ (2 : ℕ) + τ ^ (2 : ℕ) ≠ 0 →
      ((((-(a : ℂ)) + (τ : ℂ) * I)⁻¹) ^ (2 : ℕ) +
          (((a : ℂ) + (τ : ℂ) * I)⁻¹) ^ (2 : ℕ)) =
        ((2 * (a ^ (2 : ℕ) - τ ^ (2 : ℕ)) / (a ^ (2 : ℕ) + τ ^ (2 : ℕ)) ^ (2 : ℕ) : ℝ) : ℂ) := by
  intro a τ h
  have hplus : (a : ℂ) + (τ : ℂ) * I ≠ 0 := by
    intro hz
    have hz' := congrArg Complex.normSq hz
    simp [Complex.normSq_apply] at hz'
    apply h
    calc
      a ^ (2 : ℕ) + τ ^ (2 : ℕ) = a * a + τ * τ := by ring
      _ = 0 := hz'
  have hminus : (-(a : ℂ)) + (τ : ℂ) * I ≠ 0 := by
    intro hz
    have hz' := congrArg Complex.normSq hz
    simp [Complex.normSq_apply] at hz'
    apply h
    calc
      a ^ (2 : ℕ) + τ ^ (2 : ℕ) = a * a + τ * τ := by ring
      _ = 0 := hz'
  push_cast
  have hden : (a : ℂ) ^ (2 : ℕ) + (τ : ℂ) ^ (2 : ℕ) ≠ 0 := by
    exact_mod_cast h
  rw [inv_pow, inv_pow]
  field_simp [hplus, hminus, hden]
  ring_nf
  simp
  ring

/-- The full functional-equation quartet doubles the pair contribution. -/
theorem offLineQuartet_reciprocalSq :
    ∀ a τ : ℝ, a ^ (2 : ℕ) + τ ^ (2 : ℕ) ≠ 0 →
      2 * ((((-(a : ℂ)) + (τ : ℂ) * I)⁻¹) ^ (2 : ℕ) +
          (((a : ℂ) + (τ : ℂ) * I)⁻¹) ^ (2 : ℕ)) =
        ((4 * (a ^ (2 : ℕ) - τ ^ (2 : ℕ)) / (a ^ (2 : ℕ) + τ ^ (2 : ℕ)) ^ (2 : ℕ) : ℝ) : ℂ) := by
  intro a τ h
  rw [conjugatePair_reciprocalSq a τ h]
  push_cast
  ring

/-- Sharp anti-smoothing window of one off-line quartet: for horizontal displacement `a > 0`,
the quartet curvature is positive exactly at heights satisfying `|τ| < a`. -/
theorem offLineQuartet_curvature_pos_iff :
    ∀ a τ : ℝ, 0 < a →
      (0 < 4 * (a ^ (2 : ℕ) - τ ^ (2 : ℕ)) / (a ^ (2 : ℕ) + τ ^ (2 : ℕ)) ^ (2 : ℕ) ↔ |τ| < a) := by
  intro a τ ha
  have hden : 0 < (a ^ (2 : ℕ) + τ ^ (2 : ℕ)) ^ (2 : ℕ) := by
    positivity
  rw [div_pos_iff]
  constructor
  · intro h
    have hnum : 0 < 4 * (a ^ (2 : ℕ) - τ ^ (2 : ℕ)) := by
      rcases h with h | h
      · exact h.1
      · exact False.elim (by nlinarith [hden, h.2])
    rw [abs_lt]
    constructor <;> nlinarith
  · intro h
    left
    constructor
    · rw [abs_lt] at h
      nlinarith
    · exact hden

/-- Closed package of the exact affine/curvature laws used by the card. -/
theorem phaseCancellationAffineCurvatureLaw :
    (∀ a b x y : ℝ, (a * y + b) - (a * x + b) = a * (y - x)) ∧
    (∀ δa δb x y : ℝ, x ≠ y →
      ((δa * x + δb) - (δa * y + δb)) / (y - x) = -δa) ∧
    (∀ a b x y : ℝ, 0 < a → (a * x + b = a * y + b ↔ x = y)) ∧
    (∀ a τ : ℝ, a ^ (2 : ℕ) + τ ^ (2 : ℕ) ≠ 0 →
      2 * ((((-(a : ℂ)) + (τ : ℂ) * I)⁻¹) ^ (2 : ℕ) +
          (((a : ℂ) + (τ : ℂ) * I)⁻¹) ^ (2 : ℕ)) =
        ((4 * (a ^ (2 : ℕ) - τ ^ (2 : ℕ)) / (a ^ (2 : ℕ) + τ ^ (2 : ℕ)) ^ (2 : ℕ) : ℝ) : ℂ)) ∧
    (∀ a τ : ℝ, 0 < a →
      (0 < 4 * (a ^ (2 : ℕ) - τ ^ (2 : ℕ)) / (a ^ (2 : ℕ) + τ ^ (2 : ℕ)) ^ (2 : ℕ) ↔ |τ| < a)) := by
  exact ⟨affineRootGap_exact, affineDisplacement_normalizedGap,
    affineRootCollision_iff, offLineQuartet_reciprocalSq, offLineQuartet_curvature_pos_iff⟩

end

end GaloisForLFunctions.RHTower
