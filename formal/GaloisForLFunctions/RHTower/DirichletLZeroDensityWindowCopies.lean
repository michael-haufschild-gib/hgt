/-
# Multiplicity-copy packets for centered Dirichlet-L zero windows

This module turns the finite support/multiplicity sum of a centered
Dirichlet-L zero window into a finite type of individual zero copies.  A zero
of divisor multiplicity `m` supplies exactly `m` packet labels, so finite
combinatorial representative selection can preserve the literal
multiplicity-weighted zero count.

No RH, GRH, zero simplicity premise, local density estimate, or zero-detection
premise is used.
-/

import GaloisForLFunctions.RHTower.DirichletLZeroDensityWindowSupport

noncomputable section

namespace RHTower

/-- The finite type of distinct divisor points in a centered vertical zero
window. -/
abbrev CGLZeroDensityVerticalWindowZero
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :=
  ↑(cglZeroDensityVerticalWindowZeroSupport n χ σ τ H)

/-- The multiplicity-copy packet: a point of divisor multiplicity `m` has one
label for each element of `Fin m`. -/
abbrev CGLZeroDensityVerticalWindowZeroCopy
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :=
  Σ z : CGLZeroDensityVerticalWindowZero n χ σ τ H,
    Fin (cglZeroDensityVerticalWindowMultiplicity n χ σ τ H z.1).toNat

/-- The cardinality of the zero-copy packet is the finite support sum of the
individual divisor multiplicities. -/
theorem card_cglZeroDensityVerticalWindowZeroCopy
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :
    Fintype.card (CGLZeroDensityVerticalWindowZeroCopy n χ σ τ H) =
      ∑ z ∈ cglZeroDensityVerticalWindowZeroSupport n χ σ τ H,
        (cglZeroDensityVerticalWindowMultiplicity n χ σ τ H z).toNat := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  symm
  apply Finset.sum_subtype
  intro z
  rfl

/-- The cardinality of the multiplicity-copy packet is exactly the literal
centered-window zero count. -/
theorem card_cglZeroDensityVerticalWindowZeroCopy_eq_count
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :
    (Fintype.card (CGLZeroDensityVerticalWindowZeroCopy n χ σ τ H) : ℝ) =
      completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H := by
  rw [card_cglZeroDensityVerticalWindowZeroCopy]
  rw [Nat.cast_sum]
  calc
    ∑ z ∈ cglZeroDensityVerticalWindowZeroSupport n χ σ τ H,
        ((cglZeroDensityVerticalWindowMultiplicity n χ σ τ H z).toNat : ℝ) =
      ∑ z ∈ cglZeroDensityVerticalWindowZeroSupport n χ σ τ H,
        (cglZeroDensityVerticalWindowMultiplicity n χ σ τ H z : ℝ) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact_mod_cast Int.toNat_of_nonneg
        (cglZeroDensityVerticalWindowMultiplicity_pos n χ σ τ H z hz).le
    _ = completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H :=
      (completedLFunction_zeroDensityVerticalWindowCount_eq_sum_multiplicity n χ σ τ H).symm

end RHTower
