import GaloisForLFunctions.HTGeometry.AffineExponentialInvariantKaehler
import GaloisForLFunctions.HTGeometry.TorusChartFundamentalGroup
import GaloisForLFunctions.RHTower.SchanuelDefectLattice

/-!
# The Schanuel defect as a mixed invariant Kähler form

This file realizes a tuple `(x, exp x)` as a genuine point of `Gₘⁿ × Gₐⁿ` and identifies the
pullback of the mixed invariant form with the finite algebraic-coefficient sum of numerical
Schanuel defects.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open AffineExponentialPointEvaluation
open AffineExponentialInvariantKaehler

noncomputable section

@[simp] theorem coe_complexExpUnits (z : ℂ) :
    (complexExpUnits z : ℂ) = Complex.exp z := by
  have h := (unitsHomeomorphNeZero (G₀ := ℂ)).apply_symm_apply
    (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})
  exact congrArg Subtype.val h

/-- The mixed group point `(x, exp x)`. -/
def schanuelExponentialPoint {n : ℕ} (x : Fin n → ℂ) : Point ℂ n :=
  ofCoordinates x (fun i => complexExpUnits (x i))

@[simp] theorem additivePart_schanuelExponentialPoint {n : ℕ} (x : Fin n → ℂ) :
    additivePart (schanuelExponentialPoint x) = x := rfl

@[simp] theorem torusPart_schanuelExponentialPoint {n : ℕ} (x : Fin n → ℂ) (i : Fin n) :
    (torusPart (schanuelExponentialPoint x) i : ℂ) = Complex.exp (x i) := by
  change (complexExpUnits (x i) : ℂ) = Complex.exp (x i)
  exact coe_complexExpUnits (x i)

/-- Pullback of the mixed invariant direction `(c,-c)` to `(x,exp x)` is exactly the numerical
algebraic-coefficient Schanuel-defect sum. -/
theorem pointKaehlerMap_schanuelInvariantVector {n : ℕ}
    (x : Fin n → ℂ) (c : Fin n → algebraicClosure ℚ ℂ) :
    pointKaehlerMap (algebraicClosure ℚ ℂ) (schanuelExponentialPoint x)
      (mixedInvariantKaehlerVector (algebraicClosure ℚ ℂ)
        c (fun i => -c i)) =
      ∑ i, (c i : ℂ) • schanuelDefect (x i) := by
  classical
  rw [pointKaehlerMap_mixedInvariantKaehlerVector]
  have hpos (i : Fin n) :
      (AlgebraicTorusCharacter.character
        (torusPart (schanuelExponentialPoint x)) (Finsupp.single i 1) : ℂ) =
          Complex.exp (x i) := by
    rw [AlgebraicTorusCharacter.character_single, zpow_one]
    exact torusPart_schanuelExponentialPoint x i
  have hneg (i : Fin n) :
      (AlgebraicTorusCharacter.character
        (torusPart (schanuelExponentialPoint x)) (-(Finsupp.single i 1)) : ℂ) =
          (Complex.exp (x i))⁻¹ := by
    rw [AlgebraicTorusCharacter.character_neg, Units.val_inv_eq_inv_val, hpos]
  simp_rw [hpos, hneg]
  simp only [additivePart_schanuelExponentialPoint]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change ((c i : ℂ) * (Complex.exp (x i))⁻¹) •
        KaehlerDifferential.D (algebraicClosure ℚ ℂ) ℂ (Complex.exp (x i)) +
      (-(c i : ℂ)) • KaehlerDifferential.D (algebraicClosure ℚ ℂ) ℂ (x i) = _
  simp only [schanuelDefect]
  module

theorem pointKaehlerMap_schanuelInvariantVector_eq_zero_of_relation {n : ℕ}
    (x : Fin n → ℂ) (c : Fin n → algebraicClosure ℚ ℂ)
    (hrelation : ∑ i, (c i : ℂ) • schanuelDefect (x i) = 0) :
    pointKaehlerMap (algebraicClosure ℚ ℂ) (schanuelExponentialPoint x)
      (mixedInvariantKaehlerVector (algebraicClosure ℚ ℂ)
        c (fun i => -c i)) = 0 := by
  rw [pointKaehlerMap_schanuelInvariantVector, hrelation]

end

end GaloisForLFunctions.RHTower
