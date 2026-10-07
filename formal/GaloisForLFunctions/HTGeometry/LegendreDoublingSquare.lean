import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

/-!
# Square coordinates of doubled points on a Legendre curve

For a finite doubled point on `y²=x(x-1)(x-lambda)`, both its x-coordinate and its
x-coordinate minus one are squares. Either nonsquare coordinate therefore obstructs
halving in the actual affine group. These identities require no nonsingularity hypothesis
on the entire cubic beyond the nonsingularity of the points used by the affine group.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.LegendreDoubling
open WeierstrassCurve.Affine
variable {F : Type*} [Field F] [CharZero F]
local instance : DecidableEq F := Classical.decEq F

def curve (lam : F) : WeierstrassCurve.Affine F := ⟨0, -(1 + lam), 0, lam, 0⟩

theorem double_x_square {lam x y : F} (h : (curve lam).Nonsingular x y)
    (hy : y ≠ (curve lam).negY x y) :
    IsSquare ((curve lam).addX x x ((curve lam).slope x x y y)) := by
  have hy0 : y ≠ 0 := by
    intro hz
    exact hy (by simp [curve, negY, hz])
  have he := (equation_iff x y).mp ((nonsingular_iff' x y).mp h).1
  simp only [curve, zero_mul, add_zero] at he
  refine ⟨(x ^ 2 - lam) / (2 * y), ?_⟩
  rw [slope_of_Y_ne rfl hy]
  simp only [curve, addX, negY, zero_mul, sub_zero, add_zero, sub_neg_eq_add,
    ← two_mul y]
  field_simp
  linear_combination 4 * (lam + 1 - 2 * x) * he

theorem double_x_sub_one_square {lam x y : F} (h : (curve lam).Nonsingular x y)
    (hy : y ≠ (curve lam).negY x y) :
    IsSquare ((curve lam).addX x x ((curve lam).slope x x y y) - 1) := by
  have hy0 : y ≠ 0 := by
    intro hz
    exact hy (by simp [curve, negY, hz])
  have he := (equation_iff x y).mp ((nonsingular_iff' x y).mp h).1
  simp only [curve, zero_mul, add_zero] at he
  refine ⟨(x ^ 2 - 2 * x + lam) / (2 * y), ?_⟩
  rw [slope_of_Y_ne rfl hy]
  simp only [curve, addX, negY, zero_mul, sub_zero, add_zero, sub_neg_eq_add,
    ← two_mul y]
  field_simp
  linear_combination 4 * (lam - 2 * x) * he

theorem point_not_double_of_x_not_square {lam x y : F}
    (h : (curve lam).Nonsingular x y) (hx : ¬ IsSquare x)
    (R : (curve lam).Point) : R + R ≠ Point.some x y h := by
  cases R with
  | zero => exact (Point.some_ne_zero h).symm
  | some a b hab =>
    by_cases hy : b = (curve lam).negY a b
    · rw [Point.add_self_of_Y_eq hy]
      exact (Point.some_ne_zero h).symm
    · intro hd
      rw [Point.add_self_of_Y_ne hy] at hd
      have he := (Point.some.inj hd).1
      have hs := double_x_square hab hy
      rw [he] at hs
      exact hx hs

theorem point_not_double_of_x_sub_one_not_square {lam x y : F}
    (h : (curve lam).Nonsingular x y) (hx : ¬ IsSquare (x - 1))
    (R : (curve lam).Point) : R + R ≠ Point.some x y h := by
  cases R with
  | zero => exact (Point.some_ne_zero h).symm
  | some a b hab =>
    by_cases hy : b = (curve lam).negY a b
    · rw [Point.add_self_of_Y_eq hy]
      exact (Point.some_ne_zero h).symm
    · intro hd
      rw [Point.add_self_of_Y_ne hy] at hd
      have he := (Point.some.inj hd).1
      have hs := double_x_sub_one_square hab hy
      rw [he] at hs
      exact hx hs

end GaloisForLFunctions.HTGeometry.LegendreDoubling
