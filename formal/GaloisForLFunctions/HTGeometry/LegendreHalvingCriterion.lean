import GaloisForLFunctions.HTGeometry.LegendreDoublingSquare

/-!
# Complete halving criterion on a smooth Legendre curve

For a finite point with nonzero y-coordinate, the two square coordinates x and
x-1 are sufficient as well as necessary for halving. The explicit classical
three-root construction is verified using the actual affine group law, including
the sign which makes its double the specified point rather than its negative.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.LegendreDoubling
open WeierstrassCurve.Affine
variable {F : Type*} [Field F] [CharZero F]
local instance : DecidableEq F := Classical.decEq F

/-- The explicit three-root construction gives a half in the actual affine group. -/
theorem exists_half_of_square_roots {lam x y a b c : F}
    (hl0 : lam ≠ 0) (hl1 : lam ≠ 1) (hP : (curve lam).Nonsingular x y)
    (ha : a ^ 2 = x) (hb : b ^ 2 = x - 1) (hc : c ^ 2 = x - lam)
    (habc : a * b * c = -y) :
    ∃ R : (curve lam).Point, R + R = Point.some x y hP := by
  let X := (a + b) * (a + c)
  let Y := -(a + b) * (a + c) * (b + c)
  have hab : a + b ≠ 0 := by
    intro h
    have he : a ^ 2 - b ^ 2 = 0 := by linear_combination (a - b) * h
    have hh : (1 : F) = 0 := by linear_combination he - ha + hb
    exact one_ne_zero hh
  have hac : a + c ≠ 0 := by
    intro h
    have he : a ^ 2 - c ^ 2 = 0 := by linear_combination (a - c) * h
    apply hl0
    linear_combination he - ha + hc
  have hbc : b + c ≠ 0 := by
    intro h
    have he : b ^ 2 - c ^ 2 = 0 := by linear_combination (b - c) * h
    apply hl1
    linear_combination he - hb + hc
  have hy0 : Y ≠ 0 := mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hab) hac) hbc
  have hX1 : X - 1 = (a + b) * (b + c) := by
    dsimp [X]
    linear_combination ha - hb
  have hXl : X - lam = (a + c) * (b + c) := by
    dsimp [X]
    linear_combination ha - hc
  have hcurve : Y ^ 2 = X * (X - 1) * (X - lam) := by
    rw [hX1, hXl]
    dsimp [X, Y]
    ring
  have heq : (curve lam).Equation X Y := by
    apply (equation_iff X Y).mpr
    simp only [curve, zero_mul, add_zero]
    linear_combination hcurve
  have hns : (curve lam).Nonsingular X Y := by
    apply (nonsingular_iff' X Y).mpr
    refine ⟨heq, Or.inr ?_⟩
    simpa [curve] using mul_ne_zero (by norm_num : (2 : F) ≠ 0) hy0
  have hyne : Y ≠ (curve lam).negY X Y := by
    intro he
    have ht : 2 * Y = 0 := by
      simp only [curve, negY, zero_mul, sub_zero] at he
      linear_combination he
    exact (mul_ne_zero (by norm_num : (2 : F) ≠ 0) hy0) ht
  have hnum : 3 * X ^ 2 - 2 * (1 + lam) * X + lam =
      -(2 * Y) * (a + b + c) := by
    calc
      _ = (X - 1) * (X - lam) + X * (X - lam) + X * (X - 1) := by ring
      _ = _ := by
        rw [hX1, hXl]
        dsimp [X, Y]
        ring
  have hslope : (curve lam).slope X X Y Y = -(a + b + c) := by
    rw [slope_of_Y_ne rfl hyne]
    simp only [curve, negY, zero_mul, sub_zero]
    rw [show 3 * X ^ 2 + 2 * -(1 + lam) * X + lam =
      3 * X ^ 2 - 2 * (1 + lam) * X + lam by ring, hnum]
    field_simp
    ring
  have hxdouble : (curve lam).addX X X ((curve lam).slope X X Y Y) = x := by
    rw [hslope]
    dsimp [curve, addX, X]
    linear_combination -ha + hb + hc
  have hydouble : (curve lam).addY X X Y ((curve lam).slope X X Y Y) = y := by
    unfold addY
    rw [hxdouble]
    unfold negAddY
    rw [hxdouble, hslope]
    dsimp [curve, negY, X, Y]
    linear_combination -(a + b + c) * ha - habc
  refine ⟨Point.some X Y hns, ?_⟩
  rw [Point.add_self_of_Y_ne hyne, Point.some.injEq]
  exact ⟨hxdouble, hydouble⟩

/-- For a finite non-two-torsion point, the two square coordinates are a complete criterion. -/
theorem exists_half_iff_square_coordinates {lam x y : F}
    (hl0 : lam ≠ 0) (hl1 : lam ≠ 1) (hy : y ≠ 0)
    (hP : (curve lam).Nonsingular x y) :
    (∃ R : (curve lam).Point, R + R = Point.some x y hP) ↔
      IsSquare x ∧ IsSquare (x - 1) := by
  constructor
  · rintro ⟨R, hR⟩
    constructor
    · by_contra hx
      exact point_not_double_of_x_not_square hP hx R hR
    · by_contra hx
      exact point_not_double_of_x_sub_one_not_square hP hx R hR
  · rintro ⟨hx, hx1⟩
    obtain ⟨a, ha⟩ := hx.exists_sq
    obtain ⟨b, hb⟩ := hx1.exists_sq
    have he := (equation_iff x y).mp ((nonsingular_iff' x y).mp hP).1
    simp only [curve, zero_mul, add_zero] at he
    have hfac : y ^ 2 = x * (x - 1) * (x - lam) := by linear_combination he
    have hprod : x * (x - 1) * (x - lam) ≠ 0 := by
      rw [← hfac]
      exact pow_ne_zero 2 hy
    have hx0 : x ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).1).1
    have hx10 : x - 1 ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).1).2
    have ha0 : a ≠ 0 := by intro hz; simp [hz] at ha; exact hx0 ha
    have hb0 : b ≠ 0 := by intro hz; simp [hz] at hb; exact hx10 hb
    apply exists_half_of_square_roots hl0 hl1 hP ha.symm hb.symm (c := -y / (a * b))
    · rw [div_pow, neg_sq, mul_pow, ← ha, ← hb, hfac]
      field_simp
    · field_simp

end GaloisForLFunctions.HTGeometry.LegendreDoubling
