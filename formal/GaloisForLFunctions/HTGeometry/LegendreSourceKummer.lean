import GaloisForLFunctions.HTGeometry.RatFuncOrderSquare
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.Complex.Basic

/-!
# A nonzero generic two-division class of the explicit Legendre section

Over `C(q)`, the curve with parameter `(1+2*q^2)/(1+q^2)` carries the point
`Q=((1+2*q^2)/q^2, -(1+2*q^2)/q^3)`. It is nonsingular and is not twice any
rational point of this curve. The proof uses the actual affine group law: the
coordinate `x(2R)-1` is a square, whereas `x(Q)-1=(1+q^2)/q^2` has odd order
at `q=i`.

This is a classical two-descent bridge. It does not assert that the class remains
nonzero under a meromorphic Xi pullback, nor formalize infinite order of `Q`.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.LegendreSourceKummer

open Polynomial WeierstrassCurve.Affine

abbrev K := RatFunc ℂ
local instance : DecidableEq K := Classical.decEq K
def q : K := RatFunc.X
def a : K := 1 + 2 * q ^ 2
def b : K := 1 + q ^ 2
def lam : K := a / b
def curve : WeierstrassCurve.Affine K := ⟨0, -(1 + lam), 0, lam, 0⟩
def qx : K := a / q ^ 2
def qy : K := -a / q ^ 3

theorem q_ne_zero : q ≠ 0 := RatFunc.X_ne_zero

theorem a_ne_zero : a ≠ 0 := by
  have hp : (1 + 2 * (X : Polynomial ℂ) ^ 2) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval 0) h
    norm_num at this
  have hm : algebraMap (Polynomial ℂ) K (2 : Polynomial ℂ) = 2 := by
    rw [show (2 : Polynomial ℂ) = 1 + 1 by ring, map_add, map_one]
    ring
  simpa only [a, q, map_add, map_one, map_mul, hm, map_pow, RatFunc.algebraMap_X]
    using algebraMap_polynomial_ne_zero hp

theorem b_ne_zero : b ≠ 0 := by
  have hp : (1 + (X : Polynomial ℂ) ^ 2) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval 0) h
    norm_num at this
  simpa [b, q] using algebraMap_polynomial_ne_zero hp

theorem b_order : ratOrd b Complex.I = 1 := by
  let B : Polynomial ℂ := 1 + X ^ 2
  have hp : B ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval 0) h
    norm_num [B] at this
  have hi : (C Complex.I : Polynomial ℂ) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  have hf : B = (X - C Complex.I) * (X - C (-Complex.I)) := by
    dsimp [B]
    rw [map_neg]
    linear_combination hi
  have hr : (X - C (-Complex.I) : Polynomial ℂ).rootMultiplicity Complex.I = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    simp [Polynomial.IsRoot, Complex.ext_iff]
  have he : b * algebraMap (Polynomial ℂ) K (1 : Polynomial ℂ) =
      algebraMap (Polynomial ℂ) K B := by
    simp [b, q, B]
  rw [ratOrd_of_rep hp one_ne_zero he, hf,
    Polynomial.rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    Polynomial.rootMultiplicity_X_sub_C_self, hr]
  norm_num [Polynomial.rootMultiplicity_eq_zero (p := (1 : Polynomial ℂ)) (by simp)]

theorem b_not_square : ¬ IsSquare b := by
  rintro ⟨r, hr⟩
  have hn : r ≠ 0 := by
    intro hz
    exact b_ne_zero (by simpa [hz] using hr)
  have ho := ratOrd_mul hn hn Complex.I
  rw [← hr, b_order] at ho
  omega

theorem q_equation : curve.Equation qx qy := by
  rw [equation_iff]
  dsimp [curve, qx, qy, lam, a, b]
  field_simp [q_ne_zero, show 1 + q ^ 2 ≠ 0 from b_ne_zero]
  ring

theorem q_nonsingular : curve.Nonsingular qx qy := by
  rw [nonsingular_iff']
  refine ⟨q_equation, Or.inr ?_⟩
  simpa [curve, qy] using mul_ne_zero (show (2 : K) ≠ 0 by norm_num)
    (div_ne_zero (neg_ne_zero.mpr a_ne_zero) (pow_ne_zero 3 q_ne_zero))

def sectionQ : curve.Point := Point.some qx qy q_nonsingular

theorem sectionQ_ne_zero : sectionQ ≠ 0 := Point.some_ne_zero _

theorem double_x_sub_one_square {x y : K} (h : curve.Nonsingular x y)
    (hy : y ≠ curve.negY x y) :
    IsSquare (curve.addX x x (curve.slope x x y y) - 1) := by
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

theorem sectionQ_not_double (R : curve.Point) : R + R ≠ sectionQ := by
  cases R with
  | zero =>
    exact sectionQ_ne_zero.symm
  | some x y h =>
    by_cases hy : y = curve.negY x y
    · rw [Point.add_self_of_Y_eq hy]
      exact sectionQ_ne_zero.symm
    · intro hd
      rw [Point.add_self_of_Y_ne hy] at hd
      have hx := (Point.some.inj hd).1
      have hs := double_x_sub_one_square h hy
      rw [hx] at hs
      obtain ⟨r, hr⟩ := hs
      apply b_not_square
      refine ⟨q * r, ?_⟩
      have he : q ^ 2 * (qx - 1) = b := by
        dsimp [qx, a, b]
        field_simp [q_ne_zero]
        ring
      rw [← he, hr]
      ring

end GaloisForLFunctions.HTGeometry.LegendreSourceKummer
