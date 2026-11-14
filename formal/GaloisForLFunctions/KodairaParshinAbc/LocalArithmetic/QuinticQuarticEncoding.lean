import GaloisForLFunctions.HTGeometry.Polynomial.QuarticEncoding
import GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic.PowerCurveDenominators

/-!
# A quartic presentation of the quintic curve

The curve `y²+y=x⁵` is the projection of the quartic sum of squares
`(u-x²)²+(v-xu)²+(y²+y-uv)²`. The added coordinates are uniquely
determined. Every rational zero has reduced denominators
`d²,d⁵,d⁴,d⁶` in the coordinates `x,y,u,v`.
-/

namespace GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic

open MvPolynomial HTGeometry.Polynomial

/-- Three quadratic gate errors for the quintic equation. -/
def quinticQuartic : MvPolynomial (Fin 4) ℤ :=
  (X 2 - X 0 ^ 2) ^ 2 + (X 3 - X 0 * X 2) ^ 2 +
    (X 1 ^ 2 + X 1 - X 2 * X 3) ^ 2

theorem quinticQuartic_totalDegree : quinticQuartic.totalDegree ≤ 4 := by
  have hs (i : Fin 4) : (X i ^ 2 : MvPolynomial (Fin 4) ℤ).totalDegree ≤ 2 := by
    simpa only [totalDegree_X, mul_one] using totalDegree_pow (X i : MvPolynomial (Fin 4) ℤ) 2
  have hm (i j : Fin 4) : (X i * X j : MvPolynomial (Fin 4) ℤ).totalDegree ≤ 2 := by
    simpa only [totalDegree_X] using totalDegree_mul
      (X i : MvPolynomial (Fin 4) ℤ) (X j)
  have h₁ : (X 2 - X 0 ^ 2 : MvPolynomial (Fin 4) ℤ).totalDegree ≤ 2 :=
    (totalDegree_sub_le _ _).trans (max_le (by simp) (hs 0))
  have h₂ : (X 3 - X 0 * X 2 : MvPolynomial (Fin 4) ℤ).totalDegree ≤ 2 :=
    (totalDegree_sub_le _ _).trans (max_le (by simp) (hm 0 2))
  have h₃ : (X 1 ^ 2 + X 1 - X 2 * X 3 : MvPolynomial (Fin 4) ℤ).totalDegree ≤ 2 :=
    (totalDegree_sub_le _ _).trans (max_le
      ((totalDegree_add _ _).trans (max_le (hs 1) (by simp))) (hm 2 3))
  have hsquare (p : MvPolynomial (Fin 4) ℤ) (hp : p.totalDegree ≤ 2) :
      (p ^ 2).totalDegree ≤ 4 := (totalDegree_pow _ _).trans (by omega)
  exact (totalDegree_add _ _).trans (max_le
    ((totalDegree_add _ _).trans (max_le (hsquare _ h₁) (hsquare _ h₂))) (hsquare _ h₃))

private theorem three_squares_eq_zero (a b c : ℚ) :
    a ^ 2 + b ^ 2 + c ^ 2 = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have ha : a ^ 2 = 0 := by linarith only [h, sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have hb : b ^ 2 = 0 := by linarith only [h, sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have hc : c ^ 2 = 0 := by linarith only [h, sq_nonneg a, sq_nonneg b, sq_nonneg c]
    exact ⟨sq_eq_zero_iff.mp ha, sq_eq_zero_iff.mp hb, sq_eq_zero_iff.mp hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp

/-- The quartic has no extra rational points in its auxiliary fibers. -/
theorem quinticQuartic_zero_iff (w : Fin 4 → ℚ) :
    rationalEval w quinticQuartic = 0 ↔
      w 2 = w 0 ^ 2 ∧ w 3 = w 0 ^ 3 ∧ w 1 ^ 2 + w 1 = w 0 ^ 5 := by
  simp only [quinticQuartic, map_add, map_sub, map_pow, map_mul, eval₂Hom_X']
  rw [three_squares_eq_zero]
  constructor
  · rintro ⟨hu, hv, hy⟩
    have hu' := sub_eq_zero.mp hu
    have hv' : w 3 = w 0 ^ 3 := by
      calc
        w 3 = w 0 * w 2 := sub_eq_zero.mp hv
        _ = w 0 ^ 3 := by rw [hu']; ring
    refine ⟨hu', hv', ?_⟩
    calc
      w 1 ^ 2 + w 1 = w 2 * w 3 := sub_eq_zero.mp hy
      _ = w 0 ^ 5 := by rw [hu', hv']; ring
  · rintro ⟨hu, hv, hy⟩
    rw [hu, hv, hy]
    constructor
    · ring
    constructor <;> ring

/-- Exact denominator weights survive the quartic lifting. -/
theorem quinticQuartic_denominators (w : Fin 4 → ℚ)
    (hw : rationalEval w quinticQuartic = 0) :
    ∃ d : ℕ, (w 0).den = d ^ 2 ∧ (w 1).den = d ^ 5 ∧
      (w 2).den = d ^ 4 ∧ (w 3).den = d ^ 6 := by
  obtain ⟨hu, hv, hy⟩ := (quinticQuartic_zero_iff w).mp hw
  obtain ⟨d, hxden, hyden⟩ := quintic_common_denominator hy
  refine ⟨d, hxden, hyden, ?_, ?_⟩
  · rw [hu, Rat.den_pow, hxden, ← pow_mul]
  · rw [hv, Rat.den_pow, hxden, ← pow_mul]

#print axioms quinticQuartic_zero_iff
#print axioms quinticQuartic_denominators

end GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic
