import GaloisForLFunctions.HTGeometry.TwoAtomInnerErrorBudget

/-!
# Strict complete-error absorption on the inner scale interval

Separate Young inequalities allocate every ordered off-diagonal contribution
to the four proved strict diagonal budgets. Every nonzero coefficient vector
retains a positive reserve.
-/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 1500000
private theorem weighted_pair (t a b : ℝ) {W : ℝ} (hW : 0 < W) :
    2*t*|a*b| ≤ a^2/W+W*t^2*b^2 := by
  have h := div_nonneg (sq_nonneg (|a|-W*t*|b|)) hW.le
  have he : a^2/W+W*t^2*b^2-2*t*|a*b| = (|a|-W*t*|b|)^2/W := by
    rw [abs_mul,show a^2=|a|^2 by rw [sq_abs],show b^2=|b|^2 by rw [sq_abs]]
    field_simp
    <;> ring
  rw [← he] at h
  linarith only [h]
/-- All sixteen normalized entry-error contributions, with both ordered off-diagonal entries. -/
def innerEvenErrorQuadratic (q x y z w : ℝ) : ℝ :=
  let e := fun k => innerEvenErrorBound k q
  e 0*x^2+2*e 1*|x*y|+2*e 2*|x*z|+2*e 3*|x*w|+
    e 2*y^2+2*e 3*|y*z|+2*e 4*|y*w|+e 4*z^2+2*e 5*|z*w|+e 6*w^2
/-- The proved affine reserve and the complete-source extra compensation. -/
def innerEvenCoordinateReserve (q x y z w : ℝ) : ℝ :=
  x^2/1000000+y^2/10000+z^2/10+
    (500*(5-q)^2+1+(if q ≤ 9/2 then innerExtraCompensation q else 0))*w^2
/-- The complete sixteen-entry error is strictly absorbed in every nonzero direction. -/
theorem innerEvenErrorQuadratic_lt_reserve {q : ℝ} (hq : 37/10 ≤ q) (hqu : q ≤ 5)
    (x y z w : ℝ) (hc : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0) :
    innerEvenErrorQuadratic q x y z w < innerEvenCoordinateReserve q x y z w := by
  let e := fun k => innerEvenErrorBound k q
  let d : ℝ := 500*(5-q)^2+1+(if q ≤ 9/2 then innerExtraCompensation q else 0)
  let A : ℝ := e 0+1/2000000
  let B : ℝ := e 2+8000000*(e 1)^2+3/40000
  let C : ℝ := e 4+8000000*(e 2)^2+40000*(e 3)^2+1/20
  let D : ℝ := e 6+4000000*(e 3)^2+20000*(e 4)^2+20*(e 5)^2
  have hA : A < 1/1000000 := by
    have h := innerEvenErrorBound_zero hq
    dsimp [A,e]; linarith
  have hB : B < 1/10000 := by
    have h := innerEvenErrorBound_one hq
    dsimp [B,e]; linarith
  have hC : C < 1/10 := by
    have h := innerEvenErrorBound_two hq
    dsimp [C,e]; linarith
  have hD : D < d := by
    dsimp [D,d,e]
    split_ifs with hl
    · exact innerEvenErrorBound_three_lower hq hl
    · simpa using innerEvenErrorBound_three_upper (by linarith) hqu
  have h01 := weighted_pair (e 1) x y (W:=8000000) (by norm_num)
  have h02 := weighted_pair (e 2) x z (W:=8000000) (by norm_num)
  have h03 := weighted_pair (e 3) x w (W:=4000000) (by norm_num)
  have h12 := weighted_pair (e 3) y z (W:=40000) (by norm_num)
  have h13 := weighted_pair (e 4) y w (W:=20000) (by norm_num)
  have h23 := weighted_pair (e 5) z w (W:=20) (by norm_num)
  have hsum : innerEvenErrorQuadratic q x y z w ≤ A*x^2+B*y^2+C*z^2+D*w^2 := by
    dsimp [innerEvenErrorQuadratic,A,B,C,D,e] at *
    nlinarith only [h01,h02,h03,h12,h13,h23]
  have hAp : 0 < 1/1000000-A := by linarith
  have hBp : 0 < 1/10000-B := by linarith
  have hCp : 0 < 1/10-C := by linarith
  have hDp : 0 < d-D := by linarith
  have hgap : 0 < (1/1000000-A)*x^2+(1/10000-B)*y^2+(1/10-C)*z^2+(d-D)*w^2 := by
    rcases hc with hx | hy | hz | hw
    · have : 0 < x^2 := sq_pos_of_ne_zero hx
      positivity
    · have : 0 < y^2 := sq_pos_of_ne_zero hy
      positivity
    · have : 0 < z^2 := sq_pos_of_ne_zero hz
      positivity
    · have : 0 < w^2 := sq_pos_of_ne_zero hw
      positivity
  dsimp [innerEvenCoordinateReserve]
  change _ < x^2/1000000+y^2/10000+z^2/10+d*w^2
  nlinarith only [hsum,hgap]
end
end HTGeometry
