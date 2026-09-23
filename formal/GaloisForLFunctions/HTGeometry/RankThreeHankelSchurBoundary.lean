import GaloisForLFunctions.HTGeometry.RankThreeHankelMixture

/-!
# Exact Schur geometry beyond pointwise Hankel positivity

A rank-three Hankel form with a strict leading rank-two block has an exact
positive-plane plus scalar-remainder decomposition. The cofactor vector
attains that remainder. No sign is imposed on the final determinant.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Quadratic form of a symmetric rank-three Hankel block. -/
def hankelThreeQuadratic (a b c d e x y z : ℝ) : ℝ :=
  a*x^(2 : ℕ) + 2*b*x*y + c*(y^(2 : ℕ)+2*x*z) + 2*d*y*z + e*z^(2 : ℕ)

/-- Division-free positive-plane plus Schur-remainder identity. -/
theorem hankelThreeQuadratic_squares (a b c d e x y z : ℝ) :
    a*(a*c-b^(2 : ℕ))*hankelThreeQuadratic a b c d e x y z =
      (a*c-b^(2 : ℕ))*(a*x+b*y+c*z)^(2 : ℕ) +
      ((a*c-b^(2 : ℕ))*y+(a*d-b*c)*z)^(2 : ℕ) +
      a*_root_.HilbertMetric.signedEvenHankelThreeDet a b c d e*z^(2 : ℕ) := by
  unfold hankelThreeQuadratic _root_.HilbertMetric.signedEvenHankelThreeDet
  ring

/-- An explicit cofactor vector removes both positive-square coordinates. -/
theorem hankelThreeQuadratic_cofactor (a b c d e : ℝ) :
    hankelThreeQuadratic a b c d e (b*d-c^(2 : ℕ)) (b*c-a*d) (a*c-b^(2 : ℕ)) =
      (a*c-b^(2 : ℕ))*_root_.HilbertMetric.signedEvenHankelThreeDet a b c d e := by
  unfold hankelThreeQuadratic _root_.HilbertMetric.signedEvenHankelThreeDet
  ring

/-- The leading plane remains strictly positive even if the final determinant is negative. -/
theorem hankelThreeQuadratic_head_pos {a b c d e x y : ℝ}
    (ha : 0 < a) (hhead : 0 < a*c-b^(2 : ℕ)) (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < hankelThreeQuadratic a b c d e x y 0 := by
  have hid : a*hankelThreeQuadratic a b c d e x y 0 =
      (a*x+b*y)^(2 : ℕ)+(a*c-b^(2 : ℕ))*y^(2 : ℕ) := by
    unfold hankelThreeQuadratic
    ring
  have hpos : 0 < a*hankelThreeQuadratic a b c d e x y 0 := by
    rw [hid]
    by_cases hy : y = 0
    · subst y
      have hx := hxy.resolve_right (by simp)
      simpa using sq_pos_of_ne_zero (mul_ne_zero ha.ne' hx)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hhead (sq_pos_of_ne_zero hy))
  exact (mul_pos_iff_of_pos_left ha).mp hpos

/-- The exact affine minimum in the final coordinate is the Schur remainder. -/
theorem hankelThreeQuadratic_schur_minimum {a b c d e : ℝ}
    (ha : 0 < a) (hhead : 0 < a*c-b^(2 : ℕ)) (x y z : ℝ) :
    _root_.HilbertMetric.signedEvenHankelThreeDet a b c d e / (a*c-b^(2 : ℕ))*z^(2 : ℕ) ≤
      hankelThreeQuadratic a b c d e x y z := by
  have h := hankelThreeQuadratic_squares a b c d e x y z
  have hsq := add_nonneg
    (mul_nonneg hhead.le (sq_nonneg (a*x+b*y+c*z)))
    (sq_nonneg ((a*c-b^(2 : ℕ))*y+(a*d-b*c)*z))
  have hd0 : a*c-b^(2 : ℕ) ≠ 0 := hhead.ne'
  apply (mul_le_mul_iff_right₀ (mul_pos ha hhead)).mp
  calc
    a*(a*c-b^(2 : ℕ))*
        (_root_.HilbertMetric.signedEvenHankelThreeDet a b c d e / (a*c-b^(2 : ℕ))*z^(2 : ℕ)) =
        a*_root_.HilbertMetric.signedEvenHankelThreeDet a b c d e*z^(2 : ℕ) := by
      field_simp
    _ ≤ a*(a*c-b^(2 : ℕ))*hankelThreeQuadratic a b c d e x y z := by linarith

/-- Exact block diagonalization; the triangular coordinate change leaves the positive plane. -/
theorem hankelThreeQuadratic_schur_split {a b c d e : ℝ}
    (hhead : a*c-b^(2 : ℕ) ≠ 0) (x y z : ℝ) :
    hankelThreeQuadratic a b c d e
      (x+(b*d-c^(2 : ℕ))/(a*c-b^(2 : ℕ))*z) (y+(b*c-a*d)/(a*c-b^(2 : ℕ))*z) z =
      hankelThreeQuadratic a b c d e x y 0 +
      _root_.HilbertMetric.signedEvenHankelThreeDet a b c d e/(a*c-b^(2 : ℕ))*z^(2 : ℕ) := by
  unfold hankelThreeQuadratic _root_.HilbertMetric.signedEvenHankelThreeDet
  field_simp
  ring

end
end GaloisForLFunctions.HTGeometry
