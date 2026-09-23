import Mathlib

/-!
# The ordered theta-Mellin pair kernel is a Krein plane

In the absolute-convergence half-plane, every theta source atom has a common
archimedean Mellin factor and an arithmetic coordinate of the form
`exp (-w * log n)`.  After differentiating the completed sum, the real
ordered-pair core is therefore affine in the sum of the two logarithmic
coordinates:

`K(u,v) = C - d * (u + v)`.

This file proves the exact two-point determinant law.  On any two distinct
logarithmic coordinates, and for every nonzero derivative coefficient `d`,
the determinant is strictly negative.  Positive diagonal weights do not
change this conclusion.  Thus the ordered-pair kernel is a Krein plane, not a
positive Gram kernel.  No zeta-zero hypothesis or positivity assumption is
used.
-/

namespace RHTower

noncomputable section

/-- The real affine-logarithmic core of an ordered Mellin pair. -/
def thetaMellinPairCore (C d u v : ℝ) : ℝ :=
  C - d * (u + v)

/-- The affine-logarithmic pair core is symmetric. -/
theorem thetaMellinPairCore_comm (C d u v : ℝ) :
    thetaMellinPairCore C d u v = thetaMellinPairCore C d v u := by
  simp [thetaMellinPairCore, add_comm]

/-- Exact two-point determinant.  The archimedean constant `C` cancels
completely; only the logarithmic separation survives. -/
theorem thetaMellinPairCore_twoPoint_det (C d u v : ℝ) :
    thetaMellinPairCore C d u u * thetaMellinPairCore C d v v -
        thetaMellinPairCore C d u v * thetaMellinPairCore C d v u =
      -(d * (u - v)) ^ (2 : ℕ) := by
  simp only [thetaMellinPairCore]
  ring

/-- Distinct logarithmic coordinates force a strictly negative determinant
whenever the differentiated Mellin coefficient is nonzero. -/
theorem thetaMellinPairCore_twoPoint_det_neg
    {C d u v : ℝ} (hd : d ≠ 0) (huv : u ≠ v) :
    thetaMellinPairCore C d u u * thetaMellinPairCore C d v v -
        thetaMellinPairCore C d u v * thetaMellinPairCore C d v u < 0 := by
  rw [thetaMellinPairCore_twoPoint_det]
  exact neg_lt_zero.mpr (sq_pos_of_ne_zero (mul_ne_zero hd (sub_ne_zero.mpr huv)))

/-- The quadratic form of a two-point affine-logarithmic block. -/
def thetaMellinPairQuadratic
    (C d u v x y : ℝ) : ℝ :=
  x ^ (2 : ℕ) * thetaMellinPairCore C d u u +
    2 * x * y * thetaMellinPairCore C d u v +
    y ^ (2 : ℕ) * thetaMellinPairCore C d v v

/-- Light-cone normal form of the two-point quadratic block. -/
theorem thetaMellinPairQuadratic_eq
    (C d u v x y : ℝ) :
    thetaMellinPairQuadratic C d u v x y =
      (x + y) * (C * (x + y) - 2 * d * (u * x + v * y)) := by
  simp only [thetaMellinPairQuadratic, thetaMellinPairCore]
  ring

/-- A nondegenerate two-point block represents every real scalar.  In
particular it contains explicit positive and negative directions. -/
theorem exists_thetaMellinPairQuadratic_eq
    {C d u v : ℝ} (hd : d ≠ 0) (huv : u ≠ v) (target : ℝ) :
    ∃ x y : ℝ, thetaMellinPairQuadratic C d u v x y = target := by
  let t : ℝ := (C - target) / (2 * d)
  let x : ℝ := (v - t) / (v - u)
  let y : ℝ := (t - u) / (v - u)
  have hvu : v - u ≠ 0 := sub_ne_zero.mpr huv.symm
  have htwoD : 2 * d ≠ 0 := mul_ne_zero (by norm_num) hd
  refine ⟨x, y, ?_⟩
  rw [thetaMellinPairQuadratic_eq]
  dsimp [x, y, t]
  field_simp [hvu, htwoD]
  ring

/-- Every nondegenerate two-point block has both orientations. -/
theorem thetaMellinPairQuadratic_has_both_signs
    {C d u v : ℝ} (hd : d ≠ 0) (huv : u ≠ v) :
    (∃ x y : ℝ, 0 < thetaMellinPairQuadratic C d u v x y) ∧
      ∃ x y : ℝ, thetaMellinPairQuadratic C d u v x y < 0 := by
  obtain ⟨xp, yp, hp⟩ := exists_thetaMellinPairQuadratic_eq hd huv 1
  obtain ⟨xn, yn, hn⟩ := exists_thetaMellinPairQuadratic_eq hd huv (-1)
  exact ⟨⟨xp, yp, by rw [hp]; norm_num⟩, ⟨xn, yn, by rw [hn]; norm_num⟩⟩

/-- Positive Mellin amplitudes enter by diagonal congruence. -/
def thetaMellinWeightedPairCore
    (C d : ℝ) (weight logCoordinate : α → ℝ) (i j : α) : ℝ :=
  weight i * weight j *
    thetaMellinPairCore C d (logCoordinate i) (logCoordinate j)

/-- Exact determinant after arbitrary diagonal weighting. -/
theorem thetaMellinWeightedPairCore_twoPoint_det
    (C d : ℝ) (weight logCoordinate : α → ℝ) (i j : α) :
    thetaMellinWeightedPairCore C d weight logCoordinate i i *
          thetaMellinWeightedPairCore C d weight logCoordinate j j -
        thetaMellinWeightedPairCore C d weight logCoordinate i j *
          thetaMellinWeightedPairCore C d weight logCoordinate j i =
      -(weight i * weight j * d *
          (logCoordinate i - logCoordinate j)) ^ (2 : ℕ) := by
  simp only [thetaMellinWeightedPairCore, thetaMellinPairCore]
  ring

/-- Every two distinct nonzero-weight source atoms span an indefinite
two-dimensional pair block. -/
theorem thetaMellinWeightedPairCore_twoPoint_det_neg
    {C d : ℝ} {weight logCoordinate : α → ℝ} {i j : α}
    (hwi : weight i ≠ 0) (hwj : weight j ≠ 0)
    (hd : d ≠ 0) (hlog : logCoordinate i ≠ logCoordinate j) :
    thetaMellinWeightedPairCore C d weight logCoordinate i i *
          thetaMellinWeightedPairCore C d weight logCoordinate j j -
        thetaMellinWeightedPairCore C d weight logCoordinate i j *
          thetaMellinWeightedPairCore C d weight logCoordinate j i < 0 := by
  rw [thetaMellinWeightedPairCore_twoPoint_det]
  apply neg_lt_zero.mpr
  apply sq_pos_of_ne_zero
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hwi hwj) hd)
    (sub_ne_zero.mpr hlog)

/-- The oscillatory Mellin phase attached to an ordered logarithmic pair. -/
def thetaMellinPairPhase (b u v : ℝ) : ℂ :=
  Complex.exp (((b * (v - u) : ℝ) : ℂ) * Complex.I)

/-- Reversing an ordered pair cancels its unitary phase exactly. -/
theorem thetaMellinPairPhase_mul_swap (b u v : ℝ) :
    thetaMellinPairPhase b u v * thetaMellinPairPhase b v u = 1 := by
  rw [thetaMellinPairPhase, thetaMellinPairPhase, ← Complex.exp_add]
  push_cast
  ring_nf
  simp

/-- The complex ordered-pair core including its diagonal unitary phase. -/
def thetaMellinPhasedPairCore (C d b u v : ℝ) : ℂ :=
  thetaMellinPairPhase b u v * (thetaMellinPairCore C d u v : ℂ)

/-- The oscillatory phase disappears from every two-point determinant. -/
theorem thetaMellinPhasedPairCore_twoPoint_det (C d b u v : ℝ) :
    thetaMellinPhasedPairCore C d b u u *
          thetaMellinPhasedPairCore C d b v v -
        thetaMellinPhasedPairCore C d b u v *
          thetaMellinPhasedPairCore C d b v u =
      -((d * (u - v)) ^ (2 : ℕ) : ℝ) := by
  have hdiagU : thetaMellinPairPhase b u u = 1 := by
    simp [thetaMellinPairPhase]
  have hdiagV : thetaMellinPairPhase b v v = 1 := by
    simp [thetaMellinPairPhase]
  have hswap := thetaMellinPairPhase_mul_swap b u v
  rw [thetaMellinPhasedPairCore, thetaMellinPhasedPairCore,
    thetaMellinPhasedPairCore, thetaMellinPhasedPairCore,
    hdiagU, hdiagV, one_mul, one_mul]
  calc
    (thetaMellinPairCore C d u u : ℂ) *
          thetaMellinPairCore C d v v -
        (thetaMellinPairPhase b u v * thetaMellinPairCore C d u v) *
          (thetaMellinPairPhase b v u * thetaMellinPairCore C d v u) =
      ((thetaMellinPairCore C d u u * thetaMellinPairCore C d v v -
          thetaMellinPairCore C d u v * thetaMellinPairCore C d v u : ℝ) : ℂ) := by
            rw [mul_mul_mul_comm, hswap, one_mul]
            push_cast
            rfl
    _ = -((d * (u - v)) ^ (2 : ℕ) : ℝ) := by
      rw [thetaMellinPairCore_twoPoint_det]
      push_cast
      rfl

end

end RHTower
