import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedThreePositiveOrientationLaw

open Matrix

namespace RHTower

noncomputable section

/-- A real palindromic Toeplitz four-point kernel. -/
def toeplitzFour (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![a, b, c, d;
     b, a, b, c;
     c, b, a, b;
     d, c, b, a]

/-- Reflection-even block of a palindromic four-point kernel. -/
def toeplitzFourPlusBlock (a b c d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a + d, b + c;
     b + c, a + b]

/-- Reflection-odd block of a palindromic four-point kernel. -/
def toeplitzFourMinusBlock (a b c d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a - d, b - c;
     b - c, a - b]

def toeplitzFourEvenCoordinates (v : Fin 4 → ℝ) : Fin 2 → ℝ :=
  ![v 0 + v 3, v 1 + v 2]

def toeplitzFourOddCoordinates (v : Fin 4 → ℝ) : Fin 2 → ℝ :=
  ![v 0 - v 3, v 1 - v 2]

def symmetricTwoByTwo (p q r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p, q;
     q, r]

theorem symmetricTwoByTwo_isHermitian (p q r : ℝ) :
    (symmetricTwoByTwo p q r).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symmetricTwoByTwo]

theorem symmetricTwoByTwo_quadratic (p q r : ℝ) (v : Fin 2 → ℝ) :
    star v ⬝ᵥ (symmetricTwoByTwo p q r).mulVec v =
      p * v 0 ^ (2 : ℕ) + 2 * q * v 0 * v 1 + r * v 1 ^ (2 : ℕ) := by
  simp [symmetricTwoByTwo, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring

theorem symmetricTwoByTwo_posSemidef_iff_det_nonneg_of_pos_left
    {p q r : ℝ} (hp : 0 < p) :
    Matrix.PosSemidef (symmetricTwoByTwo p q r) ↔
      0 ≤ p * r - q ^ (2 : ℕ) := by
  constructor
  · intro h
    have hnonneg := h.dotProduct_mulVec_nonneg ![-q, p]
    rw [symmetricTwoByTwo_quadratic] at hnonneg
    norm_num at hnonneg
    nlinarith
  · intro hdet
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (symmetricTwoByTwo_isHermitian p q r) fun v => ?_
    rw [symmetricTwoByTwo_quadratic]
    have hidentity :
        p * v 0 ^ (2 : ℕ) + 2 * q * v 0 * v 1 + r * v 1 ^ (2 : ℕ) =
          (p * v 0 + q * v 1) ^ (2 : ℕ) / p +
            (p * r - q ^ (2 : ℕ)) / p * v 1 ^ (2 : ℕ) := by
      field_simp [hp.ne']
      ring
    rw [hidentity]
    exact add_nonneg (div_nonneg (sq_nonneg _) hp.le)
      (mul_nonneg (div_nonneg hdet hp.le) (sq_nonneg _))

theorem toeplitzFour_quadratic_parity_decomposition
    (a b c d : ℝ) (v : Fin 4 → ℝ) :
    star v ⬝ᵥ (toeplitzFour a b c d).mulVec v =
      (1 / 2 : ℝ) *
        (star (toeplitzFourEvenCoordinates v) ⬝ᵥ
          (toeplitzFourPlusBlock a b c d).mulVec (toeplitzFourEvenCoordinates v) +
        star (toeplitzFourOddCoordinates v) ⬝ᵥ
          (toeplitzFourMinusBlock a b c d).mulVec (toeplitzFourOddCoordinates v)) := by
  simp [toeplitzFour, toeplitzFourPlusBlock, toeplitzFourMinusBlock,
    toeplitzFourEvenCoordinates, toeplitzFourOddCoordinates, dotProduct,
    Matrix.mulVec, Fin.sum_univ_succ]
  ring

theorem toeplitzFour_isHermitian (a b c d : ℝ) :
    (toeplitzFour a b c d).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toeplitzFour]

theorem toeplitzFourPlusBlock_isHermitian (a b c d : ℝ) :
    (toeplitzFourPlusBlock a b c d).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toeplitzFourPlusBlock]

theorem toeplitzFourMinusBlock_isHermitian (a b c d : ℝ) :
    (toeplitzFourMinusBlock a b c d).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toeplitzFourMinusBlock]

theorem toeplitzFour_posSemidef_of_blocks
    {a b c d : ℝ}
    (hplus : Matrix.PosSemidef (toeplitzFourPlusBlock a b c d))
    (hminus : Matrix.PosSemidef (toeplitzFourMinusBlock a b c d)) :
    Matrix.PosSemidef (toeplitzFour a b c d) := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (toeplitzFour_isHermitian a b c d) fun v => ?_
  rw [toeplitzFour_quadratic_parity_decomposition]
  have hplusNonneg := hplus.dotProduct_mulVec_nonneg
    (toeplitzFourEvenCoordinates v)
  have hminusNonneg := hminus.dotProduct_mulVec_nonneg
    (toeplitzFourOddCoordinates v)
  positivity

theorem toeplitzFourPlusBlock_posSemidef_of_toeplitzFour
    {a b c d : ℝ}
    (hfour : Matrix.PosSemidef (toeplitzFour a b c d)) :
    Matrix.PosSemidef (toeplitzFourPlusBlock a b c d) := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (toeplitzFourPlusBlock_isHermitian a b c d) fun s => ?_
  let v : Fin 4 → ℝ := ![s 0 / 2, s 1 / 2, s 1 / 2, s 0 / 2]
  have hfourNonneg := hfour.dotProduct_mulVec_nonneg v
  have heven : toeplitzFourEvenCoordinates v = s := by
    funext i
    fin_cases i <;> simp [toeplitzFourEvenCoordinates, v]
  have hodd : toeplitzFourOddCoordinates v = 0 := by
    funext i
    fin_cases i <;> simp [toeplitzFourOddCoordinates, v]
  rw [toeplitzFour_quadratic_parity_decomposition] at hfourNonneg
  rw [heven, hodd] at hfourNonneg
  simpa using hfourNonneg

theorem toeplitzFourMinusBlock_posSemidef_of_toeplitzFour
    {a b c d : ℝ}
    (hfour : Matrix.PosSemidef (toeplitzFour a b c d)) :
    Matrix.PosSemidef (toeplitzFourMinusBlock a b c d) := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (toeplitzFourMinusBlock_isHermitian a b c d) fun s => ?_
  let v : Fin 4 → ℝ := ![s 0 / 2, s 1 / 2, -(s 1 / 2), -(s 0 / 2)]
  have hfourNonneg := hfour.dotProduct_mulVec_nonneg v
  have heven : toeplitzFourEvenCoordinates v = 0 := by
    funext i
    fin_cases i <;> simp [toeplitzFourEvenCoordinates, v]
  have hodd : toeplitzFourOddCoordinates v = s := by
    funext i
    fin_cases i <;> simp [toeplitzFourOddCoordinates, v]
  rw [toeplitzFour_quadratic_parity_decomposition] at hfourNonneg
  rw [heven, hodd] at hfourNonneg
  simpa using hfourNonneg

theorem toeplitzFour_posSemidef_iff_blocks (a b c d : ℝ) :
    Matrix.PosSemidef (toeplitzFour a b c d) ↔
      Matrix.PosSemidef (toeplitzFourPlusBlock a b c d) ∧
        Matrix.PosSemidef (toeplitzFourMinusBlock a b c d) := by
  constructor
  · intro h
    exact ⟨toeplitzFourPlusBlock_posSemidef_of_toeplitzFour h,
      toeplitzFourMinusBlock_posSemidef_of_toeplitzFour h⟩
  · rintro ⟨hplus, hminus⟩
    exact toeplitzFour_posSemidef_of_blocks hplus hminus

/-- Determinant wall for reflection-even four-point positivity. -/
def toeplitzFourEvenParityWall (a b c d : ℝ) : ℝ :=
  (a + d) * (a + b) - (b + c) ^ (2 : ℕ)

/-- Determinant wall for reflection-odd four-point positivity. -/
def toeplitzFourOddParityWall (a b c d : ℝ) : ℝ :=
  (a - d) * (a - b) - (b - c) ^ (2 : ℕ)

theorem toeplitzFour_posSemidef_iff_parityWalls
    {a b c d : ℝ} (hplus : 0 < a + d) (hminus : 0 < a - d) :
    Matrix.PosSemidef (toeplitzFour a b c d) ↔
      0 ≤ toeplitzFourEvenParityWall a b c d ∧
        0 ≤ toeplitzFourOddParityWall a b c d := by
  rw [toeplitzFour_posSemidef_iff_blocks]
  change
    Matrix.PosSemidef (symmetricTwoByTwo (a + d) (b + c) (a + b)) ∧
      Matrix.PosSemidef (symmetricTwoByTwo (a - d) (b - c) (a - b)) ↔ _
  rw [symmetricTwoByTwo_posSemidef_iff_det_nonneg_of_pos_left hplus,
    symmetricTwoByTwo_posSemidef_iff_det_nonneg_of_pos_left hminus]
  rfl

/-- Center-mixed theta kernel on the equispaced nodes `0,t,2t,3t`. -/
def thetaCuspCenterMixedGramFourEquispaced (a t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  toeplitzFour
    (thetaCuspCenterMixedDensity a 0)
    (thetaCuspCenterMixedDensity a t)
    (thetaCuspCenterMixedDensity a (2 * t))
    (thetaCuspCenterMixedDensity a (3 * t))

def thetaCuspCenterMixedEvenParityWall (a t : ℝ) : ℝ :=
  toeplitzFourEvenParityWall
    (thetaCuspCenterMixedDensity a 0)
    (thetaCuspCenterMixedDensity a t)
    (thetaCuspCenterMixedDensity a (2 * t))
    (thetaCuspCenterMixedDensity a (3 * t))

def thetaCuspCenterMixedOddParityWall (a t : ℝ) : ℝ :=
  toeplitzFourOddParityWall
    (thetaCuspCenterMixedDensity a 0)
    (thetaCuspCenterMixedDensity a t)
    (thetaCuspCenterMixedDensity a (2 * t))
    (thetaCuspCenterMixedDensity a (3 * t))

/-- On the physical aperture, equispaced four-point positivity is exactly two parity walls. -/
theorem thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_parityWalls
    {a t : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (ht : 0 < t) :
    Matrix.PosSemidef (thetaCuspCenterMixedGramFourEquispaced a t) ↔
      0 ≤ thetaCuspCenterMixedEvenParityWall a t ∧
        0 ≤ thetaCuspCenterMixedOddParityWall a t := by
  apply toeplitzFour_posSemidef_iff_parityWalls
  · exact add_pos (thetaCuspCenterMixedDensity_pos ha0 ha 0)
      (thetaCuspCenterMixedDensity_pos ha0 ha (3 * t))
  · exact sub_pos.mpr <| thetaCuspCenterMixedDensity_lt_zero ha0 ha
      (by positivity : 0 < 3 * t)

end

end RHTower
