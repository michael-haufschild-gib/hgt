/-
# Rank-two packet moment identities: the exact 2×2 Hankel algebra of a conjugate pair

For a conjugate point pair `u± = x0 ± d·i` of common mass `m`, the signed power moments
`h j l = m·u₊^(j+l+1) + m·u₋^(j+l+1) = 2m·Re(u₊^(j+l+1))` assemble the 2×2 Hankel matrix
`H₂`. This module proves the exact finite algebra of that matrix:

* `packetMoment_zero_zero` / `packetMoment_zero_one` / `packetMoment_one_one`:
  `h₀₀ = 2m·x0`, `h₀₁ = 2m(x0² − d²)`, `h₁₁ = 2m(x0³ − 3x0·d²)`;
* `hankelDefect_eq`: `H₂ − H̃ = −2m·d² · !![0, 1; 1, 3x0]`, where
  `H̃ = 2m·x0 · vvᵀ` with `v = (1, x0)` is the rank-one moment matrix of the collision
  configuration (mass `2m` at the single real point `x0`);
* `kernelVector_quadForm`: along the shadow-kernel direction `p = (−x0, 1)` — the
  coefficient vector of `X − x0` — the quadratic form is `pᵀH₂p = −2m·x0·d²`;
* `packetHankel_det`: `det H₂ = −4m²·d²·(x0² + d²)`; with the pair window
  `W̃ = (X − x0)² + d²` (the monic real quadratic vanishing at `u₊, u₋`) this reads
  `det H₂ = m² · W̃(0) · disc(W̃)`, since `W̃(0) = x0² + d²` and
  `disc(W̃) = (−2x0)² − 4(x0² + d²) = −4d²`;
* `packetHankel_det_neg`: for `m ≠ 0` and `d ≠ 0` the determinant is strictly negative —
  a nondegenerate off-line pair makes the 2×2 moment matrix indefinite;
* `packetHankel_collision` / `collisionShadow_posSemidef`: at `d = 0` the Hankel matrix
  degenerates exactly to the shadow, which is positive semidefinite for `m ≥ 0`, `x0 ≥ 0`.

So the sign of `disc(W̃)` is exactly the sign of `det H₂ / (m²·W̃(0))`: the off-line
displacement `d` enters the moment matrix only through `d²` in the defect `Δ`, and its
only sign witness is the indefiniteness of `H₂`.
-/
import Mathlib

namespace GaloisForLFunctions
namespace RHTower
namespace RankTwoPacketMomentIdentities

open Polynomial

noncomputable section

/-! ## The packet point and its power moments -/

/-- The upper packet point `u₊ = x0 + d·i`. -/
def packetPoint (x0 d : ℝ) : ℂ := (x0 : ℂ) + d * Complex.I

/-- Signed power moment of the conjugate pair `m·δ_{u₊} + m·δ_{u₋}`:
`h j l = 2m·Re(u₊^(j+l+1))`. -/
def packetMoment (m x0 d : ℝ) (j l : ℕ) : ℝ :=
  2 * m * ((packetPoint x0 d) ^ (j + l + 1)).re

/-- The moment is the genuine two-point sum `m·u₊^(j+l+1) + m·u₋^(j+l+1)` over the
conjugate pair. -/
theorem packetMoment_eq_pair_sum (m x0 d : ℝ) (j l : ℕ) :
    ((packetMoment m x0 d j l : ℝ) : ℂ)
      = m * packetPoint x0 d ^ (j + l + 1)
        + m * (starRingEnd ℂ) (packetPoint x0 d) ^ (j + l + 1) := by
  have h := Complex.add_conj (packetPoint x0 d ^ (j + l + 1))
  rw [← map_pow]
  calc ((packetMoment m x0 d j l : ℝ) : ℂ)
      = m * ((2 * (packetPoint x0 d ^ (j + l + 1)).re : ℝ) : ℂ) := by
        unfold packetMoment; push_cast; ring
    _ = m * (packetPoint x0 d ^ (j + l + 1)
          + (starRingEnd ℂ) (packetPoint x0 d ^ (j + l + 1))) := by rw [h]
    _ = m * packetPoint x0 d ^ (j + l + 1)
          + m * (starRingEnd ℂ) (packetPoint x0 d ^ (j + l + 1)) := by ring

/-- Real part of a complex number given in Cartesian form by two real expressions. -/
theorem re_ofReal_add_ofReal_mul_I (a b : ℝ) :
    (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I).re = a := by
  simp

/-- `u₊² = (x0² − d²) + 2x0·d·i`. -/
theorem packetPoint_sq (x0 d : ℝ) :
    packetPoint x0 d ^ 2
      = ((x0 ^ 2 - d ^ 2 : ℝ) : ℂ) + ((2 * x0 * d : ℝ) : ℂ) * Complex.I := by
  unfold packetPoint
  push_cast
  linear_combination (d : ℂ) ^ 2 * Complex.I_sq

/-- `u₊³ = (x0³ − 3x0·d²) + (3x0²·d − d³)·i`. -/
theorem packetPoint_cube (x0 d : ℝ) :
    packetPoint x0 d ^ 3
      = ((x0 ^ 3 - 3 * x0 * d ^ 2 : ℝ) : ℂ)
        + ((3 * x0 ^ 2 * d - d ^ 3 : ℝ) : ℂ) * Complex.I := by
  unfold packetPoint
  push_cast
  linear_combination (3 * (x0 : ℂ) * (d : ℂ) ^ 2 + (d : ℂ) ^ 3 * Complex.I) * Complex.I_sq

/-- `h₀₀ = 2m·x0`. -/
theorem packetMoment_zero_zero (m x0 d : ℝ) : packetMoment m x0 d 0 0 = 2 * m * x0 := by
  unfold packetMoment packetPoint
  norm_num

/-- `h₀₁ = 2m·(x0² − d²)`. -/
theorem packetMoment_zero_one (m x0 d : ℝ) :
    packetMoment m x0 d 0 1 = 2 * m * (x0 ^ 2 - d ^ 2) := by
  unfold packetMoment
  rw [show (0 : ℕ) + 1 + 1 = 2 from rfl, packetPoint_sq, re_ofReal_add_ofReal_mul_I]

/-- `h₁₀ = 2m·(x0² − d²)`. -/
theorem packetMoment_one_zero (m x0 d : ℝ) :
    packetMoment m x0 d 1 0 = 2 * m * (x0 ^ 2 - d ^ 2) := by
  unfold packetMoment
  rw [show (1 : ℕ) + 0 + 1 = 2 from rfl, packetPoint_sq, re_ofReal_add_ofReal_mul_I]

/-- `h₁₁ = 2m·(x0³ − 3x0·d²)`. -/
theorem packetMoment_one_one (m x0 d : ℝ) :
    packetMoment m x0 d 1 1 = 2 * m * (x0 ^ 3 - 3 * x0 * d ^ 2) := by
  unfold packetMoment
  rw [show (1 : ℕ) + 1 + 1 = 3 from rfl, packetPoint_cube, re_ofReal_add_ofReal_mul_I]

/-! ## The 2×2 Hankel matrix, the collision shadow, and the defect -/

/-- The 2×2 packet Hankel matrix `(H₂)_{jl} = h_{jl}`. -/
def packetHankel (m x0 d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun j l : Fin 2 => packetMoment m x0 d j.val l.val

/-- Normal form of the packet Hankel matrix. -/
theorem packetHankel_eq (m x0 d : ℝ) :
    packetHankel m x0 d
      = !![2 * m * x0, 2 * m * (x0 ^ 2 - d ^ 2);
           2 * m * (x0 ^ 2 - d ^ 2), 2 * m * (x0 ^ 3 - 3 * x0 * d ^ 2)] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [packetHankel, packetMoment_zero_zero, packetMoment_zero_one,
      packetMoment_one_zero, packetMoment_one_one]

/-- Rank-one collision shadow `H̃ = 2m·x0 · vvᵀ` with `v = (1, x0)`: the moment matrix of
the collision configuration (mass `2m` at the single real point `x0`). -/
def collisionShadow (m x0 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (2 * m * x0) • Matrix.vecMulVec ![1, x0] ![1, x0]

/-- Normal form of the collision shadow. -/
theorem collisionShadow_eq (m x0 : ℝ) :
    collisionShadow m x0
      = !![2 * m * x0, 2 * m * x0 ^ 2; 2 * m * x0 ^ 2, 2 * m * x0 ^ 3] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [collisionShadow]
  all_goals ring

/-- The blindness defect `Δ = H₂ − H̃`. -/
def hankelDefect (m x0 d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  packetHankel m x0 d - collisionShadow m x0

/-- **Exact defect form**: `Δ = −2m·d² · !![0, 1; 1, 3x0]`. The off-line displacement `d`
enters the 2×2 moment matrix only through `d²`, in a fixed matrix shape independent of the
sign of `d`. -/
theorem hankelDefect_eq (m x0 d : ℝ) :
    hankelDefect m x0 d = (-(2 * m * d ^ 2)) • !![0, 1; 1, 3 * x0] := by
  rw [hankelDefect, packetHankel_eq, collisionShadow_eq]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp
  all_goals ring

/-- Decomposition `H₂ = H̃ + Δ`. -/
theorem packetHankel_eq_shadow_add_defect (m x0 d : ℝ) :
    packetHankel m x0 d = collisionShadow m x0 + hankelDefect m x0 d := by
  rw [hankelDefect]
  abel

/-! ## The shadow kernel direction -/

/-- The coefficient vector `p = (−x0, 1)` of `X − x0` annihilates the collision shadow. -/
theorem collisionShadow_mulVec_kernelVector (m x0 : ℝ) :
    (collisionShadow m x0).mulVec ![-x0, 1] = 0 := by
  rw [collisionShadow_eq]
  funext i
  fin_cases i
  all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  all_goals ring

/-- **Kernel-direction value**: `pᵀ H₂ p = −2m·x0·d²` for `p = (−x0, 1)`. Along the shadow
kernel the whole quadratic form of `H₂` is carried by the defect. -/
theorem kernelVector_quadForm (m x0 d : ℝ) :
    ![-x0, 1] ⬝ᵥ (packetHankel m x0 d).mulVec ![-x0, 1] = -(2 * m * x0 * d ^ 2) := by
  rw [packetHankel_eq]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-! ## Determinant, pair window, and discriminant -/

/-- **Determinant, explicit form**: `det H₂ = −4m²·d²·(x0² + d²)`. -/
theorem packetHankel_det (m x0 d : ℝ) :
    (packetHankel m x0 d).det = -(4 * m ^ 2 * d ^ 2 * (x0 ^ 2 + d ^ 2)) := by
  rw [packetHankel_eq, Matrix.det_fin_two_of]
  ring

/-- The pair window `W̃ = (X − x0)² + d²`: the monic real quadratic vanishing at the packet
points `u₊, u₋`. -/
def pairWindow (x0 d : ℝ) : Polynomial ℝ := (X - C x0) ^ 2 + C (d ^ 2)

/-- Monic quadratic coefficients: `W̃ = X² + (−2x0)·X + (x0² + d²)`. -/
theorem pairWindow_eq (x0 d : ℝ) :
    pairWindow x0 d = X ^ 2 + C (-(2 * x0)) * X + C (x0 ^ 2 + d ^ 2) := by
  unfold pairWindow
  simp only [map_add, map_pow, map_neg, map_mul, map_ofNat]
  ring

/-- The packet point is a root of the pair window (read in `ℂ`). -/
theorem pairWindow_aeval_packetPoint (x0 d : ℝ) :
    Polynomial.aeval (packetPoint x0 d) (pairWindow x0 d) = 0 := by
  simp only [pairWindow, packetPoint, map_add, map_sub, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C, Complex.coe_algebraMap]
  linear_combination ((d : ℂ) ^ 2) * Complex.I_sq

/-- Window value at the origin: `W̃(0) = x0² + d²`. -/
theorem pairWindow_eval_zero (x0 d : ℝ) :
    (pairWindow x0 d).eval 0 = x0 ^ 2 + d ^ 2 := by
  simp [pairWindow, eval_pow]

/-- Discriminant of the pair window in its monic coefficients: `disc(W̃) = −4d²`. -/
theorem discrim_pairWindow (x0 d : ℝ) :
    discrim 1 (-(2 * x0)) (x0 ^ 2 + d ^ 2) = -(4 * d ^ 2) := by
  rw [discrim]
  ring

/-- **Determinant identification**: `det H₂ = m² · W̃(0) · disc(W̃)`. The determinant of the
packet Hankel matrix is the pair mass squared times the window value at the origin times the
window discriminant. -/
theorem packetHankel_det_eq_mass_mul_window_mul_discrim (m x0 d : ℝ) :
    (packetHankel m x0 d).det
      = m ^ 2 * (pairWindow x0 d).eval 0 * discrim 1 (-(2 * x0)) (x0 ^ 2 + d ^ 2) := by
  rw [packetHankel_det, pairWindow_eval_zero, discrim_pairWindow]
  ring

/-! ## Indefiniteness off the line, positive semidefiniteness at the collision -/

/-- **Off-line indefiniteness**: nonzero mass and nonzero displacement force
`det H₂ < 0` — the 2×2 packet Hankel matrix of a nondegenerate off-line pair is
indefinite. -/
theorem packetHankel_det_neg (m x0 d : ℝ) (hm : m ≠ 0) (hd : d ≠ 0) :
    (packetHankel m x0 d).det < 0 := by
  rw [packetHankel_det]
  have hm2 : 0 < m ^ 2 := lt_of_le_of_ne (sq_nonneg m) (Ne.symm (pow_ne_zero 2 hm))
  have hd2 : 0 < d ^ 2 := lt_of_le_of_ne (sq_nonneg d) (Ne.symm (pow_ne_zero 2 hd))
  have hx : 0 < x0 ^ 2 + d ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg x0) hd2
  have h4 : 0 < 4 * m ^ 2 * d ^ 2 * (x0 ^ 2 + d ^ 2) :=
    mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hm2) hd2) hx
  linarith

/-- **Collision degeneration**: at `d = 0` the packet Hankel matrix is exactly the
rank-one shadow. -/
theorem packetHankel_collision (m x0 : ℝ) :
    packetHankel m x0 0 = collisionShadow m x0 := by
  rw [packetHankel_eq, collisionShadow_eq]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp

/-- **Collision shadow positivity**: for nonnegative mass and nonnegative center the
rank-one shadow `2m·x0 · vvᵀ` is positive semidefinite. -/
theorem collisionShadow_posSemidef (m x0 : ℝ) (hm : 0 ≤ m) (hx : 0 ≤ x0) :
    (collisionShadow m x0).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun v => ?_)
  · rw [collisionShadow_eq]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.conjTranspose_apply]
  · have hsv : star v = v := by funext i; simp
    rw [hsv, collisionShadow_eq]
    have hq : v ⬝ᵥ (!![2 * m * x0, 2 * m * x0 ^ 2;
        2 * m * x0 ^ 2, 2 * m * x0 ^ 3]).mulVec v
        = 2 * (m * x0) * (v 0 + x0 * v 1) ^ 2 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hq]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hm hx))
      (sq_nonneg (v 0 + x0 * v 1))

/-- At the collision the packet Hankel matrix itself is positive semidefinite. -/
theorem packetHankel_collision_posSemidef (m x0 : ℝ) (hm : 0 ≤ m) (hx : 0 ≤ x0) :
    (packetHankel m x0 0).PosSemidef := by
  rw [packetHankel_collision]
  exact collisionShadow_posSemidef m x0 hm hx

end

end RankTwoPacketMomentIdentities
end RHTower
end GaloisForLFunctions
