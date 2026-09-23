import GaloisForLFunctions.RHTower.XiWardCubicUnshiftedKreinHardyDebt

/-!
# Boundary-translation Schur wall (W-H202)

W-H200's shifted-positive residual and W-H201's literal Krein residual differ only by translation
of the source convergence wall.  This module isolates the universal kernel multiplier performing
that translation:

`M(z,w) = (z + conj(w)) / (z + conj(w) + 1)
        = 1 - 1 / (z + conj(w) + 1)`.

The literal residual is exactly the Hadamard product of the shifted-positive residual with `M`.
But for every two distinct positive real nodes `x,y`, the determinant of `M` is

`-(2(x+y)+1)(x-y)^(2 : ℕ) / ((2x+1)(2y+1)(x+y+1)^(2 : ℕ)) < 0`.

Hence no Schur-positive denominator transport can turn scalar/shifted functional-equation
absorption into the literal W-H190 reflection-Loewner current.  This wall is independent of Xi
zeros: the negative Hardy channel is forced by moving the convergence boundary itself.  Any live
comparison must preserve that signed channel through a Krein shorting rather than discard it by a
positive kernel multiplier.
-/

open Complex Matrix
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Universal multiplier translating the Hardy boundary by one unit. -/
def xiWardCubicBoundaryTranslationMultiplier {n : ℕ}
    (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (z i + star (z j)) / (z i + star (z j) + 1)

/-- The translation multiplier is constant rank-one credit minus the shifted Hardy Cauchy Gram. -/
theorem xiWardCubicBoundaryTranslationMultiplier_eq_one_sub_cauchy
    {n : ℕ} {z : Fin n → ℂ}
    (hden : ∀ i j, z i + star (z j) + 1 ≠ 0) :
    xiWardCubicBoundaryTranslationMultiplier z = fun i j =>
      1 - rightHalfPlaneHardyCauchyGram (fun k => z k + 1 / 2) i j := by
  ext i j
  simp only [xiWardCubicBoundaryTranslationMultiplier,
    rightHalfPlaneHardyCauchyGram]
  have h : (z i + 1 / 2) + star (z j + 1 / 2) =
      z i + star (z j) + 1 := by simp; ring
  rw [h]
  have hfrac (d : ℂ) (hd : d ≠ 0) :
      (d - 1) / d = 1 - 1 / d := by
    field_simp [hd]
  convert hfrac (z i + star (z j) + 1) (hden i j) using 1 <;> ring

set_option maxRecDepth 10000

/-- Exact negative-square determinant law on every positive real two-node packet. -/
theorem xiWardCubicBoundaryTranslationMultiplier_det_two
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (xiWardCubicBoundaryTranslationMultiplier
      ![(x : ℂ), (y : ℂ)]).det =
      ((-((2 * (x + y) + 1) * (x - y) ^ (2 : ℕ)) /
        ((2 * x + 1) * (2 * y + 1) * (x + y + 1) ^ (2 : ℕ)) : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  norm_num [xiWardCubicBoundaryTranslationMultiplier]
  field_simp [show (2 * (x : ℂ) + 1) ≠ 0 by positivity,
    show (2 * (y : ℂ) + 1) ≠ 0 by positivity,
    show ((x : ℂ) + y + 1) ≠ 0 by positivity]
  ring

set_option maxRecDepth 1000

/-- **W-H202 universal Schur wall.**  The boundary-translation multiplier fails positivity for
every pair of distinct positive real nodes. -/
theorem xiWardCubicBoundaryTranslationMultiplier_not_posSemidef
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    ¬ (xiWardCubicBoundaryTranslationMultiplier
      ![(x : ℂ), (y : ℂ)]).PosSemidef := by
  intro hpsd
  have hdet := hpsd.det_nonneg
  rw [xiWardCubicBoundaryTranslationMultiplier_det_two hx hy] at hdet
  have hreal := (RCLike.nonneg_iff.mp hdet).1
  change 0 ≤ -((2 * (x + y) + 1) * (x - y) ^ (2 : ℕ)) /
    ((2 * x + 1) * (2 * y + 1) * (x + y + 1) ^ (2 : ℕ)) at hreal
  have hsquare : 0 < (x - y) ^ (2 : ℕ) :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)
  have hnum : 0 < (2 * (x + y) + 1) * (x - y) ^ (2 : ℕ) := by positivity
  have hden : 0 < (2 * x + 1) * (2 * y + 1) * (x + y + 1) ^ (2 : ℕ) := by
    positivity
  have hneg : -((2 * (x + y) + 1) * (x - y) ^ (2 : ℕ)) /
      ((2 * x + 1) * (2 * y + 1) * (x + y + 1) ^ (2 : ℕ)) < 0 := by
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) hden
  linarith

/-- Exact Hadamard transport law from shifted-positive absorption to the literal unshifted
reflection-Loewner denominator. -/
theorem xiWardCubicUnshiftedResidual_eq_shifted_hadamard_translation
    {n : ℕ} {w : Fin n → ℂ} {lam : ℂ}
    (hshift : ∀ i j, (w i - 1 / 2) + star (w j - 1 / 2) ≠ 0)
    (hunshift : ∀ i j, w i + star (w j) ≠ 0) :
    xiWardCubicUnshiftedReflectedResidualPickMatrix w lam =
      xiWardCubicReflectedResidualPickMatrix w lam ⊙
        xiWardCubicBoundaryTranslationMultiplier
          (xiWardCubicShiftedNode w) := by
  ext i j
  simp only [Matrix.hadamard_apply]
  have hmult :
      xiWardCubicBoundaryTranslationMultiplier
          (xiWardCubicShiftedNode w) i j =
        (w i + star (w j) - 1) / (w i + star (w j)) := by
    simp only [xiWardCubicBoundaryTranslationMultiplier,
      xiWardCubicShiftedNode]
    congr 1 <;> simp <;> ring
  rw [hmult]
  simp only [xiWardCubicUnshiftedReflectedResidualPickMatrix,
    xiWardCubicReflectedResidualPickMatrix]
  have hden : w i - 1 / 2 + star (w j - 1 / 2) =
      w i + star (w j) - 1 := by simp; ring
  rw [hden]
  let A : ℂ := 2 * (w i - lam)⁻¹ + star (2 * (w j - lam)⁻¹)
  let d : ℂ := w i + star (w j)
  have hd : d ≠ 0 := by
    dsimp only [d]
    exact hunshift i j
  have hdm : d - 1 ≠ 0 := by
    dsimp only [d]
    rw [← hden]
    exact hshift i j
  have hfrac : A / d = A / (d - 1) * ((d - 1) / d) := by
    field_simp [hd, hdm]
  exact hfrac

end

end RHTower
