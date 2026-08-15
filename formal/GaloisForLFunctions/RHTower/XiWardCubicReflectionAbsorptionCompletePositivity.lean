import GaloisForLFunctions.RHTower.XiWardCubicHerglotzExternalMixedJet
import GaloisForLFunctions.RHTower.XiWardInteriorReflectionAbsorption

/-!
# Shifted complete positivity and the unshifted Loewner wall (W-H200)

The existing Ward interior theorem absorbs each strict-right boundary contact into its
functional-equation-reflected left mode only in scalar real part.  A cubic mixed jet cannot be
passed through a merely scalar inequality.  This module determines exactly how far that scalar
absorption upgrades to matrix order.

For a right-centered mode `lambda`, combine its boundary contact with its reflected resolvent:

`2 (lambda⁻¹ + (w-lambda)⁻¹)`.

After shifting the source half-plane by `1/2`, its Pick kernel splits exactly into a positive
constant Cauchy Gram and the P-G197 Herglotz kernel with parameter `1/2-lambda`.  Both coefficients
are positive precisely because `0 < Re(lambda) < 1/2`.  Therefore functional-equation absorption
is completely positive on every finite source packet, not just pointwise on the diagonal.

This upgrade does **not** survive the denominator required by the unshifted W-H190/P-G197
reflection-Loewner geometry.  At `lambda = 2/5` and the two source nodes `51/100, 7/10`, the
unshifted residual determinant is the exact negative rational

`-17328000000 / 210815759`.

Thus scalar functional-equation absorption cannot be differentiated or Schur-cubed through the
literal source Loewner kernel.  The positive survivor is a sharp domain law: complete positivity
appears only after translating the source convergence wall to the Hardy boundary.  Any completed
comparison must retain a signed/Krein channel or supply an additional denominator correction
before codiagonalization.
-/

open Complex Matrix
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Translate the physical source half-plane `Re w > 1/2` to the standard Hardy half-plane. -/
def xiWardCubicShiftedNode {N : ℕ} (w : Fin N → ℂ) : Fin N → ℂ :=
  fun i => w i - 1 / 2

/-- Pick kernel of one reflected mode together with the boundary contact it absorbs. -/
def xiWardCubicReflectedContactPickMatrix {N : ℕ}
    (w : Fin N → ℂ) (lam : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j =>
    (2 * (lam⁻¹ + (w i - lam)⁻¹) +
      star (2 * (lam⁻¹ + (w j - lam)⁻¹))) /
        ((w i - 1 / 2) + star (w j - 1 / 2))

theorem xiWardCubicShiftedNode_re_pos
    {N : ℕ} {w : Fin N → ℂ}
    (hw : ∀ i, 1 / 2 < (w i).re) :
    ∀ i, 0 < (xiWardCubicShiftedNode w i).re := by
  intro i
  simp [xiWardCubicShiftedNode]
  linarith [hw i]

/-- Exact positive factorization of the reflected-contact Pick kernel. -/
theorem xiWardCubicReflectedContactPickMatrix_factorization
    {N : ℕ} (w : Fin N → ℂ) (lam : ℂ) :
    xiWardCubicReflectedContactPickMatrix w lam =
      (4 * (lam⁻¹).re : ℝ) •
        rightHalfPlaneHardyCauchyGram (xiWardCubicShiftedNode w) +
      xiWardModeHerglotzPickMatrix (xiWardCubicShiftedNode w)
        ((1 / 2 : ℂ) - lam) := by
  ext i j
  simp only [xiWardCubicReflectedContactPickMatrix,
    xiWardCubicShiftedNode, Matrix.add_apply, Matrix.smul_apply,
    Complex.real_smul, rightHalfPlaneHardyCauchyGram,
    xiWardModeHerglotzPickMatrix]
  have hreal : ((4 * (lam⁻¹).re : ℝ) : ℂ) =
      2 * lam⁻¹ + star (2 * lam⁻¹) := by
    apply Complex.ext <;> simp [Complex.inv_re, Complex.inv_im] <;> ring
  rw [hreal]
  rw [show 2 * (lam⁻¹ + (w i - lam)⁻¹) =
      2 * lam⁻¹ + 2 * (w i - lam)⁻¹ by ring]
  rw [show star (2 * (lam⁻¹ + (w j - lam)⁻¹)) =
      star (2 * lam⁻¹) + star (2 * (w j - lam)⁻¹) by
        rw [show 2 * (lam⁻¹ + (w j - lam)⁻¹) =
          2 * lam⁻¹ + 2 * (w j - lam)⁻¹ by ring]
        exact map_add (starRingEnd ℂ) _ _]
  rw [show w i - 1 / 2 + (1 / 2 - lam) = w i - lam by ring]
  rw [show w j - 1 / 2 + (1 / 2 - lam) = w j - lam by ring]
  ring

/-- Reflected absorption is completely positive for every parameter in the open critical
half-strip. -/
theorem xiWardCubicReflectedContactPickMatrix_posSemidef
    {N : ℕ} {w : Fin N → ℂ} {lam : ℂ}
    (hw : ∀ i, 1 / 2 < (w i).re)
    (hlam0 : 0 < lam.re) (hlamHalf : lam.re < 1 / 2) :
    (xiWardCubicReflectedContactPickMatrix w lam).PosSemidef := by
  rw [xiWardCubicReflectedContactPickMatrix_factorization]
  apply Matrix.PosSemidef.add
  · apply (rightHalfPlaneHardyCauchyGram_posSemidef
      (xiWardCubicShiftedNode_re_pos hw)).smul
    have hinv : 0 < (lam⁻¹).re := re_inv_pos_of_re_pos hlam0
    positivity
  · apply xiWardModeHerglotzPickMatrix_posSemidef
      (xiWardCubicShiftedNode_re_pos hw)
    norm_num [Complex.sub_re]
    linarith

/-- Reflected-contact Pick kernel for one actual strict-right Xi copy. -/
def xiWardCubicReflectedZeroContactPickMatrix {N : ℕ}
    (w : Fin N → ℂ) (q : XiRightZeroCopy) : Matrix (Fin N) (Fin N) ℂ :=
  xiWardCubicReflectedContactPickMatrix w (xiRightCenteredZero q)

/-- **W-H200 shifted complete reflection absorption.** Every actual strict-right copy contributes
a positive reflected-contact Pick matrix after the source convergence wall has been translated
to the Hardy boundary. -/
theorem xiWardCubicReflectedZeroContactPickMatrix_posSemidef
    {N : ℕ} {w : Fin N → ℂ}
    (hw : ∀ i, 1 / 2 < (w i).re) (q : XiRightZeroCopy) :
    (xiWardCubicReflectedZeroContactPickMatrix w q).PosSemidef := by
  apply xiWardCubicReflectedContactPickMatrix_posSemidef hw
    (xiRightCenteredZero_re_pos q)
  exact (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2

/-- Pick kernel of the positive residual left after the reflected mode pays its boundary
contact.  This is the actual summand of `2 I · nonright - boundarySelfSymbol`. -/
def xiWardCubicReflectedResidualPickMatrix {N : ℕ}
    (w : Fin N → ℂ) (lam : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j =>
    (2 * (w i - lam)⁻¹ + star (2 * (w j - lam)⁻¹)) /
      ((w i - 1 / 2) + star (w j - 1 / 2))

/-- Paying the boundary contact leaves exactly a shifted P-G197 Herglotz mode. -/
theorem xiWardCubicReflectedResidualPickMatrix_eq_mode
    {N : ℕ} (w : Fin N → ℂ) (lam : ℂ) :
    xiWardCubicReflectedResidualPickMatrix w lam =
      xiWardModeHerglotzPickMatrix (xiWardCubicShiftedNode w)
        ((1 / 2 : ℂ) - lam) := by
  ext i j
  simp only [xiWardCubicReflectedResidualPickMatrix,
    xiWardModeHerglotzPickMatrix, xiWardCubicShiftedNode]
  congr 1
  congr 1 <;> ring

/-- The shifted residual complement is completely positive throughout the physical source
half-plane.  The unshifted wall below shows why this cannot be substituted directly into the
literal reflection-Loewner comparison. -/
theorem xiWardCubicReflectedResidualPickMatrix_posSemidef
    {N : ℕ} {w : Fin N → ℂ} {lam : ℂ}
    (hw : ∀ i, 1 / 2 < (w i).re) (hlamHalf : lam.re < 1 / 2) :
    (xiWardCubicReflectedResidualPickMatrix w lam).PosSemidef := by
  rw [xiWardCubicReflectedResidualPickMatrix_eq_mode]
  apply xiWardModeHerglotzPickMatrix_posSemidef
      (xiWardCubicShiftedNode_re_pos hw)
  norm_num [Complex.sub_re]
  linarith

/-- Literal residual kernel with the unshifted reflection-Loewner denominator used by
W-H190/P-G197.  Its numerator is exactly the shifted-positive residual numerator above, but its
denominator keeps the original source boundary. -/
def xiWardCubicUnshiftedReflectedResidualPickMatrix {N : ℕ}
    (w : Fin N → ℂ) (lam : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j =>
    (2 * (w i - lam)⁻¹ + star (2 * (w j - lam)⁻¹)) /
      (w i + star (w j))

/-- Exact rational certificate that the literal unshifted residual kernel is indefinite.  Both
nodes lie in `Re w > 1/2`, while `lambda = 2/5` lies in the strict-right centered half-strip. -/
theorem xiWardCubicUnshiftedReflectedResidualPickMatrix_det_witness :
    (xiWardCubicUnshiftedReflectedResidualPickMatrix
      ![(51 / 100 : ℂ), (7 / 10 : ℂ)] (2 / 5 : ℂ)).det =
      (-17328000000 / 210815759 : ℂ) := by
  rw [Matrix.det_fin_two]
  norm_num [xiWardCubicUnshiftedReflectedResidualPickMatrix]

/-- **W-H200 unshifted Loewner wall.** Scalar reflection absorption has no positive-semidefinite
upgrade for the literal unshifted source kernel, already on a two-node rational packet. -/
theorem xiWardCubicUnshiftedReflectedResidualPickMatrix_not_posSemidef :
    ¬ (xiWardCubicUnshiftedReflectedResidualPickMatrix
      ![(51 / 100 : ℂ), (7 / 10 : ℂ)] (2 / 5 : ℂ)).PosSemidef := by
  intro hpsd
  have hdet := hpsd.det_nonneg
  rw [xiWardCubicUnshiftedReflectedResidualPickMatrix_det_witness] at hdet
  have hreal := (RCLike.nonneg_iff.mp hdet).1
  norm_num at hreal

end


end RHTower
