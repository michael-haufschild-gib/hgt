import GaloisForLFunctions.RHTower.XiWardCubicReflectionAbsorptionCompletePositivity

/-!
# Unshifted reflection absorption as a Krein--Hardy debt (W-H201)

W-H200 proves complete positivity only after translating the source convergence wall to the Hardy
boundary, and gives an exact rational counterexample for the literal unshifted denominator.  This
module identifies the entire obstruction rather than stopping at nonpositivity.

For arbitrary admissible nodes, the literal reflected residual has the exact signed factorization

`H_{-lambda} = 2 C Cᴴ - 4 Re(lambda) D K Dᴴ`,

where `K` is the right-half-plane Hardy Cauchy Gram, `C_i = (w_i-lambda)⁻¹`, and `D` is the
corresponding resolvent diagonal.  The debt carrier `D K Dᴴ` is positive semidefinite; every
strict-right centered zero gives it a strictly negative coefficient.

Thus W-H198's necessary scalar negative companion does not globalize to one pole coordinate.  On
a packet it becomes a complete Hardy-space negative channel.  This is the common structural source
of W-H200's unshifted wall and the P-G198 cross-mode polarization no-go.  A source-to-zero map must
therefore be genuinely Krein/J-contractive until a global shorting step cancels this Hardy debt.
-/

open Complex Matrix
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Algebraic one-mode Herglotz factorization under only the denominator conditions actually used
by the identity.  Unlike P-G197's positive-chamber theorem, the mode parameter may have either
sign. -/
theorem xiWardModeHerglotzPickMatrix_factorization_of_denominator_ne
    {n : ℕ} {w : Fin n → ℂ} {lam : ℂ}
    (hmode : ∀ i, w i + lam ≠ 0)
    (hpair : ∀ i j, w i + star (w j) ≠ 0) :
    xiWardModeHerglotzPickMatrix w lam =
      (2 : ℝ) •
        (xiWardCayleyResolventColumn w lam 0 *
          (xiWardCayleyResolventColumn w lam 0)ᴴ) +
      (4 * lam.re : ℝ) •
        (xiWardCayleyResolventDiagonal w lam 0 *
          rightHalfPlaneHardyCauchyGram w *
            (xiWardCayleyResolventDiagonal w lam 0)ᴴ) := by
  ext i j
  have hwi : w i + lam ≠ 0 := hmode i
  have hwj : star (w j + lam) ≠ 0 :=
    map_ne_zero (starRingEnd ℂ) |>.mpr (hmode j)
  have hwj' : star (w j) + star lam ≠ 0 := by
    simpa using hwj
  have hwij : w i + star (w j) ≠ 0 := hpair i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  rw [xiWardCayleyResolventColumn_gram_apply,
    xiWardCayleyResolventDiagonal_cauchy_apply]
  simp only [xiWardModeHerglotzPickMatrix, ofReal_zero, add_zero]
  have hreal : (lam.re : ℂ) = (lam + star lam) / 2 := by
    apply Complex.ext <;> simp
  have hstarTerm : star (2 * (w j + lam)⁻¹) =
      2 * (star (w j) + star lam)⁻¹ := by simp
  have hstarInv : star (w j + lam)⁻¹ =
      (star (w j) + star lam)⁻¹ := by simp
  rw [hstarTerm, hstarInv]
  field_simp [hwi, hwj, hwj', hwij]
  push_cast
  rw [hreal]
  ring

/-- The literal unshifted reflected residual is exactly the Herglotz mode at the negative
reflected parameter. -/
theorem xiWardCubicUnshiftedReflectedResidualPickMatrix_eq_negative_mode
    {n : ℕ} (w : Fin n → ℂ) (lam : ℂ) :
    xiWardCubicUnshiftedReflectedResidualPickMatrix w lam =
      xiWardModeHerglotzPickMatrix w (-lam) := by
  ext i j
  simp only [xiWardCubicUnshiftedReflectedResidualPickMatrix,
    xiWardModeHerglotzPickMatrix]
  congr 1

/-- Positive Hardy debt carrier forced by one reflected strict-right mode. -/
def xiWardCubicUnshiftedReflectedHardyDebt {n : ℕ}
    (w : Fin n → ℂ) (lam : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  xiWardCayleyResolventDiagonal w (-lam) 0 *
    rightHalfPlaneHardyCauchyGram w *
      (xiWardCayleyResolventDiagonal w (-lam) 0)ᴴ

/-- The globalized companion channel is positive semidefinite before its negative Krein sign is
applied. -/
theorem xiWardCubicUnshiftedReflectedHardyDebt_posSemidef
    {n : ℕ} {w : Fin n → ℂ} (hw : ∀ i, 0 < (w i).re) (lam : ℂ) :
    (xiWardCubicUnshiftedReflectedHardyDebt w lam).PosSemidef := by
  exact (rightHalfPlaneHardyCauchyGram_posSemidef hw).mul_mul_conjTranspose_same
    (xiWardCayleyResolventDiagonal w (-lam) 0)

/-- **W-H201 exact Krein--Hardy decomposition.**  In the physical source chamber, every literal
unshifted reflected residual is resolved rank-one credit minus a positively dressed Hardy debt. -/
theorem xiWardCubicUnshiftedReflectedResidualPickMatrix_signed_factorization
    {n : ℕ} {w : Fin n → ℂ} {lam : ℂ}
    (hw : ∀ i, 1 / 2 < (w i).re) (hlamHalf : lam.re < 1 / 2) :
    xiWardCubicUnshiftedReflectedResidualPickMatrix w lam =
      (2 : ℝ) •
        (xiWardCayleyResolventColumn w (-lam) 0 *
          (xiWardCayleyResolventColumn w (-lam) 0)ᴴ) +
      (-4 * lam.re : ℝ) •
        xiWardCubicUnshiftedReflectedHardyDebt w lam := by
  rw [xiWardCubicUnshiftedReflectedResidualPickMatrix_eq_negative_mode]
  rw [xiWardModeHerglotzPickMatrix_factorization_of_denominator_ne]
  · simp only [Complex.neg_re, xiWardCubicUnshiftedReflectedHardyDebt]
    congr 1
    ring
  · intro i
    intro h
    have hre := congrArg Complex.re h
    change (w i).re - lam.re = 0 at hre
    linarith [hw i, hlamHalf]
  · intro i j h
    have hre := congrArg Complex.re h
    change (w i).re + (w j).re = 0 at hre
    linarith [hw i, hw j]

/-- Every actual strict-right zero makes the Hardy debt coefficient strictly negative. -/
theorem xiWardCubicUnshiftedReflectedHardyDebt_coefficient_neg
    (q : XiRightZeroCopy) :
    -4 * (xiRightCenteredZero q).re < 0 := by
  linarith [xiRightCenteredZero_re_pos q]

end

end RHTower
