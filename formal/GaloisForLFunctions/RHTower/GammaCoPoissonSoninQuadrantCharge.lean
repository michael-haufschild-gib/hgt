import GaloisForLFunctions.RHTower.GammaCoPoissonSoninQuadrantSection
import GaloisForLFunctions.RHTower.XiHypertranscendentalModularResidueTransgression

/-!
# The quadrant escape exponent is the centered Xi divisor charge

The modulus of the ladder character is `r^(Re w - 1/2)`, so its logarithm is the horizontal
displacement of `w` scaled by `log r`.  The displacement is exactly the normalized shell-transfer
entropy, and the centered affine Xi boundary residue at a divisor point of order `n` is `n` times
that entropy.  Hence the escape exponent of the quadrant section is the centered Xi divisor charge
divided by the multiplicity, and it vanishes exactly on the critical line.
-/

open Complex Real

noncomputable section

namespace RHTower

/-- The logarithm of the ladder character is the horizontal displacement scaled by `log r`. -/
theorem log_norm_soninLadderCharacter {r : ℝ} (hr : 0 < r) (w : ℂ) :
    Real.log ‖soninLadderCharacter w r‖ = (w.re - 1 / 2) * Real.log r := by
  rw [norm_soninLadderCharacter hr, Real.log_rpow hr]

/-- The ladder exponent is the negative of the normalized shell-transfer entropy. -/
theorem log_norm_soninLadderCharacter_eq_shellTransferEntropy {r : ℝ} (hr : 0 < r) (w : ℂ) :
    Real.log ‖soninLadderCharacter w r‖ = -shellTransferEntropy w * Real.log r := by
  rw [log_norm_soninLadderCharacter hr, shellTransferEntropy_eq]
  ring

/-- **The local--cofinal--quadrant charge identity.**  At a Xi divisor point of order `n` the
ladder exponent is the centered affine Xi boundary residue divided by `n`, up to sign. -/
theorem log_norm_soninLadderCharacter_mul_eq_centeredXiAffineResidue {r : ℝ} (hr : 0 < r)
    (rho : ℂ) (n : ℤ) :
    (n : ℝ) * Real.log ‖soninLadderCharacter rho r‖ =
      -(-((rho - 1 / 2) * (n : ℂ))).re * Real.log r := by
  rw [re_centeredXiAffineResidue_eq_shellTransferEntropy rho n,
    log_norm_soninLadderCharacter_eq_shellTransferEntropy hr]
  ring

/-- The quadrant escape exponent vanishes exactly on the critical line. -/
theorem log_norm_soninLadderCharacter_eq_zero_iff {r : ℝ} (hr : 0 < r) (hr1 : 1 < r) (w : ℂ) :
    Real.log ‖soninLadderCharacter w r‖ = 0 ↔ w.re = 1 / 2 := by
  have hlogr : Real.log r ≠ 0 := ne_of_gt (Real.log_pos hr1)
  rw [log_norm_soninLadderCharacter hr, mul_eq_zero]
  simp only [hlogr, or_false]
  constructor <;> intro h <;> linarith

end RHTower
