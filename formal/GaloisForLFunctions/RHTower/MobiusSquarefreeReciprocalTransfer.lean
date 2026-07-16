import GaloisForLFunctions.RHTower.InfiniteMobiusLaplaceMultiplier

/-!
# The Möbius contraction carries the reciprocal squarefree Euler transfer

The actual normalized all-prime Möbius shift has Laplace multiplier

`ζ(2σ) / (ζ(σ) ζ(σ + πx))`.

The higher-trace squarefree correction `ζ(2(σ+πx))/ζ(2σ)` is holomorphic and nonzero on the
Euler half-plane.  Their product is exactly the reciprocal squarefree Euler factor, with only the
base normalization `ζ(σ)⁻¹` left over.  Thus the first-trace reciprocal transfer is already the
characteristic multiplier of the source Möbius contraction, not a divisor-defined response.
-/

open Complex

noncomputable section

namespace RHTower

/-- The harmless higher-trace correction from the Möbius multiplier to the reciprocal
squarefree Euler multiplier. -/
def mobiusSquarefreeSafeCorrection (sigma x : ℝ) : ℂ :=
  riemannZeta (2 * (((sigma + Real.pi * x : ℝ) : ℂ))) /
    riemannZeta (2 * (sigma : ℂ))

/-- The source-defined reciprocal squarefree transfer. -/
def mobiusSquarefreeReciprocalTransfer (sigma x : ℝ) : ℂ :=
  mobiusSquarefreeSafeCorrection sigma x * infiniteMobiusLaplaceMultiplier sigma x

/-- The safe correction cancels the fixed second-trace normalization and leaves exactly the
reciprocal squarefree Euler factor, normalized at the base by `ζ(σ)⁻¹`. -/
theorem mobiusSquarefreeReciprocalTransfer_eq
    {sigma x : ℝ} (hsigma : 1 < sigma) (hx : 0 ≤ x) :
    mobiusSquarefreeReciprocalTransfer sigma x =
      riemannZeta (2 * (((sigma + Real.pi * x : ℝ) : ℂ))) /
        (riemannZeta (sigma : ℂ) *
          riemannZeta (((sigma + Real.pi * x : ℝ) : ℂ))) := by
  have htwoSigma : riemannZeta (2 * (sigma : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      simp
      linarith)
  rw [mobiusSquarefreeReciprocalTransfer, mobiusSquarefreeSafeCorrection,
    infiniteMobiusLaplaceMultiplier_eq_zetaRatio hsigma hx]
  field_simp [htwoSigma]

/-- Multiplying back the base residue normalization recovers the literal reciprocal squarefree
Euler quotient `ζ(2s)/ζ(s)`. -/
theorem riemannZeta_mul_mobiusSquarefreeReciprocalTransfer_eq
    {sigma x : ℝ} (hsigma : 1 < sigma) (hx : 0 ≤ x) :
    riemannZeta (sigma : ℂ) * mobiusSquarefreeReciprocalTransfer sigma x =
      riemannZeta (2 * (((sigma + Real.pi * x : ℝ) : ℂ))) /
        riemannZeta (((sigma + Real.pi * x : ℝ) : ℂ)) := by
  have hsigmaZeta : riemannZeta (sigma : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hsigma)
  have hshiftZeta :
      riemannZeta (((sigma + Real.pi * x : ℝ) : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      simp
      nlinarith [Real.pi_pos])
  rw [mobiusSquarefreeReciprocalTransfer_eq hsigma hx]
  field_simp [hsigmaZeta, hshiftZeta]

end RHTower

