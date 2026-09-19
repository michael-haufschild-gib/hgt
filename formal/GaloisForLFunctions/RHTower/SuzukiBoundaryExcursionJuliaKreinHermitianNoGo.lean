import GaloisForLFunctions.RHTower.SuzukiBoundaryExcursionFourLabelPlucker
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolJuliaKreinMatrixCompletion

/-!
# Hermitian direct-pullback obstruction for the Suzuki boundary-excursion carrier

The literal reflected four-label Suzuki boundary-excursion carrier has coefficient form
`diag(-1, -1)`.  The actual P-G105F Julia--Krein coefficient block has positive child diagonal
`1 / 64`.  Therefore no complex matrix can obtain that P block as a Hermitian pullback of the
literal Suzuki form.

This closes only the direct finite quadratic-form identification.  It does not rule out the
required source-faithful defect intertwiner: such an intertwiner must add a genuinely indefinite
source factor (for example, a source-derived light/Krein port) before it can meet P-G105F.
-/

open Complex Matrix

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Hermitian coefficient form of the literal reflected four-label boundary-excursion carrier. -/
def suzukiBoundaryExcursionFourLabelHermitianForm : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(suzukiBoundaryExcursionFourLabelEntry31 : ℂ),
      (suzukiBoundaryExcursionFourLabelEntry32 : ℂ);
     (suzukiBoundaryExcursionFourLabelEntry41 : ℂ),
      (suzukiBoundaryExcursionFourLabelEntry42 : ℂ)]

/-- **Direct Hermitian-pullback no-go.**  The P-G105F Julia--Krein coefficient block cannot be
obtained from the literal four-label Suzuki boundary-excursion form by a single Hermitian
pullback.  The obstruction is already its positive child diagonal: every such pullback has a
nonpositive `(0,0)` real part. -/
theorem not_exists_suzukiBoundaryExcursionFourLabelHermitianPullback_eq_routePJuliaKreinBlock :
    ¬ ∃ A : Matrix (Fin 2) (Fin 2) ℂ,
      A.conjTranspose * suzukiBoundaryExcursionFourLabelHermitianForm * A =
        RHTower.routePPrimitiveBurnolJuliaKreinBlock := by
  rintro ⟨A, hA⟩
  have h00 := congrFun (congrFun hA 0) 0
  have hreal := congrArg Complex.re h00
  simp [suzukiBoundaryExcursionFourLabelHermitianForm, Matrix.mul_apply,
    Fin.sum_univ_two, Complex.mul_re,
    RHTower.routePPrimitiveBurnolJuliaKreinBlock,
    suzukiBoundaryExcursionFourLabelEntry31_eq_neg_one,
    suzukiBoundaryExcursionFourLabelEntry32_eq_zero,
    suzukiBoundaryExcursionFourLabelEntry41_eq_zero,
    suzukiBoundaryExcursionFourLabelEntry42_eq_neg_one] at hreal
  nlinarith [sq_nonneg (A 0 0).re, sq_nonneg (A 0 0).im,
    sq_nonneg (A 1 0).re, sq_nonneg (A 1 0).im]

end GaloisForLFunctions.RHTower
