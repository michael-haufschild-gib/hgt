import GaloisForLFunctions.RHTower.SuzukiWardAtomicContinuousLightWeld
import GaloisForLFunctions.RHTower.SuzukiCauchyReporterSecantSharpArithmeticLocalization
import GaloisForLFunctions.RHTower.SuzukiNaturalApertureCauchyEnergyEscape

/-!
# Exact local cancellation window for the completed Suzuki Ward wall

The literal completed Ward wall is a positive finite prime wall minus a positive
regular-screw continuum.  Its Cauchy Gram cross term has the opposite sign from the raw
secant Gram.  The exact secant transition atlas therefore has a concrete source consequence:
transition-separated prime--regular pairs cannot cancel the completed wall energy; they add to
it.  Only the complementary, source-specific local window can carry cancellation.

This is a sign localization, not a cofinal estimate.  In particular it introduces neither a
positive envelope nor a replacement source.
-/

open Set
open scoped NNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open _root_.RHTower

/-- Signed cross contribution of two positive masses in the literal prime-minus-regular
Suzuki Ward wall.  The minus sign is the source sign: the regular wall is subtracted before any
Gram form is taken. -/
def suzukiCompletedWardSignedCross
    (c d : ℝ) (p q : ℝ≥0) : ℝ :=
  -(c * suzukiReporterSecantCauchyGram p q * d)

/-- A transition-separated prime--regular pair is energetically adverse: because the raw Gram
is nonpositive, its signed completed-wall cross contribution is nonnegative. -/
theorem suzukiCompletedWardSignedCross_nonneg_of_transitionSeparated
    {c d : ℝ} {p q : ℝ≥0}
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hsep : suzukiReporterSecantTransitionSeparated p q) :
    0 ≤ suzukiCompletedWardSignedCross c d p q := by
  unfold suzukiCompletedWardSignedCross
  apply neg_nonneg.mpr
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos hc
      (suzukiReporterSecantCauchyGram_nonpos_of_transitionSeparated hsep)) hd

/-- Outside the transition-separated region the literal signed cross contribution is
nonpositive, hence is the only sign channel through which prime--regular cancellation can
occur. -/
theorem suzukiCompletedWardSignedCross_nonpos_of_not_transitionSeparated
    {c d : ℝ} {p q : ℝ≥0}
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hsep : ¬ suzukiReporterSecantTransitionSeparated p q) :
    suzukiCompletedWardSignedCross c d p q ≤ 0 := by
  unfold suzukiCompletedWardSignedCross
  apply neg_nonpos.mpr
  exact mul_nonneg
    (mul_nonneg hc
      (suzukiReporterSecantCauchyGram_pos_of_not_transitionSeparated hsep).le) hd

/-- The regular continuum's actual lag at aperture `H`. -/
def suzukiRegularWardLag (H h : ℝ) (hh : h ≤ H) : ℝ≥0 :=
  ⟨H - h, sub_nonneg.mpr hh⟩

/-- The literal finite-prime coefficient used by the natural Suzuki Cauchy packet is
nonnegative, including its zero padding below index two. -/
theorem suzukiNaturalAperturePaddedWeight_nonneg
    (N : ℕ) (i : Fin (N + 1)) :
    0 ≤ suzukiNaturalAperturePaddedWeight N i := by
  unfold suzukiNaturalAperturePaddedWeight
  split <;> positivity

/-- Source-faithful sign law for one literal prime--regular pair.  Once its actual lags are
transition-separated, that pair contributes nonnegatively to the completed wall energy and so
cannot be invoked as cancellation. -/
theorem suzukiNaturalPrimeRegularSignedCross_nonneg_of_transitionSeparated
    (N : ℕ) (i : Fin (N + 1)) (h : ℝ)
    (hh : h ≤ Real.log (N : ℝ))
    (hbase : unitRieszSuzukiBase ≤ h)
    (hsep : suzukiReporterSecantTransitionSeparated
      (suzukiNaturalAperturePaddedLag N i)
      (suzukiRegularWardLag (Real.log (N : ℝ)) h hh)) :
    0 ≤ suzukiCompletedWardSignedCross
      (suzukiNaturalAperturePaddedWeight N i)
      (screwRegularKernel h)
      (suzukiNaturalAperturePaddedLag N i)
      (suzukiRegularWardLag (Real.log (N : ℝ)) h hh) := by
  apply suzukiCompletedWardSignedCross_nonneg_of_transitionSeparated
  · exact suzukiNaturalAperturePaddedWeight_nonneg N i
  · exact (screwRegularKernel_pos_of_unitRieszSuzukiBase_le hbase).le
  · exact hsep

/-- Complementary source-faithful sign law.  A prime--regular pair can lower the completed
wall energy only in the exact non-transition-separated local window. -/
theorem suzukiNaturalPrimeRegularSignedCross_nonpos_of_not_transitionSeparated
    (N : ℕ) (i : Fin (N + 1)) (h : ℝ)
    (hh : h ≤ Real.log (N : ℝ))
    (hbase : unitRieszSuzukiBase ≤ h)
    (hsep : ¬ suzukiReporterSecantTransitionSeparated
      (suzukiNaturalAperturePaddedLag N i)
      (suzukiRegularWardLag (Real.log (N : ℝ)) h hh)) :
    suzukiCompletedWardSignedCross
      (suzukiNaturalAperturePaddedWeight N i)
      (screwRegularKernel h)
      (suzukiNaturalAperturePaddedLag N i)
      (suzukiRegularWardLag (Real.log (N : ℝ)) h hh) ≤ 0 := by
  apply suzukiCompletedWardSignedCross_nonpos_of_not_transitionSeparated
  · exact suzukiNaturalAperturePaddedWeight_nonneg N i
  · exact (screwRegularKernel_pos_of_unitRieszSuzukiBase_le hbase).le
  · exact hsep

end

end GaloisForLFunctions.RHTower
