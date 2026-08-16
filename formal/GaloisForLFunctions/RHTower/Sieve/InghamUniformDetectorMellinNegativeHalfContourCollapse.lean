import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinNegativeHalfHorizontalDecay

open Complex Filter Set Topology MeasureTheory intervalIntegral

namespace RHTower.Sieve

noncomputable section

/-- The selected Euler-line integral on the right edge of Route T's buffered rectangle. -/
def inghamRouteTBufferedSelectedTwoRightEdge (X : ℕ) : ℂ :=
  ∫ t in (-inghamRouteTBufferedNegativeHalfHeight X)..
      inghamRouteTBufferedNegativeHalfHeight X,
    zetaLogDerivReg ((2 : ℂ) + (t : ℂ) * I) *
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X)
        ((2 : ℂ) + (t : ℂ) * I)

/-- Complete zero packet inside Route T's selected buffered rectangle. -/
def inghamRouteTBufferedSelectedNegativeHalfZeroPacket (X : ℕ) : ℂ :=
  routeTNormalizedZetaRegularMellinZeroPacket
    (inghamRouteTMellinPhysicalCenter X)
    (inghamRouteTMellinBufferedPhysicalWidth X) (-1 / 2) 2
    (inghamRouteTBufferedNegativeHalfHeight X)

/-- Exact synchronized contour collapse: the arithmetic right edge and complete zero packet are
the sum of the three error edges, all selected at one common height. -/
theorem routeTBufferedNegativeHalf_contour_collapse
    {X : ℕ} (hX : 12 ≤ X) :
    I • inghamRouteTBufferedSelectedTwoRightEdge X +
        inghamRouteTBufferedSelectedNegativeHalfZeroPacket X =
      I • inghamRouteTBufferedSelectedNegativeHalfLeftEdge X +
        inghamRouteTBufferedNegativeHalfTopEdge X -
        inghamRouteTBufferedNegativeHalfBottomEdge X := by
  have hboundary := routeTBufferedNegativeHalfBoundary_eq_neg_zeroPacket hX
  simp only [routeTNormalizedZetaRegularMellinBoundary,
    inghamRouteTBufferedSelectedTwoRightEdge,
    inghamRouteTBufferedSelectedNegativeHalfLeftEdge,
    inghamRouteTBufferedNegativeHalfTopEdge,
    inghamRouteTBufferedNegativeHalfBottomEdge,
    inghamRouteTBufferedSelectedNegativeHalfZeroPacket] at hboundary ⊢
  norm_num [smul_eq_mul] at hboundary ⊢
  linear_combination hboundary

/-- Route T's fixed `Re s = -1/2` rectangle has no asymptotic boundary contribution away from
the arithmetic Euler edge and its complete enclosed zero packet. -/
theorem tendsto_routeTBufferedNegativeHalf_rightEdge_add_zeroPacket_zero :
    Tendsto (fun X : ℕ =>
      I • inghamRouteTBufferedSelectedTwoRightEdge X +
        inghamRouteTBufferedSelectedNegativeHalfZeroPacket X)
      atTop (nhds 0) := by
  have hrhs : Tendsto (fun X : ℕ =>
      I • inghamRouteTBufferedSelectedNegativeHalfLeftEdge X +
        inghamRouteTBufferedNegativeHalfTopEdge X -
        inghamRouteTBufferedNegativeHalfBottomEdge X)
      atTop (nhds 0) := by
    simpa using
      ((tendsto_inghamRouteTBufferedSelectedNegativeHalfLeftEdge_zero.const_smul I).add
        tendsto_inghamRouteTBufferedNegativeHalfTopEdge_zero).sub
          tendsto_inghamRouteTBufferedNegativeHalfBottomEdge_zero
  apply hrhs.congr'
  filter_upwards [eventually_ge_atTop (12 : ℕ)] with X hX
  exact (routeTBufferedNegativeHalf_contour_collapse hX).symm

end

end RHTower.Sieve
