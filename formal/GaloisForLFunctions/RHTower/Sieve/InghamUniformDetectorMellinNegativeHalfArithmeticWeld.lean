import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinNegativeHalfContourCollapse
import GaloisForLFunctions.RHTower.Sieve.ChebyshevPerronIdentity
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLeftPoleTerm
import GaloisForLFunctions.RHTower.Sieve.MaynardAdjacentAggregateCellExtraction

open Complex Filter Set Topology MeasureTheory intervalIntegral ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

/-- Literal von Mangoldt Dirichlet series tested by Route T's selected truncated Mellin edge. -/
def inghamRouteTBufferedSelectedTwoVonMangoldtEdge (X : ℕ) : ℂ :=
  ∫ t in (-inghamRouteTBufferedNegativeHalfHeight X)..
      inghamRouteTBufferedNegativeHalfHeight X,
    (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        (n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I))) *
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X)
        ((2 : ℂ) + (t : ℂ) * I)

/-- Polar continuum on the same selected edge and with the same normalized Mellin kernel. -/
def inghamRouteTBufferedSelectedTwoPoleEdge (X : ℕ) : ℂ :=
  ∫ t in (-inghamRouteTBufferedNegativeHalfHeight X)..
      inghamRouteTBufferedNegativeHalfHeight X,
    (((2 : ℂ) + (t : ℂ) * I) - 1)⁻¹ *
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X)
        ((2 : ℂ) + (t : ℂ) * I)

private theorem continuous_zetaLogDerivReg_two_line :
    Continuous (fun t : ℝ => zetaLogDerivReg ((2 : ℂ) + (t : ℂ) * I)) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hin : Continuous (fun u : ℝ => (2 : ℂ) + (u : ℂ) * I) := by fun_prop
  exact ContinuousAt.comp
    (g := zetaLogDerivReg)
    (f := fun u : ℝ => (2 : ℂ) + (u : ℂ) * I)
    (differentiableAt_zetaLogDerivReg
      (zetaResidueUnit_ne_zero_two t)).continuousAt
    hin.continuousAt

/-- The selected arithmetic edge splits coefficient-faithfully into its polar continuum and the
regular zeta edge used by the zero contour. -/
theorem inghamRouteTBufferedSelectedTwoVonMangoldtEdge_eq_pole_add_regular
    {X : ℕ} (hX : 1 ≤ X) :
    inghamRouteTBufferedSelectedTwoVonMangoldtEdge X =
      inghamRouteTBufferedSelectedTwoPoleEdge X +
        inghamRouteTBufferedSelectedTwoRightEdge X := by
  let N : ℝ := inghamRouteTMellinPhysicalCenter X
  let H : ℝ := inghamRouteTMellinBufferedPhysicalWidth X
  let T : ℝ := inghamRouteTBufferedNegativeHalfHeight X
  have hN : 0 < N := inghamRouteTMellinPhysicalCenter_pos hX
  have hH : 0 < H := inghamRouteTMellinBufferedPhysicalWidth_pos hX
  have hKcont : Continuous (fun t : ℝ =>
      routeTNormalizedSmoothWindowMellin N H
        ((2 : ℂ) + (t : ℂ) * I)) :=
    continuous_routeTNormalizedSmoothWindowMellin_line hN hH (by norm_num)
  have hlin : Continuous (fun t : ℝ => ((2 : ℂ) + (t : ℂ) * I) - 1) := by fun_prop
  have hinv : Continuous (fun t : ℝ => (((2 : ℂ) + (t : ℂ) * I) - 1)⁻¹) :=
    hlin.inv₀ fun t => sub_one_ne_zero_line_of_ne (by norm_num : (2 : ℝ) ≠ 1)
  have hpole : IntervalIntegrable (fun t : ℝ =>
      (((2 : ℂ) + (t : ℂ) * I) - 1)⁻¹ *
        routeTNormalizedSmoothWindowMellin N H
          ((2 : ℂ) + (t : ℂ) * I)) volume (-T) T :=
    (hinv.mul hKcont).intervalIntegrable _ _
  have hreg : IntervalIntegrable (fun t : ℝ =>
      zetaLogDerivReg ((2 : ℂ) + (t : ℂ) * I) *
        routeTNormalizedSmoothWindowMellin N H
          ((2 : ℂ) + (t : ℂ) * I)) volume (-T) T :=
    (continuous_zetaLogDerivReg_two_line.mul hKcont).intervalIntegrable _ _
  have hpoint (t : ℝ) :
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          (n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I))) *
        routeTNormalizedSmoothWindowMellin N H
          ((2 : ℂ) + (t : ℂ) * I) =
        (((2 : ℂ) + (t : ℂ) * I) - 1)⁻¹ *
            routeTNormalizedSmoothWindowMellin N H
              ((2 : ℂ) + (t : ℂ) * I) +
          zetaLogDerivReg ((2 : ℂ) + (t : ℂ) * I) *
            routeTNormalizedSmoothWindowMellin N H
              ((2 : ℂ) + (t : ℂ) * I) := by
    have hsum := tsum_vonMangoldt_cpow_eq
      (s := (2 : ℂ) + (t : ℂ) * I) (by norm_num)
    have hsplit := neg_logDeriv_riemannZeta_eq_of_ne_zero
      (s := (2 : ℂ) + (t : ℂ) * I)
      (by
        intro hs
        have hre := congrArg Complex.re hs
        norm_num at hre)
      (riemannZeta_ne_zero_of_one_le_re (by norm_num))
    rw [logDeriv_apply] at hsplit
    rw [hsum]
    rw [show -deriv riemannZeta ((2 : ℂ) + (t : ℂ) * I) /
          riemannZeta ((2 : ℂ) + (t : ℂ) * I) =
        -(deriv riemannZeta ((2 : ℂ) + (t : ℂ) * I) /
          riemannZeta ((2 : ℂ) + (t : ℂ) * I)) by ring,
      hsplit]
    ring
  have hcongr :
      (∫ t in (-T)..T,
        (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I))) *
          routeTNormalizedSmoothWindowMellin N H
            ((2 : ℂ) + (t : ℂ) * I)) =
        ∫ t in (-T)..T,
          ((((2 : ℂ) + (t : ℂ) * I) - 1)⁻¹ *
              routeTNormalizedSmoothWindowMellin N H
                ((2 : ℂ) + (t : ℂ) * I) +
            zetaLogDerivReg ((2 : ℂ) + (t : ℂ) * I) *
              routeTNormalizedSmoothWindowMellin N H
                ((2 : ℂ) + (t : ℂ) * I)) :=
    intervalIntegral.integral_congr (fun t _ => hpoint t)
  rw [inghamRouteTBufferedSelectedTwoVonMangoldtEdge,
    inghamRouteTBufferedSelectedTwoPoleEdge,
    inghamRouteTBufferedSelectedTwoRightEdge]
  change (∫ t in (-T)..T, _) = (∫ t in (-T)..T, _) + (∫ t in (-T)..T, _)
  rw [hcongr, intervalIntegral.integral_add hpole hreg]

/-- Exact Route T explicit formula on one selected contour: literal von Mangoldt current minus
polar continuum plus the complete zero packet equals the three synchronized error edges. -/
theorem routeTBufferedNegativeHalf_arithmetic_contour_collapse
    {X : ℕ} (hX : 12 ≤ X) :
    I • (inghamRouteTBufferedSelectedTwoVonMangoldtEdge X -
          inghamRouteTBufferedSelectedTwoPoleEdge X) +
        inghamRouteTBufferedSelectedNegativeHalfZeroPacket X =
      I • inghamRouteTBufferedSelectedNegativeHalfLeftEdge X +
        inghamRouteTBufferedNegativeHalfTopEdge X -
        inghamRouteTBufferedNegativeHalfBottomEdge X := by
  have hsplit :=
    inghamRouteTBufferedSelectedTwoVonMangoldtEdge_eq_pole_add_regular
      (show 1 ≤ X by omega)
  have hcollapse := routeTBufferedNegativeHalf_contour_collapse hX
  rw [show inghamRouteTBufferedSelectedTwoVonMangoldtEdge X -
      inghamRouteTBufferedSelectedTwoPoleEdge X =
      inghamRouteTBufferedSelectedTwoRightEdge X by linear_combination hsplit]
  exact hcollapse

/-- The coefficient-faithful prime-minus-continuum current and complete zero packet cancel
asymptotically; every discarded contour edge is already proved to vanish. -/
theorem tendsto_routeTBufferedNegativeHalf_arithmetic_explicitFormula_zero :
    Tendsto (fun X : ℕ =>
      I • (inghamRouteTBufferedSelectedTwoVonMangoldtEdge X -
            inghamRouteTBufferedSelectedTwoPoleEdge X) +
        inghamRouteTBufferedSelectedNegativeHalfZeroPacket X)
      atTop (nhds 0) := by
  apply tendsto_routeTBufferedNegativeHalf_rightEdge_add_zeroPacket_zero.congr'
  filter_upwards [eventually_ge_atTop (12 : ℕ)] with X hX
  have hsplit :=
    inghamRouteTBufferedSelectedTwoVonMangoldtEdge_eq_pole_add_regular
      (show 1 ≤ X by omega)
  rw [show inghamRouteTBufferedSelectedTwoVonMangoldtEdge X -
      inghamRouteTBufferedSelectedTwoPoleEdge X =
      inghamRouteTBufferedSelectedTwoRightEdge X by linear_combination hsplit]

end

end RHTower.Sieve
