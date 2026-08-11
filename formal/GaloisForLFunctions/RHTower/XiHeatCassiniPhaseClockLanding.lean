import GaloisForLFunctions.RHTower.LambdaPositiveFunctionalEquationOffLine
import GaloisForLFunctions.RHTower.XiHeatCassiniBVWoldFisherLanding

/-!
# Laplace phase-clock landing of the Stieltjes--Cassini defect

For a squared Xi node `A+iB` and positive shift `y`, the midpoint defect is the Laplace-weighted
decoherence energy

`∫₀∞ exp (-(y+A)u) (1-cos(Bu)) du`.

The frequency is not an abstract divisor label: `B=-(2 Re rho-1) Im rho`, the product of the
valuation-one centered Wold rate and the physical zero-height clock.  This identifies exactly which
Schwarz-odd coordinate must be retained before quadratic source completion.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Positive Laplace phase-decoherence density of one squared Xi atom. -/
def xiHeatCassiniPhaseClockAtom (y u : ℝ) (q : XiZeroCopy) : ℝ :=
  Real.exp (-((y + (xiSquaredNode q).re) * u)) *
    (1 - Real.cos ((xiSquaredNode q).im * u))

/-- Complete phase-clock energy, retaining multiplicity by `XiZeroCopy`. -/
def xiHeatCassiniPhaseClockEnergy (y : ℝ) : ℝ :=
  ∑' q : XiZeroCopy,
    ∫ u in Ioi (0 : ℝ), xiHeatCassiniPhaseClockAtom y u q

/-- Squared-node phase is horizontal Wold rate times physical height. -/
theorem xiSquaredNode_im_eq_neg_centeredWoldRate_mul_height (q : XiZeroCopy) :
    (xiSquaredNode q).im =
      -(primeDepthBVWoldXiCenteredRate q.1 * (q.1 : ℂ).im) := by
  rw [xiSquaredNode_im]
  unfold primeDepthBVWoldXiCenteredRate
  ring

/-- Phase-clock density is pointwise nonnegative. -/
theorem xiHeatCassiniPhaseClockAtom_nonneg
    (y u : ℝ) (q : XiZeroCopy) :
    0 ≤ xiHeatCassiniPhaseClockAtom y u q := by
  unfold xiHeatCassiniPhaseClockAtom
  exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.cos_le_one _))

private theorem integrableOn_exp_neg_mul_cos
    {A B : ℝ} (hA : 0 < A) :
    IntegrableOn
      (fun u : ℝ => Real.exp (-(A * u)) * Real.cos (B * u))
      (Ioi 0) := by
  have hdom : IntegrableOn (fun u : ℝ => Real.exp (-A * u)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hA
  apply MeasureTheory.Integrable.mono' hdom
  · exact ((Real.continuous_exp.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards with u
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hcos : |Real.cos (B * u)| ≤ 1 := Real.abs_cos_le_one _
    simpa [abs_of_pos (Real.exp_pos _)] using
      mul_le_mul_of_nonneg_left hcos (Real.exp_pos (-(A * u))).le

/-- One phase-clock density is integrable on the positive ray. -/
theorem integrableOn_xiHeatCassiniPhaseClockAtom
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    IntegrableOn (xiHeatCassiniPhaseClockAtom y · q) (Ioi 0) := by
  let A : ℝ := y + (xiSquaredNode q).re
  let B : ℝ := (xiSquaredNode q).im
  have hA : 0 < A := add_pos hy (xiSquaredNode_re_pos q)
  have hExp : IntegrableOn (fun u : ℝ => Real.exp (-(A * u))) (Ioi 0) :=
    by simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hA
  have hCos := integrableOn_exp_neg_mul_cos (A := A) (B := B) hA
  have hsub : IntegrableOn (fun u : ℝ =>
      Real.exp (-(A * u)) - Real.exp (-(A * u)) * Real.cos (B * u)) (Ioi 0) :=
    hExp.sub hCos
  exact hsub.congr (by
    filter_upwards with u
    simp only [xiHeatCassiniPhaseClockAtom, A, B]
    ring)

/-- **Orbitwise Laplace decoherence law.** -/
theorem integral_xiHeatCassiniPhaseClockAtom_eq_orientationTerm
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    (∫ u in Ioi (0 : ℝ), xiHeatCassiniPhaseClockAtom y u q) =
      xiHeatCassiniOrientationTerm y q := by
  let A : ℝ := y + (xiSquaredNode q).re
  let B : ℝ := (xiSquaredNode q).im
  have hA : 0 < A := add_pos hy (xiSquaredNode_re_pos q)
  have hD : 0 < A ^ 2 + B ^ 2 := by
    nlinarith [sq_pos_of_pos hA, sq_nonneg B]
  have hExp : IntegrableOn (fun u : ℝ => Real.exp (-(A * u))) (Ioi 0) :=
    by simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hA
  have hCos := integrableOn_exp_neg_mul_cos (A := A) (B := B) hA
  rw [show xiHeatCassiniPhaseClockAtom y = fun u q =>
      Real.exp (-((y + (xiSquaredNode q).re) * u)) -
        Real.exp (-((y + (xiSquaredNode q).re) * u)) *
          Real.cos ((xiSquaredNode q).im * u) by
    funext u r
    rw [xiHeatCassiniPhaseClockAtom]
    ring]
  change (∫ u in Ioi (0 : ℝ),
      Real.exp (-(A * u)) - Real.exp (-(A * u)) * Real.cos (B * u)) = _
  rw [MeasureTheory.integral_sub hExp hCos,
    integral_Ioi_exp_neg_mul hA, integral_Ioi_exp_neg_mul_cos hA]
  change 1 / A - A / (A ^ 2 + B ^ 2) =
    B ^ 2 / (A * (A ^ 2 + B ^ 2))
  field_simp [hA.ne', hD.ne']
  ring

/-- Complete phase-clock energy is exactly the Stieltjes--Cassini orientation defect. -/
theorem xiHeatCassiniPhaseClockEnergy_eq_orientationDefect
    {y : ℝ} (hy : 0 < y) :
    xiHeatCassiniPhaseClockEnergy y = xiHeatCassiniOrientationDefect y := by
  rw [xiHeatCassiniPhaseClockEnergy, xiHeatCassiniOrientationDefect]
  exact tsum_congr fun q =>
    integral_xiHeatCassiniPhaseClockAtom_eq_orientationTerm hy q

/-- Phase-clock energy vanishes exactly under RH. -/
theorem riemannHypothesis_iff_xiHeatCassiniPhaseClockEnergy_eq_zero
    {y : ℝ} (hy : 0 < y) :
    RiemannHypothesis ↔ xiHeatCassiniPhaseClockEnergy y = 0 := by
  rw [xiHeatCassiniPhaseClockEnergy_eq_orientationDefect hy]
  exact riemannHypothesis_iff_xiHeatCassiniOrientationDefect_eq_zero hy

end

end RHTower
