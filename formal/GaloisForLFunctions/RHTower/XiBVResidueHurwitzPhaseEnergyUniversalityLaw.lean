import GaloisForLFunctions.RHTower.XiCCMBVWindowDilationOrientationUniversalityLaw
import GaloisForLFunctions.RHTower.XiHurwitzPhaseEnergyGrowth

/-!
# BV-residue reconstruction of the Xi Hurwitz phase and energy

Forward and inverse dilation of one compact bounded-variation prime window act on its continued
source residue by opposite Mellin characters.  Their norm ratio therefore recovers the horizontal
Xi displacement exactly.  That displacement is the principal Hurwitz phase already governing the
orientation-energy atom and the eventual negative continued-Cauchy source floor.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

open CompactBVPrimeWindow

/-- Source-side logarithmic phase coordinate read from forward/inverse BV-window residue norms. -/
def xiBVResiduePhaseCoordinate
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 1 < r)
    (q : XiRightZeroCopy) : ℝ :=
  Real.log
      (‖(W.argumentDilation r (lt_trans zero_lt_one hr)).continuedSourceResidueValue
          (q.1.1 : ℂ)‖ /
        ‖(W.argumentExpansion r (lt_trans zero_lt_one hr)).continuedSourceResidueValue
          (q.1.1 : ℂ)‖) /
    (2 * Real.log r)

/-- Full source-to-phase-to-energy certificate induced by a noncensored BV prime window. -/
structure XiBVResidueHurwitzPhaseEnergyUniversalCertificate
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 1 < r)
    (q : XiRightZeroCopy) : Prop where
  phaseReconstruction :
    xiBVResiduePhaseCoordinate W r hr q =
      xiHurwitzRightPrincipalPhase q
  defectReconstruction :
    xiHurwitzOrientationDefect q.1.1 =
      Real.sin (2 * Real.pi * xiBVResiduePhaseCoordinate W r hr q) ^ 2
  recoveredPhase_pos :
    0 < xiBVResiduePhaseCoordinate W r hr q
  recoveredPhase_lt_half :
    xiBVResiduePhaseCoordinate W r hr q < 1 / 2
  energyAtom_pos :
    0 < xiHurwitzOrientationWeight q.1.1 *
      Real.sin (2 * Real.pi * xiBVResiduePhaseCoordinate W r hr q) ^ 2
  energyAtom_le :
    xiHurwitzOrientationWeight q.1.1 *
        Real.sin (2 * Real.pi * xiBVResiduePhaseCoordinate W r hr q) ^ 2 ≤
      xiHurwitzOrientationEnergy
  eventualNegativeSourceFloor :
    ∃ V : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2,
      (∀ n, V n ∈ xiWeilContinuedCauchyAlgebraicSubspace) ∧
      Tendsto V atTop (nhds xiHurwitzOrientationVector) ∧
      Tendsto (fun n => xiWeilHilbertQuadratic (V n)) atTop
        (nhds (-xiHurwitzOrientationEnergy)) ∧
      ∀ᶠ n in atTop,
        xiWeilHilbertQuadratic (V n) <
          -(xiHurwitzOrientationWeight q.1.1 *
            Real.sin (2 * Real.pi * xiBVResiduePhaseCoordinate W r hr q) ^ 2) / 2

/-- **BV-residue/Hurwitz phase-energy universality.**  Every noncensored BV-window residue pair
recovers the right-zero Hurwitz phase exactly.  The recovered source coordinate is strictly inside
`(0,1/2)`, gives the exact orientation defect and its positive energy atom, and controls the same
eventual negative continued-Cauchy floor. -/
theorem xiBVResidue_hurwitzPhaseEnergyUniversality
    (W : CompactBVPrimeWindow) {r : ℝ} (hr : 1 < r)
    (q : XiRightZeroCopy)
    (hres : W.continuedSourceResidueValue (q.1.1 : ℂ) ≠ 0) :
    XiBVResidueHurwitzPhaseEnergyUniversalCertificate W r hr q := by
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hbaseNorm :
      ‖W.continuedSourceResidueValue (q.1.1 : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hres
  have hphase :
      xiHurwitzRightPrincipalPhase q = ((q.1.1 : ℂ).re - 1 / 2) := by
    rw [xiHurwitzRightPrincipalPhase_eq_transverse,
      xiRightCenteredZero_eq_support_sub_half, Complex.sub_re]
    norm_num
  have hratio :
      ‖(W.argumentDilation r hrpos).continuedSourceResidueValue (q.1.1 : ℂ)‖ /
          ‖(W.argumentExpansion r hrpos).continuedSourceResidueValue (q.1.1 : ℂ)‖ =
        r ^ (2 * xiHurwitzRightPrincipalPhase q) := by
    rw [continuedSourceResidueValue_argumentDilation,
      continuedSourceResidueValue_argumentExpansion,
      norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hrpos,
      Complex.norm_cpow_eq_rpow_re_of_pos hrpos,
      hphase]
    have hcancel :
        (r ^ (((q.1.1 : ℂ) - 1 / 2).re) *
              ‖W.continuedSourceResidueValue (q.1.1 : ℂ)‖) /
            (r ^ ((1 / 2 - (q.1.1 : ℂ)).re) *
              ‖W.continuedSourceResidueValue (q.1.1 : ℂ)‖) =
          r ^ (((q.1.1 : ℂ) - 1 / 2).re) /
            r ^ ((1 / 2 - (q.1.1 : ℂ)).re) := by
      field_simp
    rw [hcancel, ← Real.rpow_sub hrpos]
    congr 1
    norm_num [Complex.sub_re]
    ring
  have hreconstruct :
      xiBVResiduePhaseCoordinate W r hr q =
        xiHurwitzRightPrincipalPhase q := by
    rw [xiBVResiduePhaseCoordinate, hratio, Real.log_rpow hrpos]
    have hlog : Real.log r ≠ 0 := (Real.log_pos hr).ne'
    field_simp
  refine {
    phaseReconstruction := hreconstruct
    defectReconstruction := ?_
    recoveredPhase_pos := ?_
    recoveredPhase_lt_half := ?_
    energyAtom_pos := ?_
    energyAtom_le := ?_
    eventualNegativeSourceFloor := ?_ }
  · rw [hreconstruct]
    exact xiHurwitzOrientationDefect_eq_sin_sq_rightPrincipalPhase q
  · rw [hreconstruct]
    exact xiHurwitzRightPrincipalPhase_pos q
  · rw [hreconstruct]
    exact xiHurwitzRightPrincipalPhase_lt_half q
  · rw [hreconstruct]
    exact xiHurwitzRightPrincipalPhase_energyWitness_pos q
  · rw [hreconstruct]
    exact xiHurwitzRightPrincipalPhase_witness_le_orientationEnergy q
  · simpa only [hreconstruct] using
      exists_continuedCauchyCore_eventually_lt_neg_half_phaseWitness q

end

end RHTower
