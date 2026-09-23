import GaloisForLFunctions.RHTower.FrankensteinKreinCCMRoutePSignedConormalResidueBridge
import GaloisForLFunctions.RHTower.XiReflectionSelfIntersectionCharge
import GaloisForLFunctions.RHTower.XiWardCubicCompletedPairResidueIncidence

/-!
# Cubic Ward/Krein opposite-radial pair incidence

Pairing the two functional-equation orientations after both have been placed on the positive
radial half-line erases every exponential and leaves the nonintegrable density `r^(2 : ℕ)`.  The signed
completed source has more structure before that polarization: its two conormal legs can be formed
at opposite radial orientations `(-r, r)` while both spectral variables remain on the same
literal CCM/Krein meromorphic family.

This module proves that the order matters.  Take the first residue at the reflected Xi pole on the
negative radial leg and the second residue at the forward Xi pole on the positive radial leg.
Functional-equation reflection converts the first landing into minus the Hermitian mate, while
the two signed residues contribute `I^(2 : ℕ) = -1`; the signs cancel exactly.  The result is the
positive, exponentially decaying cubic conormal pair, with both analytic multiplicities intact.

Consequently every entry of W-H186's positive raw pair-residue matrix is literally the aperture
integral of iterated residues of one coefficient-faithful signed CCM/Krein source current.  This
removes the post-residue `r^(2 : ℕ)` obstruction and explains the correct pre-radial architecture.
It does not prove the remaining global trace contraction: polar--Gamma shorting of this
opposite-radial quadratic current against the summable primitive Euler carrier is still open.
-/

open Complex Matrix Set Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Functional-equation line reflection preserves the exact analytic multiplicity recorded by
the CCM signed source. -/
theorem inverseTiltedXiMultiplicity_lineConj (rho : XiDivisorSupport) :
    inverseTiltedXiMultiplicity (xiZeroLineConjEquiv rho) =
      inverseTiltedXiMultiplicity rho := by
  unfold inverseTiltedXiMultiplicity
  rw [xi_orderAt_xiZeroLineConjEquiv]

/-- The reflected Xi support placed on the negative radial leg is minus the Hermitian modular
mate of the forward support. -/
theorem routePXiBaseConormalResidueFeature_lineConj_neg_eq_neg_reflectedMate
    (rho : XiDivisorSupport) (r : ℝ) :
    routePXiBaseConormalResidueFeature
        ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) (-r) =
      -xiWardCubicReflectedConormalMateFeature (rho : ℂ) r := by
  rw [xiWardCubicReflectedConormalMateFeature,
    xiZeroLineConjEquiv_apply]
  simp

/-- Literal quadratic signed source with opposite radial orientations, formed before either
spectral variable is restricted to the Xi divisor. -/
def xiWardCubicKreinOppositeRadialPairCurrent (u v : ℂ) (r : ℝ) : ℂ :=
  frankensteinKreinCCMRoutePSignedConormalColumn u (-r) *
    frankensteinKreinCCMRoutePSignedConormalColumn v r

/-- Exact source current remaining after the positive-radial leg residue is taken. -/
def xiWardCubicKreinOppositeRadialPairRightResidue
    (u : ℂ) (tau : XiDivisorSupport) (r : ℝ) : ℂ :=
  frankensteinKreinCCMRoutePSignedConormalColumn u (-r) *
    (I * (inverseTiltedXiMultiplicity tau : ℂ) *
      routePXiBaseConormalResidueFeature (tau : ℂ) r)

/-- The first residue retains the complete negative-radial source leg. -/
theorem xiWardCubicKreinOppositeRadialPairCurrent_right_residue
    (u : ℂ) (tau : XiDivisorSupport) (r : ℝ) :
    Tendsto
      (fun v : ℂ => (v - criticalMellinXiPole tau) *
        xiWardCubicKreinOppositeRadialPairCurrent u v r)
      (nhdsWithin (criticalMellinXiPole tau)
        ({criticalMellinXiPole tau}ᶜ))
      (nhds (xiWardCubicKreinOppositeRadialPairRightResidue u tau r)) := by
  have h :=
    (frankensteinKreinCCMRoutePSignedConormalColumn_residue tau r).const_mul
      (frankensteinKreinCCMRoutePSignedConormalColumn u (-r))
  simpa [xiWardCubicKreinOppositeRadialPairCurrent,
    xiWardCubicKreinOppositeRadialPairRightResidue, mul_assoc,
    mul_left_comm] using h

/-- **W-H187 opposite-radial incidence.**  Successive residues at the reflected negative-radial
pole and the forward positive-radial pole equal the positive multiplicity-weighted modular pair. -/
theorem xiWardCubicKreinOppositeRadialPairCurrent_iterated_residue
    (rho tau : XiDivisorSupport) (r : ℝ) :
    Tendsto
      (fun u : ℂ =>
        (u - criticalMellinXiPole (xiZeroLineConjEquiv rho)) *
          xiWardCubicKreinOppositeRadialPairRightResidue u tau r)
      (nhdsWithin (criticalMellinXiPole (xiZeroLineConjEquiv rho))
        ({criticalMellinXiPole (xiZeroLineConjEquiv rho)}ᶜ))
      (nhds (((inverseTiltedXiMultiplicity rho : ℂ) *
          (inverseTiltedXiMultiplicity tau : ℂ)) *
        (xiWardCubicReflectedConormalMateFeature (rho : ℂ) r *
          routePXiBaseConormalResidueFeature (tau : ℂ) r))) := by
  have h :=
    (frankensteinKreinCCMRoutePSignedConormalColumn_residue
      (xiZeroLineConjEquiv rho) (-r)).mul_const
        (I * (inverseTiltedXiMultiplicity tau : ℂ) *
          routePXiBaseConormalResidueFeature (tau : ℂ) r)
  rw [inverseTiltedXiMultiplicity_lineConj,
    routePXiBaseConormalResidueFeature_lineConj_neg_eq_neg_reflectedMate] at h
  convert h using 1
  · funext u
    simp [xiWardCubicKreinOppositeRadialPairRightResidue, mul_assoc,
      mul_left_comm]
  · congr 1
    ring_nf
    rw [show (I : ℂ) ^ (2 : ℕ) = -1 by norm_num]
    ring

/-- Coefficient-faithful residue landing of the opposite-radial signed source pair. -/
def xiWardCubicKreinOppositeRadialPairResidueLanding
    (rho tau : XiDivisorSupport) (r : ℝ) : ℂ :=
  ((inverseTiltedXiMultiplicity rho : ℂ) *
      (inverseTiltedXiMultiplicity tau : ℂ)) *
    (xiWardCubicReflectedConormalMateFeature (rho : ℂ) r *
      routePXiBaseConormalResidueFeature (tau : ℂ) r)

/-- Named landing form of W-H187. -/
theorem xiWardCubicKreinOppositeRadialPairCurrent_iterated_residue_landing
    (rho tau : XiDivisorSupport) (r : ℝ) :
    Tendsto
      (fun u : ℂ =>
        (u - criticalMellinXiPole (xiZeroLineConjEquiv rho)) *
          xiWardCubicKreinOppositeRadialPairRightResidue u tau r)
      (nhdsWithin (criticalMellinXiPole (xiZeroLineConjEquiv rho))
        ({criticalMellinXiPole (xiZeroLineConjEquiv rho)}ᶜ))
      (nhds (xiWardCubicKreinOppositeRadialPairResidueLanding rho tau r)) := by
  exact xiWardCubicKreinOppositeRadialPairCurrent_iterated_residue rho tau r

/-- CCM inverse-tilted multiplicity and the Xi support multiplicity are the same analytic order. -/
theorem inverseTiltedXiMultiplicity_eq_xiSupportMultiplicity
    (rho : XiDivisorSupport) :
    inverseTiltedXiMultiplicity rho = xiSupportMultiplicity rho := by
  rw [inverseTiltedXiMultiplicity,
    xiSupportMultiplicity_eq_analyticOrderAt_toNat]

/-- Aperture integration of the literal signed-source residue landing is the complete raw cubic
pair kernel. -/
theorem integral_xiWardCubicKreinOppositeRadialPairResidueLanding
    {rho tau : XiDivisorSupport}
    (hrho : 1 / 2 < ((rho : ℂ)).re)
    (htau : 1 / 2 < ((tau : ℂ)).re) :
    (∫ r : ℝ in Ioi 0,
      xiWardCubicKreinOppositeRadialPairResidueLanding rho tau r) =
      ((inverseTiltedXiMultiplicity rho : ℂ) *
          (inverseTiltedXiMultiplicity tau : ℂ)) *
        routePBaseCauchyCubicKernel 1
          ((rho : ℂ) - 1 / 2).re ((tau : ℂ) - 1 / 2).re
          (((tau : ℂ) - 1 / 2).im - ((rho : ℂ) - 1 / 2).im) := by
  unfold xiWardCubicKreinOppositeRadialPairResidueLanding
  rw [MeasureTheory.integral_const_mul,
    integral_xiWardCubicReflectedConormalMateFeature_mul_baseFeature hrho htau]

/-- Exact source handoff: each entry of W-H186's PSD raw residue matrix is the radial integral of
iterated residues of the literal opposite-radial CCM/Krein source current. -/
theorem xiWardCubicRawCompletedPairResidueMatrix_apply_eq_kreinSourceIntegral
    {N : ℕ} (q : Fin N → XiRightZeroCopy) (i j : Fin N) :
    xiWardCubicRawCompletedPairResidueMatrix q i j =
      ∫ r : ℝ in Ioi 0,
        xiWardCubicKreinOppositeRadialPairResidueLanding
          (q i).1.1 (q j).1.1 r := by
  rw [integral_xiWardCubicKreinOppositeRadialPairResidueLanding]
  · rw [xiWardCubicRawCompletedPairResidueMatrix_apply,
      inverseTiltedXiMultiplicity_eq_xiSupportMultiplicity,
      inverseTiltedXiMultiplicity_eq_xiSupportMultiplicity,
      xiRightCenteredZero_eq_support_sub_half,
      xiRightCenteredZero_eq_support_sub_half]
    push_cast
    ring
  · have hpos := xiRightCenteredZero_re_pos (q i)
    rw [xiRightCenteredZero_eq_support_sub_half] at hpos
    norm_num at hpos ⊢
    linarith
  · have hpos := xiRightCenteredZero_re_pos (q j)
    rw [xiRightCenteredZero_eq_support_sub_half] at hpos
    norm_num at hpos ⊢
    linarith

end

end RHTower
