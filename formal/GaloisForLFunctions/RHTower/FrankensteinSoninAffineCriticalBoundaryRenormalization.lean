import GaloisForLFunctions.RHTower.SoninCofinalContractiveMobiusGammaXiIncidence
import GaloisForLFunctions.RHTower.MobiusGammaXiPreScalarAffineBoundaryRenormalization

/-!
# Contractive Sonin--affine critical boundary renormalization

This module composes two unconditional source constructions which had
previously stopped on opposite sides of the critical boundary:

* the norm-one inward Sonin corner transports the moving squarefree Fisher
  two-jet cofinally as its Euler parameter approaches `1`;
* the affine prime--polar--Gamma packet gives the exact coefficient-faithful
  correction from the completed relative trace to the continued Ward response.

One common cofinal depth schedule now carries both constructions.  Before
correction, the Sonin transport converges to the normalized affine readout.
After correction, it converges to the actual critical Ward coefficient.  No
positivity or four-unit order is asserted; that is the remaining RH-bearing
gate.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- The coefficient-faithful affine Gamma/polar correction applied before taking the
critical limit to the actual contractive inward Sonin carrier. -/
def soninContractivePreScalarAffineBoundaryRenormalization
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (depth : ℕ → ℕ) (j : ℕ) : ℂ :=
  -2 * I *
      soninContractiveCofinalMobiusGammaXiWardMovingTransport
        a c d r hc hcd hr
        soninMobiusCriticalSigmaSequence
        soninMobiusCriticalSigmaSequence_gt_one
        (fun _ => 0) (fun _ => by norm_num)
        depth j +
    mobiusGammaXiPreScalarAffineBoundaryCorrection j

/-- A single contractive Sonin schedule crosses the singular Euler target while the
literal affine prime--polar--Gamma correction preserves the completed Ward coefficient.
This closes the cofinal, landing, and coefficient-fidelity gates simultaneously; it
does not assert the missing four-unit order law. -/
theorem exists_soninContractivePreScalarAffineCriticalBoundaryRenormalization
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      Tendsto (fun j =>
        soninContractiveCofinalMobiusGammaXiWardMovingTransport
            a c d r hc hcd hr
            soninMobiusCriticalSigmaSequence
            soninMobiusCriticalSigmaSequence_gt_one
            (fun _ => 0) (fun _ => by norm_num)
            depth j -
          mobiusGammaXiPreScalarAffineNormalizedZeroModeReadout j (depth j))
        atTop (nhds 0) ∧
      Tendsto (fun j =>
        soninContractivePreScalarAffineBoundaryRenormalization
            a c d r hc hcd hr depth j -
          mobiusGammaXiPreScalarAffineBoundaryRenormalization j (depth j))
        atTop (nhds 0) ∧
      Tendsto (fun j =>
        soninContractivePreScalarAffineBoundaryRenormalization
          a c d r hc hcd hr depth j)
        atTop (nhds mobiusGammaXiCoupledErrorCriticalCoefficient) ∧
      (Tendsto (fun j =>
          soninContractivePreScalarAffineBoundaryRenormalization
            a c d r hc hcd hr depth j)
          atTop (nhds 0) ↔ RiemannHypothesis) := by
  let sigma : ℕ → ℝ := soninMobiusCriticalSigmaSequence
  let u : ℕ → ℝ := fun _ => 0
  have hsigma (j : ℕ) : 1 < sigma j :=
    soninMobiusCriticalSigmaSequence_gt_one j
  have hu (j : ℕ) : 0 ≤ u j := by simp [u]
  have hsigmaOne : Tendsto sigma atTop (nhds (1 : ℝ)) :=
    tendsto_soninMobiusCriticalSigmaSequence.mono_right inf_le_left
  have hnormal : Tendsto (fun j => sigma j - 1) atTop (nhds 0) := by
    simpa using hsigmaOne.sub_const 1
  have hgraphScaleZero : Tendsto (fun j =>
      (sigma j - 1) *
        (squarefreeMobiusTotal
            (mobiusCriticalBoundaryParameter (sigma j) (u j)) /
          squarefreeMobiusTotal (sigma j)))
      atTop (nhds 0) := by
    have heq : (fun j =>
        (sigma j - 1) *
          (squarefreeMobiusTotal
              (mobiusCriticalBoundaryParameter (sigma j) (u j)) /
            squarefreeMobiusTotal (sigma j))) =
        fun j => sigma j - 1 := by
      funext j
      have htotal : squarefreeMobiusTotal (sigma j) ≠ 0 :=
        ne_of_gt (squarefreeMobiusTotal_pos (hsigma j))
      simp [u, mobiusCriticalBoundaryParameter, htotal]
    rw [heq]
    exact hnormal
  obtain ⟨depth, hdepth, hsonin⟩ :=
    exists_soninContractiveCofinalMobiusGammaXiWardMovingTransport
      a c d r ha hc hcd hda hr harc sigma hsigma u hu hgraphScaleZero
  have hreadout (j : ℕ) :
      mobiusGammaXiPreScalarAffineNormalizedZeroModeReadout j (depth j) =
        continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate
            (mobiusCriticalBoundaryParameter (sigma j) (u j) : ℂ)) := by
    rw [mobiusGammaXiPreScalarAffineNormalizedZeroModeReadout_eq_transport,
      eulerPositiveGammaXiWardHilbertTransportAt_eq_continuedSource]
    simp [sigma, u, mobiusCriticalBoundaryParameter,
      eulerPositiveCriticalBoundaryParameter]
  have hraw : Tendsto (fun j =>
      soninContractiveCofinalMobiusGammaXiWardMovingTransport
          a c d r hc hcd hr sigma hsigma u hu depth j -
        mobiusGammaXiPreScalarAffineNormalizedZeroModeReadout j (depth j))
      atTop (nhds 0) := by
    convert hsonin using 1
    funext j
    rw [hreadout]
  have hcorrected : Tendsto (fun j =>
      soninContractivePreScalarAffineBoundaryRenormalization
          a c d r hc hcd hr depth j -
        mobiusGammaXiPreScalarAffineBoundaryRenormalization j (depth j))
      atTop (nhds 0) := by
    have hscaled : Tendsto (fun j =>
        (-2 * I) *
          (soninContractiveCofinalMobiusGammaXiWardMovingTransport
              a c d r hc hcd hr sigma hsigma u hu depth j -
            mobiusGammaXiPreScalarAffineNormalizedZeroModeReadout
              j (depth j)))
        atTop (nhds 0) := by
      simpa using hraw.const_mul (-2 * I)
    convert hscaled using 1
    funext j
    simp only [soninContractivePreScalarAffineBoundaryRenormalization,
      mobiusGammaXiPreScalarAffineBoundaryRenormalization, sigma, u]
    ring
  have haffine : Tendsto (fun j =>
      mobiusGammaXiPreScalarAffineBoundaryRenormalization j (depth j))
      atTop (nhds mobiusGammaXiCoupledErrorCriticalCoefficient) := by
    have hward := tendsto_continuedXiAntiCausalWardResponse_criticalNode
      (u := 0) (by norm_num)
    convert hward using 1
    · funext j
      exact mobiusGammaXiPreScalarAffineBoundaryRenormalization_eq_ward
        j (depth j)
    · rfl
  have hcritical : Tendsto (fun j =>
      soninContractivePreScalarAffineBoundaryRenormalization
        a c d r hc hcd hr depth j)
      atTop (nhds mobiusGammaXiCoupledErrorCriticalCoefficient) := by
    have hadd : Tendsto (fun j =>
        (soninContractivePreScalarAffineBoundaryRenormalization
            a c d r hc hcd hr depth j -
          mobiusGammaXiPreScalarAffineBoundaryRenormalization j (depth j)) +
        mobiusGammaXiPreScalarAffineBoundaryRenormalization j (depth j))
        atTop (nhds mobiusGammaXiCoupledErrorCriticalCoefficient) := by
      simpa using hcorrected.add haffine
    convert hadd using 1
    funext j
    ring
  refine ⟨depth, hdepth, ?_, hcorrected, hcritical, ?_⟩
  · simpa only [sigma, u] using hraw
  constructor
  · intro hzero
    have hcoeff : mobiusGammaXiCoupledErrorCriticalCoefficient = 0 :=
      tendsto_nhds_unique hcritical hzero
    exact continuedXiAntiCausalWardResponse_half_eq_zero_iff_rh.mp hcoeff
  · intro hRH
    have hcoeff : mobiusGammaXiCoupledErrorCriticalCoefficient = 0 :=
      continuedXiAntiCausalWardResponse_half_eq_zero_iff_rh.mpr hRH
    simpa [hcoeff] using hcritical

end RHTower
