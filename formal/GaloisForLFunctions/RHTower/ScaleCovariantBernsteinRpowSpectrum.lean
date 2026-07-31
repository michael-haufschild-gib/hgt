import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinInverseScaleSelection
import GaloisForLFunctions.RHTower.FinitePacketPositiveRpowHalfOrderTransfer

/-!
# Real-p spectrum of the scale-covariant Bernstein packet

Every transverse source phase selected by the confocal envelope controls the exact nth-root growth
of all finite real-p energies of the same Bernstein coefficient packet.
-/

open Complex Filter Topology
open scoped BigOperators Real

namespace RHTower

noncomputable section

/-- The canonical ellipse phase attains the complete affine amplitude. -/
theorem norm_affine_bernsteinEllipsePhase_eq_amplitude
    {u : ℂ} (him : u.im ≠ 0) :
    ‖1 - u + u * bernsteinEllipsePhase u‖ = ‖u‖ + ‖1 - u‖ := by
  obtain ⟨w, hw, hattain, _⟩ :=
    exists_unit_bernsteinBase_norm_gt_one_of_im_ne_zero him
  have hphase := bernsteinEllipsePhase_eq_of_norm_affine_eq_amplitude him hw hattain
  rw [hphase] at hattain
  simpa only [add_comm] using hattain

/-- **Defect-neutral scale-covariant positive-power spectrum.**  At the sharp radial threshold
`M<R`, every transverse source whose transverse defect vanishes cofinally has a source-attained
confocal amplitude `B>1`.  The nth root of every positive real-power energy of the associated
Bernstein packet converges to `B^p`. -/
theorem exists_tendsto_inverseScaleAtomicBernsteinRpowEnergy_of_transverse_neutral
    {I : Type*} (c z : I → ℂ) (hc : Summable c)
    (htrans : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0))
    (hzinj : Function.Injective z)
    (hcne : ∀ i, c i ≠ 0)
    {M R p : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, ‖z i‖ ≤ M)
    (hR : M < R) (hp : 0 < p)
    (hreal : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    {i0 : I} (hi0 : (z i0).im ≠ 0) :
    ∃ B : ℝ,
      B = HTGeometry.confocalAmplitudeEnvelope (Set.range z) R ∧
      1 < B ∧
      Tendsto
        (fun n : ℕ =>
          finitePacketRpowEnergy
              (atomicBernsteinPacket c (inverseScaleAtomicNode z R)) p n ^
            ((n : ℝ)⁻¹))
        atTop (nhds (B ^ p)) := by
  classical
  have hRpos : 0 < R := hM.trans_lt hR
  obtain ⟨D, B, beta, L, hBconf, hB, hbeta1, hbeta, hDne, hD, hDsub,
      hL, hLpos, hhalf⟩ :=
    exists_positive_halfOrder_inverseScaleAtomicPacket_of_transverse_neutral
      c z hc htrans hzinj hcne hM hbound hR hreal hi0
  let u : I → ℂ := inverseScaleAtomicNode z R
  have hamp : ∀ j, ‖u j‖ + ‖1 - u j‖ ≤ B := by
    intro j
    by_cases hj : j ∈ D
    · simpa only [u, atomicBernsteinAmplitude] using (hD j hj).le
    · exact (hDsub j hj).trans hbeta.le
  let A : ℝ := atomicWeightL1 c
  have hA : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  have hupper : ∀ n : ℕ,
      finitePacketL1 (atomicBernsteinPacket c u) n ≤ A * B ^ n := by
    intro n
    exact finitePacketL1_atomicBernsteinPacket_le hc hamp n
  have hhalf' : Tendsto
      (fun n : ℕ => Real.sqrt n *
        finitePacketRpowEnergy (atomicBernsteinPacket c u) 2 n / (B ^ 2) ^ n)
      atTop (nhds L) := by
    simpa only [finitePacketRpowEnergy_two_eq_squareEnergy,
      atomicBernsteinPacketSquareEnergy, u] using hhalf
  refine ⟨B, hBconf, hB, ?_⟩
  exact tendsto_finitePacketRpowEnergy_of_positive_square_halfOrder
    (atomicBernsteinPacket c u) hp hA (lt_trans zero_lt_one hB) hLpos hupper hhalf'

/-- Cofinite convergence to the origin is a convenient sufficient condition for the intrinsic
transverse-neutrality hypothesis. -/
theorem exists_tendsto_inverseScaleAtomicBernsteinRpowEnergy
    {I : Type*} (c z : I → ℂ) (hc : Summable c)
    (hz0 : Tendsto z cofinite (nhds 0))
    (hzinj : Function.Injective z)
    (hcne : ∀ i, c i ≠ 0)
    {M R p : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, ‖z i‖ ≤ M)
    (hR : M < R) (hp : 0 < p)
    (hreal : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    {i0 : I} (hi0 : (z i0).im ≠ 0) :
    ∃ B : ℝ,
      B = HTGeometry.confocalAmplitudeEnvelope (Set.range z) R ∧
      1 < B ∧
      Tendsto
        (fun n : ℕ =>
          finitePacketRpowEnergy
              (atomicBernsteinPacket c (inverseScaleAtomicNode z R)) p n ^
            ((n : ℝ)⁻¹))
        atTop (nhds (B ^ p)) := by
  have htrans : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0) := by
    have hnorm := hz0.norm
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hz0
    have h2 : Tendsto (fun i => ‖z i‖ - (z i).re) cofinite (nhds 0) := by
      simpa only [Function.comp_apply, norm_zero, Complex.zero_re, sub_zero]
        using hnorm.sub hre
    simpa only [HTGeometry.transverseDefect] using h2
  exact exists_tendsto_inverseScaleAtomicBernsteinRpowEnergy_of_transverse_neutral
    c z hc htrans hzinj hcne hM hbound hR hp hreal hi0

end

end RHTower
