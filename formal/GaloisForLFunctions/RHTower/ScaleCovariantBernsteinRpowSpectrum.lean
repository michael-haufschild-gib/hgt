import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinInverseScaleSelection
import GaloisForLFunctions.RHTower.AtomicBernsteinPacketRpowGrowth

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

/-- **Scale-covariant real-p spectrum.**  At every radius larger than twice the source bound,
every transverse source has one source-attained confocal amplitude `B > 1`, and the nth root of
each real-p energy of the associated Bernstein packet converges to `B^p`. -/
theorem exists_tendsto_inverseScaleAtomicBernsteinRpowEnergy
    {I : Type*} (c z : I → ℂ) (hc : Summable c)
    (hz0 : Tendsto z cofinite (nhds 0))
    (hzinj : Function.Injective z)
    (hcne : ∀ i, c i ≠ 0)
    {M R p : ℝ} (hM : 0 ≤ M) (hbound : ∀ i, ‖z i‖ ≤ M)
    (hR : 2 * M < R) (hp : 1 ≤ p)
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
  have hRpos : 0 < R := by linarith
  have hRM : M < R := by linarith
  obtain ⟨D, B, beta, L, hBconf, hB, hbeta1, hbeta, hDne, hD, hDsub,
      hL, hLpos, hhalf⟩ :=
    exists_positive_halfOrder_inverseScaleAtomicPacket
      c z hc hz0 hzinj hcne hM hbound hRM hreal hi0
  let u : I → ℂ := inverseScaleAtomicNode z R
  have huinj : Function.Injective u :=
    inverseScaleAtomicNode_injective hzinj hRpos
  have huhalf : ∀ i, ‖u i‖ < 1 / 2 :=
    norm_inverseScaleAtomicNode_lt_half hbound hR
  have hureal : ∀ i, (u i).im = 0 → 0 ≤ (u i).re :=
    inverseScaleAtomicNode_re_nonneg_of_im_eq_zero hRpos hreal
  have huim : ∀ j ∈ D, (u j).im ≠ 0 := by
    intro j hj
    exact im_ne_zero_of_one_lt_atomicBernsteinAmplitude
      ((huhalf j).trans (by norm_num : (1 / 2 : ℝ) < 1))
      (hureal j) (hB.trans_eq (hD j hj).symm)
  obtain ⟨iD, hiD⟩ := hDne
  have hiDim : (u iD).im ≠ 0 := huim iD hiD
  let w : ℂ := bernsteinEllipsePhase (u iD)
  let b : ℂ := 1 - u iD + u iD * w
  have hw : ‖w‖ = 1 := bernsteinEllipsePhase_norm_eq_one hiDim
  have hb : ‖b‖ = B := by
    dsimp only [b, w]
    rw [norm_affine_bernsteinEllipsePhase_eq_amplitude hiDim]
    simpa only [atomicBernsteinAmplitude, u, add_comm] using hD iD hiD
  have hamp : ∀ j, ‖u j‖ + ‖1 - u j‖ ≤ B := by
    intro j
    by_cases hj : j ∈ D
    · simpa only [u, atomicBernsteinAmplitude] using (hD j hj).le
    · exact (hDsub j hj).trans hbeta.le
  have hsub : ∀ j ∉ ({iD} : Finset I), ‖1 - u j + u j * w‖ < B := by
    intro j hj
    have hji : j ≠ iD := by simpa using hj
    by_cases hjD : j ∈ D
    · have hjim : (u j).im ≠ 0 := huim j hjD
      have hle : ‖1 - u j + u j * w‖ ≤ B := by
        calc
          ‖1 - u j + u j * w‖ ≤ ‖1 - u j‖ + ‖u j * w‖ := norm_add_le _ _
          _ = ‖1 - u j‖ + ‖u j‖ := by rw [norm_mul, hw, mul_one]
          _ = B := by
            simpa only [u, atomicBernsteinAmplitude, add_comm] using hD j hjD
      exact lt_of_le_of_ne hle fun heq => by
        have hattain : ‖1 - u j + u j * w‖ = ‖1 - u j‖ + ‖u j‖ := by
          rw [heq]
          simpa only [u, atomicBernsteinAmplitude, add_comm] using (hD j hjD).symm
        have hphase :=
          bernsteinEllipsePhase_eq_of_norm_affine_eq_amplitude hjim hw hattain
        have hphaseNe := bernsteinEllipsePhase_ne_of_small_distinct_equalAmplitude
          hjim hiDim (huhalf j) (huhalf iD)
          (fun h => hji (huinj h))
          (by
            simpa only [u, atomicBernsteinAmplitude] using
              (hD iD hiD).trans (hD j hjD).symm)
        exact hphaseNe (by simpa only [w] using hphase.symm)
    · calc
        ‖1 - u j + u j * w‖ ≤ ‖1 - u j‖ + ‖u j * w‖ := norm_add_le _ _
        _ = ‖1 - u j‖ + ‖u j‖ := by rw [norm_mul, hw, mul_one]
        _ = atomicBernsteinAmplitude u j := by rw [atomicBernsteinAmplitude, add_comm]
        _ ≤ beta := hDsub j hjD
        _ < B := hbeta
  have hdom : ∀ j ∈ ({iD} : Finset I), 1 - u j + u j * w = b := by
    intro j hj
    simpa only [Finset.mem_singleton.mp hj, b]
  have hC : ∑ j ∈ ({iD} : Finset I), c j ≠ 0 := by
    simpa using hcne iD
  refine ⟨B, hBconf, hB, ?_⟩
  exact tendsto_atomicBernsteinPacketRpowEnergy_rpow_inv_natCast
    c u hc hp (lt_trans zero_lt_one hB) hamp {iD} hw.le hdom hsub hb hC

end

end RHTower
