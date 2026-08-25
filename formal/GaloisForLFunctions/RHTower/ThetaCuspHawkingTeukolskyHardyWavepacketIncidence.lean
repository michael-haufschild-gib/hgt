import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyBackreactionReturnDeterminant
import GaloisForLFunctions.RHTower.ThetaCuspHawkingCausalHardyIndexEndpoint
import GaloisForLFunctions.HTGeometry.HardyDiskKernelContinuity

/-!
# Causal wavepacket incidence for gravitational theta poles

The resonance Szegő kernel has nonzero overlap with its Birmingham--Mokhtari Green pole.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Every upper theta resonance is excited by a finite-energy causal Hardy wavepacket. -/
theorem exists_d4BMGravitationalHardyWavepacketSimplePole
    (r : ThetaCuspHawkingBackreactionResonantMode) (hr : 0 < r.1.im) :
    ∃ q : XiZeroCopy,
      xiSpectralPoint q = r.1 ∧
      GaloisForLFunctions.HTGeometry.hardyFun
          (thetaCuspHawkingCausalHardyKernel r hr)
          (thetaCuspHawkingCausalHardyNode r) ≠ 0 ∧
      meromorphicOrderAt
          (fun omega : ℂ =>
            GaloisForLFunctions.HTGeometry.hardyFun
                (thetaCuspHawkingCausalHardyKernel r hr)
                (thetaCuspHawkingCausalHardyNode r) *
              d4GravitationalHypergeometricBoundaryGreen omega (xiSpectralPoint q))
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q)) =
        ((-1 : ℤ) : WithTop ℤ) := by
  obtain ⟨q, hq⟩ :=
    (XiC_eq_zero_iff_exists_xiZeroCopy r.1).mp
      (thetaCuspHawkingBackreactionResonantMode_XiC_eq_zero r)
  have ha := norm_thetaCuspHawkingCausalHardyNode_lt_one r hr
  have heval :
      GaloisForLFunctions.HTGeometry.hardyFun
          (thetaCuspHawkingCausalHardyKernel r hr)
          (thetaCuspHawkingCausalHardyNode r) ≠ 0 := by
    unfold thetaCuspHawkingCausalHardyKernel
    rw [GaloisForLFunctions.HTGeometry.hardyFun_hardyKernel ha ha]
    apply inv_ne_zero
    rw [sub_ne_zero]
    intro h
    have hn := congrArg norm h
    simp at hn
    nlinarith [norm_nonneg (thetaCuspHawkingCausalHardyNode r)]
  refine ⟨q, hq, heval, ?_⟩
  let c : ℂ :=
    GaloisForLFunctions.HTGeometry.hardyFun
      (thetaCuspHawkingCausalHardyKernel r hr)
      (thetaCuspHawkingCausalHardyNode r)
  have hc : c ≠ 0 := by
    simpa only [c] using heval
  change meromorphicOrderAt
      ((fun _ : ℂ => c) *
        fun omega : ℂ =>
          d4GravitationalHypergeometricBoundaryGreen omega (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q)) = _
  rw [meromorphicOrderAt_mul_of_ne_zero analyticAt_const hc]
  exact d4GravitationalHypergeometricBoundaryGreen_order_qnmPlus_xi 0 q

end


end RHTower
