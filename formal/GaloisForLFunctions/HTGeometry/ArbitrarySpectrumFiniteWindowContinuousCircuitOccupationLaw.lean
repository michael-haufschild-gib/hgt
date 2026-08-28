import GaloisForLFunctions.HTGeometry.ArbitrarySpectrumFiniteDetuningTensorWindowLaw
import GaloisForLFunctions.HTGeometry.FiniteWindowContinuousCircuitOccupationLaw

/-!
# Arbitrary-spectrum finite-window continuous-circuit occupation

Every finite spectrum, including degenerate and resonant spectra, obeys a translated-window upper
occupation law for the complete continuous two-qubit circuit class.  Exact retained resonances form
the persistent term; all retained nonresonant sheets pay an inverse-window detuning correction.
-/

open Real intervalIntegral MeasureTheory Set Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Unconditional finite-window continuous-circuit occupation law for an arbitrary finite spectrum.
No spectral genericity, simplicity, randomness, chaos, mixing, or Diophantine premise is used. -/
theorem arbitrarySpectrum_continuousCircuitCapture_finiteWindow_le
    {n d s : ℕ}
    (energy : Fin (d + 1) → ℝ)
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (N : ℕ) (u T : ℝ) (hT : 0 < T) :
    (volume
      (projectiveContinuousCircuitCaptureTimes energy e V s ∩
        Set.Ioc u (u + T))).toReal ≤
      (2 : ℝ) ^ d * T * atMostTwentiethCircuitEntropyBound n s *
        ((2 * finiteWindowContinuousCircuitCubeRadius / (2 * π) +
              periodicTentFejerError N
                (2 * finiteWindowContinuousCircuitCubeRadius)) ^ d +
          ((resonantPacketIndexSet N
              (RHTower.zeroProjectiveFrequency energy)).card : ℝ) *
            ((((N : ℝ) + 1)⁻¹ *
              (2 * finiteWindowContinuousCircuitCubeRadius / (2 * π) +
                periodicTentFejerError N
                  (2 * finiteWindowContinuousCircuitCubeRadius))) ^ d) +
          ((nonresonantPacketIndexSet N
              (RHTower.zeroProjectiveFrequency energy)).card : ℝ) *
            ((((N : ℝ) + 1)⁻¹ *
              (2 * finiteWindowContinuousCircuitCubeRadius / (2 * π) +
                periodicTentFejerError N
                  (2 * finiteWindowContinuousCircuitCubeRadius))) ^ d) *
            (2 / (T * finitePacketNonzeroDetuningFloor N
              (RHTower.zeroProjectiveFrequency energy)))) := by
  let net := atMostTwentiethCircuitNet n s
  let m := net.card
  let target := twentiethCircuitNetTarget (n := n) (s := s)
  let rho := finiteWindowContinuousCircuitCubeRadius
  let omega := RHTower.zeroProjectiveFrequency energy
  let centers : Fin m → Fin d → ℝ := fun a =>
    projectiveSpectralPointTubeAngularCenter e V
      (target a : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (1 / 10 : ℝ)
  have hsubTube :
      projectiveContinuousCircuitCaptureTimes energy e V s ⊆
        projectiveSpectralTubeFamilyAngularVisit e V m target
          (1 / 10 : ℝ) omega :=
    projectiveContinuousCircuitCaptureTimes_subset_twentiethTubeVisit energy e V
  have hsubCube :
      projectiveSpectralTubeFamilyAngularVisit e V m target
          (1 / 10 : ℝ) omega ⊆
        finiteCubeVisit rho centers omega := by
    exact projectiveSpectralTubeFamilyAngularVisit_subset_finiteCubeVisit
      e V m target (by norm_num)
        (by
          have h := two_arcsin_one_fifth_lt_finiteWindowContinuousCircuitCubeRadius
          norm_num at h ⊢
          exact h) omega
  have hsub :
      projectiveContinuousCircuitCaptureTimes energy e V s ∩ Set.Ioc u (u + T) ⊆
        finiteCubeVisit rho centers omega ∩ Set.Ioc u (u + T) :=
    Set.inter_subset_inter_left _ (hsubTube.trans hsubCube)
  have hrightFinite :
      volume (finiteCubeVisit rho centers omega ∩ Set.Ioc u (u + T)) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_Ioc_lt_top.ne
      (measure_mono Set.inter_subset_right)
  have hreal :
      (volume
        (projectiveContinuousCircuitCaptureTimes energy e V s ∩
          Set.Ioc u (u + T))).toReal ≤
        (volume
          (finiteCubeVisit rho centers omega ∩ Set.Ioc u (u + T))).toReal := by
    rw [← measureReal_def, ← measureReal_def]
    exact measureReal_mono hsub hrightFinite
  have hcube := arbitrarySpectrum_finiteCubeVisit_tensorMajorantWindowUpper
    omega N m finiteWindowContinuousCircuitCubeRadius_pos
      two_finiteWindowContinuousCircuitCubeRadius_le_pi centers u T hT
  have hcard : (m : ℝ) ≤ atMostTwentiethCircuitEntropyBound n s := by
    simpa [m, net] using atMostTwentiethCircuitNet_card_real_le n s
  have hdelta : 0 < finitePacketNonzeroDetuningFloor N omega :=
    finitePacketNonzeroDetuningFloor_pos N omega
  have hbase : 0 ≤
      2 * rho / (2 * π) + periodicTentFejerError N (2 * rho) :=
    add_nonneg
      (div_nonneg
        (mul_nonneg (by norm_num) finiteWindowContinuousCircuitCubeRadius_pos.le)
        (by positivity))
      (periodicTentFejerError_pos N
        (mul_pos (by norm_num) finiteWindowContinuousCircuitCubeRadius_pos)).le
  have hA : 0 ≤
      (((N : ℝ) + 1)⁻¹ *
        (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d :=
    pow_nonneg (mul_nonneg (inv_nonneg.mpr (by positivity)) hbase) _
  have hratio : 0 ≤ 2 / (T * finitePacketNonzeroDetuningFloor N omega) :=
    div_nonneg (by norm_num) (mul_nonneg hT.le hdelta.le)
  have hbracketNonneg : 0 ≤
      (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ d +
        ((resonantPacketIndexSet N omega).card : ℝ) *
          ((((N : ℝ) + 1)⁻¹ *
            (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d) +
        ((nonresonantPacketIndexSet N omega).card : ℝ) *
          ((((N : ℝ) + 1)⁻¹ *
            (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho))) ^ d) *
          (2 / (T * finitePacketNonzeroDetuningFloor N omega)) := by
    positivity
  refine hreal.trans (hcube.trans ?_)
  dsimp only [m, target, rho, omega, centers] at hcube ⊢
  have hscale : 0 ≤ (2 : ℝ) ^ d * T := mul_nonneg (by positivity) hT.le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard hscale) hbracketNonneg

end

end GaloisForLFunctions.HTGeometry
