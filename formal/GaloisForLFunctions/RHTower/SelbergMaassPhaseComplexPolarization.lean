import GaloisForLFunctions.RHTower.SelbergMaassKernelWronskian

/-!
# Complex polarization of the arithmetic Maass phase average

The existing phase average recovers the real transfer loss.  Applying its same
identity to an imaginary second input recovers the missing imaginary component.
Thus the complete finite phase family recovers the Hermitian complex transfer
form exactly.  This makes the coordinate-weighted top Fourier pairing visible
to the same-residue coefficient kernel; it asserts no sign for that kernel.
-/

open Complex Set UpperHalfPlane ModularGroup MeasureTheory
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassPhaseComplexPolarization
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassCuspTransport
open SelbergMaassUnipotentBlocks SelbergMaassCharacterProjection SelbergMaassCharacterFourier
open SelbergMaassCharacterDynamics SelbergMaassCharacterSeamFlux SelbergMaassDilationStress
open SelbergMaassPhaseRellich SelbergMaassMixedLoss SelbergMaassTraceEnergy
open SelbergMaassPhaseStress SelbergMaassKernelWronskian
open GaloisForLFunctions.HTGeometry
noncomputable section

variable (N : ℕ) (r s : ZMod (N + 1))

def phaseAverageC (H : PhaseIndex N → ℂ) : ℂ :=
  ((((N + 1 : ℕ) : ℝ)⁻¹ ^ 3 / 2 : ℝ) : ℂ) * ∑ i, H i

private theorem lossPair_smul_I (v w : EuclideanSpace ℂ (Deck N)) :
    lossPair N r s v (Complex.I • w) = (complexLoss N r s w v).im := by
  rw [← complexLoss_re]
  have hright : complexLoss N r s v (Complex.I • w) =
      Complex.I * complexLoss N r s v w := by
    unfold complexLoss
    simp only [map_smul, inner_smul_right, mul_sub]
  calc
    (complexLoss N r s v (Complex.I • w)).re =
        (Complex.I * complexLoss N r s v w).re := by rw [hright]
    _ = ((starRingEnd ℂ) (complexLoss N r s v w)).im := by
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
        zero_sub, Complex.conj_im]
    _ = (complexLoss N r s w v).im := by rw [complexLoss_conj]

private theorem phaseAverageC_re (H : PhaseIndex N → ℂ) :
    (phaseAverageC N H).re = phaseAverage N (fun i => (H i).re) := by
  unfold phaseAverageC phaseAverage
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change ((((N + 1 : ℕ) : ℝ)⁻¹ ^ 3 / 2) * Complex.reCLM (∑ i, H i)) =
    (((N + 1 : ℕ) : ℝ)⁻¹ ^ 3 / 2) * ∑ i, Complex.reCLM (H i)
  rw [map_sum]

private theorem phaseAverageC_im (H : PhaseIndex N → ℂ) :
    (phaseAverageC N H).im = phaseAverage N (fun i => (H i).im) := by
  unfold phaseAverageC phaseAverage
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  change ((((N + 1 : ℕ) : ℝ)⁻¹ ^ 3 / 2) * Complex.imCLM (∑ i, H i)) =
    (((N + 1 : ℕ) : ℝ)⁻¹ ^ 3 / 2) * ∑ i, Complex.imCLM (H i)
  rw [map_sum]

theorem phaseAverageC_pair (v w : EuclideanSpace ℂ (Deck N)) :
    phaseAverageC N (fun i => phaseReadout N r s i v *
      (starRingEnd ℂ) (phaseReadout N r s i w)) =
      complexLoss N r s w v := by
  apply Complex.ext
  · rw [phaseAverageC_re]
    calc
      phaseAverage N (fun i =>
          (phaseReadout N r s i v * (starRingEnd ℂ) (phaseReadout N r s i w)).re) =
          lossPair N r s v w := phaseAverage_pair N r s v w
      _ = (complexLoss N r s v w).re := (complexLoss_re N r s v w).symm
      _ = (complexLoss N r s w v).re := by
        rw [← complexLoss_conj N r s v w]
        simp
  · rw [phaseAverageC_im]
    have h := phaseAverage_pair N r s v (Complex.I • w)
    rw [lossPair_smul_I] at h
    calc
      phaseAverage N (fun i =>
          (phaseReadout N r s i v * (starRingEnd ℂ) (phaseReadout N r s i w)).im) =
          phaseAverage N (fun i =>
            (phaseReadout N r s i v *
              (starRingEnd ℂ) (phaseReadout N r s i (Complex.I • w))).re) := by
            unfold phaseAverage
            congr 2
            funext i
            change (phaseReadout N r s i v *
              (starRingEnd ℂ) (phaseReadout N r s i w)).im =
              (phaseReadout N r s i v *
                (starRingEnd ℂ) (phaseReadout N r s i (Complex.I • w))).re
            rw [map_smul]
            simp only [smul_eq_mul, map_mul, Complex.conj_I]
            simp [Complex.mul_re, Complex.mul_im]
            ring
      _ = (complexLoss N r s w v).im := h

end
end GaloisForLFunctions.RHTower.SelbergMaassPhaseComplexPolarization
