import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPrimeCorrectionHasAUniformTail
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPoleProfilesAreAsymptoticallyOrthonormal
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePrimeRowCorrectionControlsTheResidual
import GaloisForLFunctions.TransThresholdPairCorrelation.ParitySensitiveRamanujanStabilizerTransfer

/-!
# Ramanujan pole profiles are quasimodes of the full prime matrix

The exact completed arithmetic row has adjunction energy. Its uniform summable
tail, together with Mertens and floor roundoff, makes the literal matrix residual
negligible in squared norm compared with the logarithmic mass of the profile.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticIntersectionTheory ArithmeticEffectivityTheory BezoutValuationIncidence

/-- The arithmetic energy attached to a Ramanujan conductor. -/
def ramanujanAdjunctionEnergy (m : ℕ) : ℝ :=
  Real.eulerMascheroniConstant + (Real.log m + tameDifferent m)

theorem normalizedRamanujanMode_eq_coefficient {m : ℕ} (hm : 0 < m) (n : ℕ) :
    normalizedRamanujanMode m n = ramanujanLagCoefficient m n / Real.sqrt (m.totient : ℝ) := by
  rw [normalizedRamanujanMode, TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hm]

theorem ramanujanPoleProfile_eq_mul_poleVector (m n : ℕ) :
    ramanujanPoleProfile m n = normalizedRamanujanMode m n * poleVector n := by
  unfold ramanujanPoleProfile poleVector
  ring

/-- The same tail controls every row after complete-period normalization. -/
theorem abs_normalizedRamanujan_correction_le_tail {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (y : ℕ) :
    |poleProfileCorrection (normalizedRamanujanMode m) y n +
      (Real.log m + tameDifferent m) * normalizedRamanujanMode m n| ≤
        ramanujanCorrectionTail m y / Real.sqrt (m.totient : ℝ) := by
  have hg : normalizedRamanujanMode m =
      fun j => ramanujanLagCoefficient m j / Real.sqrt (m.totient : ℝ) :=
    funext (normalizedRamanujanMode_eq_coefficient hm)
  rw [hg, poleProfileCorrection_div]
  have heq : poleProfileCorrection (ramanujanLagCoefficient m) y n / Real.sqrt (m.totient : ℝ) +
      (Real.log m + tameDifferent m) * (ramanujanLagCoefficient m n / Real.sqrt (m.totient : ℝ)) =
      ((∑ t ∈ Icc 1 y, ramanujanUpCorrectionTerm m n t) +
        (Real.log m + tameDifferent m) * ramanujanLagCoefficient m n +
          ramanujanDownCorrection m n) / Real.sqrt (m.totient : ℝ) := by
    rw [poleProfileCorrection_eq_divisor_jumps]
    change ((_ + ramanujanDownCorrection m n) / Real.sqrt (m.totient : ℝ) + _) = _
    unfold ramanujanUpCorrectionTerm
    ring
  rw [heq, abs_div, abs_of_nonneg (Real.sqrt_nonneg (m.totient : ℝ))]
  exact div_le_div_of_nonneg_right (abs_ramanujan_correction_error_le_tail hm hn y)
    (Real.sqrt_nonneg _)

/-- Every fixed positive conductor gives a full prime-matrix quasimode with
vanishing squared residual at logarithmic scale. -/
theorem tendsto_ramanujanPoleProfile_residual_sq {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N,
        ((∑ j ∈ Icc 1 N, weilPrimeKernel n j * ramanujanPoleProfile m j) -
          (Real.log N - ramanujanAdjunctionEnergy m) * ramanujanPoleProfile m n) ^ 2) /
            Real.log N) atTop (𝓝 0) := by
  have htail : Tendsto
      (fun y => ramanujanCorrectionTail m y / Real.sqrt (m.totient : ℝ)) atTop (𝓝 0) := by
    simpa only [zero_div] using (tendsto_ramanujanCorrectionTail m).div_const
      (Real.sqrt (m.totient : ℝ))
  have h := tendsto_poleProfileResidual_sq_of_correction (normalizedRamanujanMode m)
    (Real.log m + tameDifferent m) (∑ j ∈ range m, |normalizedRamanujanMode m j|)
    (abs_normalizedRamanujanMode_le hm)
    (fun y => ramanujanCorrectionTail m y / Real.sqrt (m.totient : ℝ)) htail
    (fun y n hn => abs_normalizedRamanujan_correction_le_tail hm hn y)
  simpa only [poleProfileResidual, ramanujanAdjunctionEnergy,
    ramanujanPoleProfile_eq_mul_poleVector] using h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

