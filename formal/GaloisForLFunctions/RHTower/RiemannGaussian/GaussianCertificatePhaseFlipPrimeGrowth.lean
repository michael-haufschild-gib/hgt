import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianCertificatePeakObstruction

/-!
# Finite-prime cost at a Gaussian phase flip

At the phase flip `π / ε`, each fixed prime-power channel is controlled by
its logarithmic slope.  Together with the elementary peak law for a compact
Gaussian certificate, this isolates the only two possible payment channels:
the digamma gain and a retained prime block whose logarithmic slope mass is
large enough at that width.
-/

open Filter Set

namespace RiemannGaussian

noncomputable section

/-- The logarithmic slope mass of a finite prime-power block. -/
def gaussianPrimePhaseSlopeMass (indices : Finset ℕ) : ℝ :=
  ∑ n ∈ indices,
    ArithmeticFunction.vonMangoldt n / Real.sqrt n * |Real.log n|

/-- At the phase flip, every fixed finite prime-power block is bounded by its
logarithmic slope mass. -/
theorem gaussianPrimePartialOscillationEnergy_phaseFlip_le_slopeMass
    {ε : ℝ} (hε : 0 < ε) (indices : Finset ℕ) :
    gaussianPrimePartialOscillationEnergy ε (Real.pi / ε) indices ≤
      2 * Real.pi / (ε * Real.sqrt (Real.pi * ε)) *
        gaussianPrimePhaseSlopeMass indices := by
  rw [gaussianPrimePartialOscillationEnergy_eq_phaseSum]
  have hphase : ∀ n : ℕ,
      1 - Real.cos ((Real.pi / ε) * Real.log n) ≤
        (Real.pi / ε) * |Real.log n| := by
    intro n
    have hnonneg : 0 ≤ 1 - Real.cos ((Real.pi / ε) * Real.log n) :=
      sub_nonneg.mpr (Real.cos_le_one _)
    calc
      1 - Real.cos ((Real.pi / ε) * Real.log n) =
          |Real.cos ((Real.pi / ε) * Real.log n) - Real.cos 0| := by
            rw [Real.cos_zero, abs_sub_comm, abs_of_nonneg hnonneg]
      _ ≤ |(Real.pi / ε) * Real.log n - 0| :=
        Real.abs_cos_sub_cos_le _ _
      _ = (Real.pi / ε) * |Real.log n| := by
        rw [sub_zero, abs_mul, abs_of_pos (div_pos Real.pi_pos hε)]
  have hexp : ∀ n : ℕ,
      Real.exp (-(Real.log n) ^ (2 : ℕ) / (4 * ε)) ≤ 1 := by
    intro n
    rw [Real.exp_le_one_iff]
    have hden : 0 ≤ 4 * ε := mul_nonneg (by norm_num) hε.le
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg (Real.log n))) hden
  calc
    ∑ n ∈ indices, gaussianPrimeEnergyWeight ε n *
        (1 - Real.cos ((Real.pi / ε) * Real.log n)) ≤
      ∑ n ∈ indices,
        (2 / Real.sqrt (Real.pi * ε)) *
          ((ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
            ((Real.pi / ε) * |Real.log n|)) := by
        apply Finset.sum_le_sum
        intro n hn
        unfold gaussianPrimeEnergyWeight
        have hweight : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
          positivity
        have hfactor : 0 ≤ 2 / Real.sqrt (Real.pi * ε) := by positivity
        have hosc : 0 ≤ 1 - Real.cos ((Real.pi / ε) * Real.log n) :=
          sub_nonneg.mpr (Real.cos_le_one _)
        calc
          (2 / Real.sqrt (Real.pi * ε)) *
              (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
                Real.exp (-(Real.log n) ^ (2 : ℕ) / (4 * ε))) *
              (1 - Real.cos ((Real.pi / ε) * Real.log n)) =
            (2 / Real.sqrt (Real.pi * ε)) *
              ((ArithmeticFunction.vonMangoldt n / Real.sqrt n *
                Real.exp (-(Real.log n) ^ (2 : ℕ) / (4 * ε))) *
                (1 - Real.cos ((Real.pi / ε) * Real.log n))) := by ring
          _ ≤ (2 / Real.sqrt (Real.pi * ε)) *
              ((ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
                (1 - Real.cos ((Real.pi / ε) * Real.log n))) := by
              apply mul_le_mul_of_nonneg_left _ hfactor
              calc
                (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
                    Real.exp (-(Real.log n) ^ (2 : ℕ) / (4 * ε))) *
                    (1 - Real.cos ((Real.pi / ε) * Real.log n)) =
                  (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
                    (Real.exp (-(Real.log n) ^ (2 : ℕ) / (4 * ε)) *
                      (1 - Real.cos ((Real.pi / ε) * Real.log n))) := by ring
                _ ≤ (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
                    (1 * (1 - Real.cos ((Real.pi / ε) * Real.log n))) := by
                    gcongr
                    exact hexp n
                _ = (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
                    (1 - Real.cos ((Real.pi / ε) * Real.log n)) := by ring
          _ ≤ (2 / Real.sqrt (Real.pi * ε)) *
              ((ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
                ((Real.pi / ε) * |Real.log n|)) := by
              apply mul_le_mul_of_nonneg_left _ hfactor
              exact mul_le_mul_of_nonneg_left (hphase n) hweight
    _ = 2 * Real.pi / (ε * Real.sqrt (Real.pi * ε)) *
        gaussianPrimePhaseSlopeMass indices := by
        unfold gaussianPrimePhaseSlopeMass
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring

/-- A compact phase-flip certificate must pay its explicit elementary peak by
the digamma gain and the logarithmic slope mass of its retained prime block. -/
theorem GaussianArithmeticWidthCertificate.phaseFlipPeak_le_digammaGain_add_slopeMass
    {ε : ℝ} (certificate : GaussianArithmeticWidthCertificate ε)
    (hphaseRadius : Real.pi / ε ≤ certificate.compactRadius) :
    4 * Real.exp (ε / 4) +
        4 * Real.exp (ε / 4 - Real.pi ^ (2 : ℕ) / ε) ≤
      gaussianDigammaGain ε (Real.pi / ε) +
        2 * Real.pi / (ε * Real.sqrt (Real.pi * ε)) *
          gaussianPrimePhaseSlopeMass (Finset.range certificate.cutoff) := by
  have hpeak := certificate.phaseFlipPeak_le_digammaGain_add_partialOscillation
    hphaseRadius
  have hpartial := gaussianPrimePartialOscillationEnergy_phaseFlip_le_slopeMass
    certificate.width_pos (Finset.range certificate.cutoff)
  linarith

end

end RiemannGaussian
