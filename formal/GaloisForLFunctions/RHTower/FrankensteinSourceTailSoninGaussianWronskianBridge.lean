import GaloisForLFunctions.RHTower.FrankensteinSourceTailSoninPhaseWork
import GaloisForLFunctions.RHTower.RouteRFixedTraceTailRoos

/-!
# Complete-source Sonin / Gaussian Wronskian bridge

This file identifies a single pre-divisor source current across four previously
separate constructions.  The complete-resolution tail and the two cofinal
Sonin Hardy orientations produce a nonnegative current.  It is exactly a
strictly positive source normalization times the squared reflected-Gaussian
Wronskian; after the canonical nowhere-zero transfer, the same identity holds
for every literal Route-R prime Bockstein coefficient.

The final diagonal theorem is one source law, not a post hoc matching of zero
sets:

* `ORIENT`: both Sonin phases survive until their source pairing;
* `COF + LAND`: one finite cofinal schedule lands on the source current;
* `COMP`: that one schedule has the normalized literal coefficient at every
  ordinary prime;
* `ORD`: the normalization is strictly positive on every Xi fibre.

It deliberately does not assert a global summability, budget, or annihilation
law for these coefficients.  Any such assertion is the remaining `DYN` gate
and is RH-strength in the present corpus.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- The reflected Gaussian Wronskian is the centered source rate times its
strictly positive Hermitian pair scale. -/
private theorem deningerMeyerReflectedGaussianLineWronskian_eq_rate_mul_pairScale
    (q : XiZeroCopy) :
    DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLineWronskian q =
      (primeDepthBVWoldXiCenteredRate q.1 : ℂ) *
        DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLinePairScale q := by
  rw [DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLineWronskian_eq_greenFracture_mul,
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re,
    primeDepthBVWoldXiCenteredRate]
  push_cast
  ring

/-- Positive source normalization converting the squared reflected-Gaussian
Wronskian into the complete-source Sonin work. -/
def sourceTailSoninGaussianWronskianGain (q : XiZeroCopy) : ℝ :=
  Real.log 2 ^ 2 * (1 - primeDepthBVWoldXiCenteredRate q.1 ^ 2) /
    (4 * (1 + primeDepthBVWoldXiCenteredRate q.1 ^ 2) ^ 2 *
      (DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLinePairScale q).re ^ 2)

/-- The source normalization is positive throughout the unconditional Xi
strip; it introduces neither a new zero nor a chosen prime label. -/
theorem sourceTailSoninGaussianWronskianGain_pos (q : XiZeroCopy) :
    0 < sourceTailSoninGaussianWronskianGain q := by
  rw [sourceTailSoninGaussianWronskianGain]
  have hstrip := sourceHorizontalXiCenteredRate_abs_lt_one q
  have hsq : primeDepthBVWoldXiCenteredRate q.1 ^ 2 < 1 := by
    have habsSq : |primeDepthBVWoldXiCenteredRate q.1| ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (abs_nonneg _) zero_le_one).2 hstrip
    calc
      primeDepthBVWoldXiCenteredRate q.1 ^ 2 =
          |primeDepthBVWoldXiCenteredRate q.1| ^ 2 := (sq_abs _).symm
      _ < (1 : ℝ) ^ 2 := habsSq
      _ = 1 := by norm_num
  have hnum : 0 < Real.log 2 ^ 2 * (1 - primeDepthBVWoldXiCenteredRate q.1 ^ 2) := by
    exact mul_pos (sq_pos_of_pos (Real.log_pos one_lt_two)) (by linarith)
  have hden : 0 < 4 * (1 + primeDepthBVWoldXiCenteredRate q.1 ^ 2) ^ 2 *
      (DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLinePairScale q).re ^ 2 := by
    have hscale :=
      DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLinePairScale_re_pos q
    exact mul_pos
      (mul_pos (by norm_num) (sq_pos_of_pos (by positivity)))
      (sq_pos_of_pos hscale)
  exact div_pos hnum hden

/-- **Quantitative source bridge.**  Complete-resolution/Sonin work is the
positive normalized square of the target-free reflected Gaussian Wronskian. -/
theorem sourceTailSoninPhaseWork_eq_gaussianWronskianGain_normSq
    (q : XiZeroCopy) :
    sourceTailSoninPhaseWork q =
      ((sourceTailSoninGaussianWronskianGain q *
        Complex.normSq
          (DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLineWronskian q) : ℝ) : ℂ) := by
  rw [sourceTailSoninPhaseWork_closedForm,
    sourceTailSoninGaussianWronskianGain,
    deningerMeyerReflectedGaussianLineWronskian_eq_rate_mul_pairScale,
    Complex.normSq_mul]
  have hscale :
      DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLinePairScale q =
        ((DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLinePairScale q).re : ℂ) := by
    rw [DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLinePairScale_eq_normSq]
    simp only [ofReal_re]
  rw [hscale]
  simp only [ofReal_re]
  rw [Complex.normSq_ofReal, Complex.normSq_ofReal]
  push_cast
  have hscale_ne :
      (DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLinePairScale q).re ≠ 0 :=
    ne_of_gt (DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLinePairScale_re_pos q)
  have hden_ne : 1 + primeDepthBVWoldXiCenteredRate q.1 ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (primeDepthBVWoldXiCenteredRate q.1)]
  field_simp [hscale_ne, hden_ne]

/-- Real-valued form of the quantitative source bridge. -/
theorem sourceTailSoninPhaseWork_re_eq_gaussianWronskianGain_normSq
    (q : XiZeroCopy) :
    (sourceTailSoninPhaseWork q).re =
      sourceTailSoninGaussianWronskianGain q *
        Complex.normSq
          (DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLineWronskian q) := by
  have h := congrArg Complex.re
    (sourceTailSoninPhaseWork_eq_gaussianWronskianGain_normSq q)
  simpa using h

/-- Dividing the literal Route-R prime Bockstein by its coefficient-faithful
pre-divisor transfer recovers the same source Wronskian on every prime fibre. -/
theorem normalizedRouteRPrimeGammaBockstein_eq_gaussianSourceWronskian
    (p : Nat.Primes) (q : XiZeroCopy) :
    ((primeActivationOccupancyFisherTwist
          (-(2 * (q.1 : ℂ).re - 1)) p -
        primeActivationOccupancyFisherTwist
          (2 * (q.1 : ℂ).re - 1) p : ℝ) : ℂ) /
        routeRPrimeGammaXiWronskianTransferFactor p q =
      DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLineWronskian q := by
  rw [routeRPrimeGammaBockstein_eq_gaussianSourceWronskianTransfer]
  field_simp [routeRPrimeGammaXiWronskianTransferFactor_ne_zero]

/-- **Coefficient-faithful source bridge.**  At every ordinary prime, the
complete-source/Sonin work is the same strictly positive normalization times
the normalized literal Route-R Bockstein square. -/
theorem sourceTailSoninPhaseWork_eq_normalizedRouteRPrimeGammaBockstein_normSq
    (p : Nat.Primes) (q : XiZeroCopy) :
    sourceTailSoninPhaseWork q =
      ((sourceTailSoninGaussianWronskianGain q *
        Complex.normSq
          (((primeActivationOccupancyFisherTwist
                (-(2 * (q.1 : ℂ).re - 1)) p -
              primeActivationOccupancyFisherTwist
                (2 * (q.1 : ℂ).re - 1) p : ℝ) : ℂ) /
            routeRPrimeGammaXiWronskianTransferFactor p q) : ℝ) : ℂ) := by
  rw [normalizedRouteRPrimeGammaBockstein_eq_gaussianSourceWronskian]
  exact sourceTailSoninPhaseWork_eq_gaussianWronskianGain_normSq q

/-- **Single-source multi-gate diagonal.**  One finite cofinal Sonin schedule
lands simultaneously on every normalized literal Route-R Bockstein square,
while the unchanged complete tail identifies the corresponding unnormalized
prime carrier. -/
theorem exists_sourceTailSoninGaussianWronskianPrimeBockstein_diagonal
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (q : XiZeroCopy) :
    ∃ Nseq : ℕ → ℕ,
      (∀ j, j < Nseq j) ∧
      (∀ p : Nat.Primes,
        Tendsto (fun j =>
          (I * ((Real.log 2 : ℝ) : ℂ) / 8) *
            (sourceZeroHorizontalTailLog q : ℂ) *
            soninCofinalCriticalPhaseOddFisherScore a c d r hc hcd hr
              (primeDepthBVWoldXiCenteredRate q.1) j (Nseq j))
          atTop
          (nhds ((sourceTailSoninGaussianWronskianGain q *
            Complex.normSq
              (((primeActivationOccupancyFisherTwist
                    (-(2 * (q.1 : ℂ).re - 1)) p -
                  primeActivationOccupancyFisherTwist
                    (2 * (q.1 : ℂ).re - 1) p : ℝ) : ℂ) /
                routeRPrimeGammaXiWronskianTransferFactor p q) : ℝ) : ℂ))) ∧
      (∀ p : Nat.Primes,
        sourceZeroHorizontalPrimeCarrier q p =
          primeGammaCofinalBocksteinCoefficient
            (-2 * sourceZeroHorizontalTailLog q / Real.log 2) p) := by
  obtain ⟨Nseq, hcofinal, hlimit, hcarrier⟩ :=
    exists_sourceTailSoninPhaseWork_diagonal a c d r ha hc hcd hda hr harc q
  refine ⟨Nseq, hcofinal, ?_, hcarrier⟩
  intro p
  rw [sourceTailSoninPhaseWork_eq_normalizedRouteRPrimeGammaBockstein_normSq p q] at hlimit
  exact hlimit

end RHTower
