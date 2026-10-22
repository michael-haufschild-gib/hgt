import GaloisForLFunctions.RHTower.CCM.CCMFirstClockExponentialTiltOdds
import GaloisForLFunctions.RHTower.CCM.CCMInfiniteConvolutionPrimeFaceRigidity

/-!
# CCM convolution–tilt odds rigidity universality

The separated exponential-tilt law and infinite convolution prime-face rigidity act on the same
literal irreducible-prime source.  Restricting the first theorem to that face and sewing it to the
second shows that scalar Gamma sewing followed by any infinite Dirichlet-convolution functional
cannot rotate first-clock counter/aligned odds.  It multiplies both chambers by one common prime
derivative.  If that derivative is nonnegative, the transformed critical face remains at least as
counter-biased as every safe Mellin exponent.
-/

open ArithmeticFunction Finset Set

namespace RHTower

noncomputable section

/-- Irreducible primes in the literal first CCM aperture. -/
def ccmFirstClockIrreduciblePrimeSupport (L : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌊Real.exp L⌋₊).filter Nat.Prime

/-- Aligned irreducible-prime mass after exponential tilt of the critical source. -/
def ccmFirstClockIrreduciblePrimeAlignedTiltMass (L θ : ℝ) : ℝ :=
  ∑ p ∈ ccmFirstClockIrreduciblePrimeSupport L,
    criticalMellinAtomWeight p *
      max (Real.sin ((2 * Real.pi / L) * Real.log p)) 0 *
      Real.exp (θ * Real.log p)

/-- Counter-phased irreducible-prime mass after exponential tilt of the critical source. -/
def ccmFirstClockIrreduciblePrimeCounterTiltMass (L θ : ℝ) : ℝ :=
  ∑ p ∈ ccmFirstClockIrreduciblePrimeSupport L,
    criticalMellinAtomWeight p *
      max (-Real.sin ((2 * Real.pi / L) * Real.log p)) 0 *
      Real.exp (θ * Real.log p)

/-- Aligned irreducible-prime mass at Mellin exponent `σ`. -/
def ccmFirstClockIrreduciblePrimeAlignedExponentMass (L σ : ℝ) : ℝ :=
  ∑ p ∈ ccmFirstClockIrreduciblePrimeSupport L,
    (p : ℝ) ^ (-σ) * ArithmeticFunction.vonMangoldt p *
      max (Real.sin ((2 * Real.pi / L) * Real.log p)) 0

/-- Counter-phased irreducible-prime mass at Mellin exponent `σ`. -/
def ccmFirstClockIrreduciblePrimeCounterExponentMass (L σ : ℝ) : ℝ :=
  ∑ p ∈ ccmFirstClockIrreduciblePrimeSupport L,
    (p : ℝ) ^ (-σ) * ArithmeticFunction.vonMangoldt p *
      max (-Real.sin ((2 * Real.pi / L) * Real.log p)) 0

/-- Increasing outward exponential tilt raises counter/aligned odds already on the irreducible
prime face. -/
theorem ccmFirstClockIrreduciblePrimeTilt_counterAligned_cross_mono
    {L θ₁ θ₂ : ℝ} (hL : 0 < L) (hθ : θ₁ ≤ θ₂) :
    ccmFirstClockIrreduciblePrimeCounterTiltMass L θ₂ *
        ccmFirstClockIrreduciblePrimeAlignedTiltMass L θ₁ ≥
      ccmFirstClockIrreduciblePrimeCounterTiltMass L θ₁ *
        ccmFirstClockIrreduciblePrimeAlignedTiltMass L θ₂ := by
  unfold ccmFirstClockIrreduciblePrimeCounterTiltMass
    ccmFirstClockIrreduciblePrimeAlignedTiltMass
  have hmono := finiteExponentialTilt_separatedOdds_mono
      (s := ccmFirstClockIrreduciblePrimeSupport L)
      (a := criticalMellinAtomWeight)
      (aligned := fun p =>
        max (Real.sin ((2 * Real.pi / L) * Real.log p)) 0)
      (counter := fun p =>
        max (-Real.sin ((2 * Real.pi / L) * Real.log p)) 0)
      (x := fun p => Real.log p)
      (c := L / 2) (θ₁ := θ₁) (θ₂ := θ₂)
      (ha := fun p _hp => criticalMellinAtomWeight_nonneg p)
      (haligned := fun _p _hp => le_max_right _ _)
      (hcounter := fun _p _hp => le_max_right _ _)
      (halignedSupport := by
        intro p hp hpos
        exact firstClock_aligned_support_le_half hL
          (log_mem_firstClockAperture
            (Finset.mem_filter.mp hp).1) hpos)
      (hcounterSupport := by
        intro p hp hpos
        exact firstClock_counter_support_half_le hL
          (log_mem_firstClockAperture
            (Finset.mem_filter.mp hp).1) hpos)
      hθ
  simpa only [finiteExponentialTiltMass] using hmono

theorem ccmFirstClockIrreduciblePrimeAlignedTiltMass_halfWeight_eq_exponentMass
    {L σ : ℝ} :
    ccmFirstClockIrreduciblePrimeAlignedTiltMass L (1 / 2 - σ) =
      ccmFirstClockIrreduciblePrimeAlignedExponentMass L σ := by
  unfold ccmFirstClockIrreduciblePrimeAlignedTiltMass
    ccmFirstClockIrreduciblePrimeAlignedExponentMass
  apply Finset.sum_congr rfl
  intro p hp
  rw [show criticalMellinAtomWeight p *
        max (Real.sin (2 * Real.pi / L * Real.log ↑p)) 0 *
          Real.exp ((1 / 2 - σ) * Real.log ↑p) =
      (criticalMellinAtomWeight p *
        Real.exp ((1 / 2 - σ) * Real.log ↑p)) *
          max (Real.sin (2 * Real.pi / L * Real.log ↑p)) 0 by ring,
    criticalMellinAtomWeight_mul_halfWeightTilt
      (Nat.Prime.pos (Finset.mem_filter.mp hp).2)]

theorem ccmFirstClockIrreduciblePrimeCounterTiltMass_halfWeight_eq_exponentMass
    {L σ : ℝ} :
    ccmFirstClockIrreduciblePrimeCounterTiltMass L (1 / 2 - σ) =
      ccmFirstClockIrreduciblePrimeCounterExponentMass L σ := by
  unfold ccmFirstClockIrreduciblePrimeCounterTiltMass
    ccmFirstClockIrreduciblePrimeCounterExponentMass
  apply Finset.sum_congr rfl
  intro p hp
  rw [show criticalMellinAtomWeight p *
        max (-Real.sin (2 * Real.pi / L * Real.log ↑p)) 0 *
          Real.exp ((1 / 2 - σ) * Real.log ↑p) =
      (criticalMellinAtomWeight p *
        Real.exp ((1 / 2 - σ) * Real.log ↑p)) *
          max (-Real.sin (2 * Real.pi / L * Real.log ↑p)) 0 by ring,
    criticalMellinAtomWeight_mul_halfWeightTilt
      (Nat.Prime.pos (Finset.mem_filter.mp hp).2)]

/-- Critical irreducible-prime odds dominate every safe Mellin exponent. -/
theorem ccmFirstClockIrreduciblePrime_critical_counterAlignedOdds_ge_safe
    {L σ : ℝ} (hL : 0 < L) (hσ : 1 / 2 ≤ σ) :
    ccmFirstClockIrreduciblePrimeCounterTiltMass L 0 *
        ccmFirstClockIrreduciblePrimeAlignedExponentMass L σ ≥
      ccmFirstClockIrreduciblePrimeCounterExponentMass L σ *
        ccmFirstClockIrreduciblePrimeAlignedTiltMass L 0 := by
  have h := ccmFirstClockIrreduciblePrimeTilt_counterAligned_cross_mono
    (L := L) (θ₁ := 1 / 2 - σ) (θ₂ := 0) hL (by linarith)
  rw [ccmFirstClockIrreduciblePrimeAlignedTiltMass_halfWeight_eq_exponentMass,
    ccmFirstClockIrreduciblePrimeCounterTiltMass_halfWeight_eq_exponentMass] at h
  exact h

/-- Aligned prime-face mass after scalar Gamma sewing and an infinite convolution functional. -/
def ccmGammaSewnConvolutionPrimeAlignedMass
    (c : ℕ → ℝ) (a L : ℝ) : ℝ :=
  ∑ p ∈ ccmFirstClockIrreduciblePrimeSupport L,
    (p : ℝ) ^ (-1 / 2 : ℝ) *
      dirichletConvolutionSeries c (ccmGammaSewnVonMangoldtSource a) p *
      max (Real.sin ((2 * Real.pi / L) * Real.log p)) 0

/-- Counter-phased prime-face mass after scalar Gamma sewing and convolution. -/
def ccmGammaSewnConvolutionPrimeCounterMass
    (c : ℕ → ℝ) (a L : ℝ) : ℝ :=
  ∑ p ∈ ccmFirstClockIrreduciblePrimeSupport L,
    (p : ℝ) ^ (-1 / 2 : ℝ) *
      dirichletConvolutionSeries c (ccmGammaSewnVonMangoldtSource a) p *
      max (-Real.sin ((2 * Real.pi / L) * Real.log p)) 0

/-- Gamma sewing and convolution multiply the aligned chamber by the prime derivative scalar. -/
theorem ccmGammaSewnConvolutionPrimeAlignedMass_eq_derivative_mul
    (c : ℕ → ℝ) (a L : ℝ) :
    ccmGammaSewnConvolutionPrimeAlignedMass c a L =
      dirichletConvolutionSeriesPrimeDerivative c a *
        ccmFirstClockIrreduciblePrimeAlignedTiltMass L 0 := by
  rw [ccmGammaSewnConvolutionPrimeAlignedMass,
    ccmFirstClockIrreduciblePrimeAlignedTiltMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpPrime := (Finset.mem_filter.mp hp).2
  rw [dirichletConvolutionSeries_apply_prime c
      (ccmGammaSewnVonMangoldtSource a) hpPrime,
    ccmGammaSewnVonMangoldtSource_apply_one,
    ccmGammaSewnVonMangoldtSource_apply_prime a hpPrime,
    criticalMellinAtomWeight,
    ArithmeticFunction.vonMangoldt_apply_prime hpPrime]
  simp only [zero_mul, Real.exp_zero, mul_one]
  ring

/-- Gamma sewing and convolution multiply the counter chamber by the same derivative scalar. -/
theorem ccmGammaSewnConvolutionPrimeCounterMass_eq_derivative_mul
    (c : ℕ → ℝ) (a L : ℝ) :
    ccmGammaSewnConvolutionPrimeCounterMass c a L =
      dirichletConvolutionSeriesPrimeDerivative c a *
        ccmFirstClockIrreduciblePrimeCounterTiltMass L 0 := by
  rw [ccmGammaSewnConvolutionPrimeCounterMass,
    ccmFirstClockIrreduciblePrimeCounterTiltMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpPrime := (Finset.mem_filter.mp hp).2
  rw [dirichletConvolutionSeries_apply_prime c
      (ccmGammaSewnVonMangoldtSource a) hpPrime,
    ccmGammaSewnVonMangoldtSource_apply_one,
    ccmGammaSewnVonMangoldtSource_apply_prime a hpPrime,
    criticalMellinAtomWeight,
    ArithmeticFunction.vonMangoldt_apply_prime hpPrime]
  simp only [zero_mul, Real.exp_zero, mul_one]
  ring

/-- **CCM convolution–tilt odds rigidity universality law.**  On the irreducible-prime face,
arbitrary scalar Gamma sewing and infinite convolution preserve critical counter/aligned odds
exactly.  If their common derivative scalar is nonnegative, the transformed face cannot improve
on the counter/aligned ordering of any safe Mellin exponent. -/
theorem ccmGammaSewnConvolution_irreduciblePrimeTiltOddsRigidity
    (c : ℕ → ℝ) (a : ℝ) {L σ : ℝ}
    (hL : 0 < L) (hσ : 1 / 2 ≤ σ)
    (hderivative : 0 ≤ dirichletConvolutionSeriesPrimeDerivative c a) :
    let D := dirichletConvolutionSeriesPrimeDerivative c a
    ccmGammaSewnConvolutionPrimeAlignedMass c a L =
        D * ccmFirstClockIrreduciblePrimeAlignedTiltMass L 0 ∧
      ccmGammaSewnConvolutionPrimeCounterMass c a L =
        D * ccmFirstClockIrreduciblePrimeCounterTiltMass L 0 ∧
      ccmGammaSewnConvolutionPrimeCounterMass c a L *
          ccmFirstClockIrreduciblePrimeAlignedTiltMass L 0 =
        ccmFirstClockIrreduciblePrimeCounterTiltMass L 0 *
          ccmGammaSewnConvolutionPrimeAlignedMass c a L ∧
      ccmGammaSewnConvolutionPrimeCounterMass c a L *
          ccmFirstClockIrreduciblePrimeAlignedExponentMass L σ ≥
        ccmFirstClockIrreduciblePrimeCounterExponentMass L σ *
          ccmGammaSewnConvolutionPrimeAlignedMass c a L := by
  dsimp only
  have haligned :=
    ccmGammaSewnConvolutionPrimeAlignedMass_eq_derivative_mul c a L
  have hcounter :=
    ccmGammaSewnConvolutionPrimeCounterMass_eq_derivative_mul c a L
  refine ⟨haligned, hcounter, ?_, ?_⟩
  · rw [haligned, hcounter]
    ring
  · rw [haligned, hcounter]
    have hsafe :=
      ccmFirstClockIrreduciblePrime_critical_counterAlignedOdds_ge_safe
        hL hσ
    calc
      ccmFirstClockIrreduciblePrimeCounterExponentMass L σ *
            (dirichletConvolutionSeriesPrimeDerivative c a *
              ccmFirstClockIrreduciblePrimeAlignedTiltMass L 0) =
          dirichletConvolutionSeriesPrimeDerivative c a *
            (ccmFirstClockIrreduciblePrimeCounterExponentMass L σ *
              ccmFirstClockIrreduciblePrimeAlignedTiltMass L 0) := by ring
      _ ≤ dirichletConvolutionSeriesPrimeDerivative c a *
            (ccmFirstClockIrreduciblePrimeCounterTiltMass L 0 *
              ccmFirstClockIrreduciblePrimeAlignedExponentMass L σ) :=
        mul_le_mul_of_nonneg_left hsafe hderivative
      _ = (dirichletConvolutionSeriesPrimeDerivative c a *
            ccmFirstClockIrreduciblePrimeCounterTiltMass L 0) *
          ccmFirstClockIrreduciblePrimeAlignedExponentMass L σ := by ring

end

end RHTower
