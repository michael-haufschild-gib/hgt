import GaloisForLFunctions.RHTower.CCMActualHeadMatchedOrientedCharacteristicCocycle
import GaloisForLFunctions.RHTower.SuzukiWallFieldLightConeKernelCompletion

/-!
# Matched CCM wall-light incidence

The oriented matched cocycle makes Suzuki light-channel occurrence division-free and pointwise.
At a prime-power source, its arithmetic sine coordinate is exactly positive-light energy minus
negative-light energy.  Consequently a critical-weighted actual matched CCM cell has a spectral
normal form whose second channel is the literal Suzuki light imbalance, with no scalar division.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section
namespace RHTower

/-- Literal diagonal light imbalance of one Suzuki prime-power wall. -/
def ccmActualHeadMatchedWallLightImbalance
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) : ℝ :=
  normSq (suzukiCriticalWallPositiveLightAmplitude (2 * Real.pi * xi) p e) -
    normSq (suzukiCriticalWallNegativeLightAmplitude (2 * Real.pi * xi) p e)

/-- Wall-light imbalance is exactly the arithmetic sine coordinate of critical Mellin mass. -/
theorem ccmActualHeadMatchedWallLightImbalance_eq
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedWallLightImbalance p e xi =
      criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) *
        Real.sin (2 * Real.pi *
          Real.log (xiGammaEulerValuationNat (p, e)) * xi) := by
  let n := xiGammaEulerValuationNat (p, e)
  have hsquare := congrArg Complex.im
    (sq_suzukiCriticalWallField_eq_farHingeNumerator
      (2 * Real.pi * xi) p e)
  change ((suzukiCriticalWallField (2 * Real.pi * xi) p e) ^ 2).im =
    (((ArithmeticFunction.vonMangoldt n : ℂ) / (Real.sqrt n : ℂ)) *
      suzukiOscillatoryKernel ((2 * Real.pi * xi : ℝ) : ℂ)
        (Real.log n)).im at hsquare
  have hphase :
      (2 * Real.pi * xi) * Real.log (n : ℝ) =
        2 * Real.pi * Real.log (n : ℝ) * xi := by ring
  have him :
      ((suzukiCriticalWallField (2 * Real.pi * xi) p e) ^ 2).im =
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          Real.sin (2 * Real.pi * Real.log n * xi) := by
    rw [hsquare]
    have hkernel :
        (suzukiOscillatoryKernel ((2 * Real.pi * xi : ℝ) : ℂ)
          (Real.log (n : ℝ))).im =
            Real.sin ((2 * Real.pi * xi) * Real.log n) := by
      simp only [suzukiOscillatoryKernel]
      rw [show (Real.log n : ℂ) *
          (I * ((2 * Real.pi * xi : ℝ) : ℂ)) =
            ((((2 * Real.pi * xi) * Real.log n : ℝ) : ℂ) * I) by
        push_cast
        ring]
      rw [Complex.exp_mul_I]
      simp only [Complex.add_im, Complex.cos_ofReal_im, Complex.mul_im,
        Complex.sin_ofReal_re, Complex.I_im, Complex.sin_ofReal_im,
        Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    rw [Complex.mul_im, hkernel, hphase]
    norm_num
  unfold ccmActualHeadMatchedWallLightImbalance
  change _ = criticalMellinAtomWeight n * _
  rw [normSq_suzukiCriticalWallPositiveLightAmplitude_sub_negative, him,
    criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude,
    sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt]

/-- Pointwise division-free incidence symbol: even matched rebate plus literal Suzuki light
imbalance paired with the odd polar orientation profile. -/
def ccmActualHeadMatchedWallLightIncidenceSymbol
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) : ℝ :=
  let n := xiGammaEulerValuationNat (p, e)
  criticalMellinAtomWeight n *
      Real.cos (2 * Real.pi * Real.log n * xi) *
        ccmActualHeadMatchedCosinePhaseProfile n xi +
    ccmActualHeadMatchedWallLightImbalance p e xi *
      ccmActualHeadMatchedSinePhaseProfile n xi

/-- Incidence symbol is exactly critical mass times the real oriented cocycle. -/
theorem ccmActualHeadMatchedWallLightIncidenceSymbol_eq
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedWallLightIncidenceSymbol p e xi =
      criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) *
        (ccmActualHeadMatchedOrientedPhaseSymbol
          (xiGammaEulerValuationNat (p, e)) xi).re := by
  rw [ccmActualHeadMatchedWallLightIncidenceSymbol,
    ccmActualHeadMatchedWallLightImbalance_eq,
    ccmActualHeadMatchedOrientedPhaseSymbol_re]
  ring

theorem integrable_ccmActualHeadMatchedWallLightIncidenceSymbol_mul_density
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      ccmActualHeadMatchedWallLightIncidenceSymbol p e xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  let n := xiGammaEulerValuationNat (p, e)
  have h :=
    (integrable_ccmActualHeadMatchedOrientedPhaseSymbol_re_mul_density n f).const_mul
      (criticalMellinAtomWeight n)
  refine h.congr (Filter.Eventually.of_forall fun xi => ?_)
  change criticalMellinAtomWeight n *
        ((ccmActualHeadMatchedOrientedPhaseSymbol n xi).re *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) =
      ccmActualHeadMatchedWallLightIncidenceSymbol p e xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2
  rw [ccmActualHeadMatchedWallLightIncidenceSymbol_eq]
  dsimp only [n]
  ring

/-- **Division-free actual-cell occurrence.**  A critical-weighted actual matched CCM cell is
exactly the spectral integral of its even rebate and the literal positive-minus-negative Suzuki
light channel. -/
theorem criticalMellinAtomWeight_mul_matchedCell_eq_wallLightIncidence
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    let n := xiGammaEulerValuationNat (p, e)
    criticalMellinAtomWeight n *
        (criticalMellinAtomWeight n *
            ccmActualHeadTranslationDefect (Real.log n) f -
          ccmActualHeadOutgoingPolarSymmetricCell
            (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f) =
      -2 * ∫ xi : ℝ,
        ccmActualHeadMatchedWallLightIncidenceSymbol p e xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  dsimp only
  let n := xiGammaEulerValuationNat (p, e)
  rw [ccmActualHeadPrimeWeight_sub_matchedPolarCell_eq_orientedPhase]
  calc
    criticalMellinAtomWeight n *
        (-2 * ∫ xi : ℝ,
          (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) =
      -2 * (criticalMellinAtomWeight n *
        ∫ xi : ℝ,
          (ccmActualHeadMatchedOrientedPhaseSymbol n xi).re *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by ring
    _ = -2 * ∫ xi : ℝ,
        criticalMellinAtomWeight n *
          ((ccmActualHeadMatchedOrientedPhaseSymbol n xi).re *
            ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
      rw [integral_const_mul]
    _ = -2 * ∫ xi : ℝ,
        ccmActualHeadMatchedWallLightIncidenceSymbol p e xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
      congr 1
      apply integral_congr_ae
      filter_upwards with xi
      rw [ccmActualHeadMatchedWallLightIncidenceSymbol_eq]
      dsimp only [n]
      ring

/-- Negative light is exactly a scalar center reserve minus half the oriented light imbalance. -/
theorem normSq_suzukiCriticalWallNegativeLightAmplitude_eq_centerReserve_sub_imbalance
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) :
    normSq (suzukiCriticalWallNegativeLightAmplitude (2 * Real.pi * xi) p e) =
      (criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) -
        ccmActualHeadMatchedWallLightImbalance p e xi) / 2 := by
  have hsum := normSq_suzukiCriticalWallLightAmplitudes_eq_vonMangoldt_div_sqrt
    (2 * Real.pi * xi) p e
  rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude,
    sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt]
  unfold ccmActualHeadMatchedWallLightImbalance
  linarith

@[simp] theorem ccmActualHeadMatchedWallLightIncidenceSymbol_zero
    (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadMatchedWallLightIncidenceSymbol p e 0 = 0 := by
  rw [ccmActualHeadMatchedWallLightIncidenceSymbol_eq]
  simp

/-- The center reserve is strictly present at every literal prime-power wall. -/
theorem normSq_suzukiCriticalWallNegativeLightAmplitude_two_pi_zero_pos
    (p : Nat.Primes) (e : ℕ) :
    0 < normSq (suzukiCriticalWallNegativeLightAmplitude (2 * Real.pi * 0) p e) := by
  rw [normSq_suzukiCriticalWallNegativeLightAmplitude_eq_centerReserve_sub_imbalance,
    ccmActualHeadMatchedWallLightImbalance_eq]
  simp only [mul_zero, Real.sin_zero, sub_zero]
  have hw : 0 < criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) := by
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  linarith

/-- **Center-reserve no-go.**  Oriented matched incidence alone cannot pointwise dominate the raw
negative-light energy: it is blind exactly where every prime-power wall retains half its mass. -/
theorem not_negativeLight_le_abs_matchedWallLightIncidence
    (p : Nat.Primes) (e : ℕ) :
    ¬ ∀ xi : ℝ,
      normSq (suzukiCriticalWallNegativeLightAmplitude (2 * Real.pi * xi) p e) ≤
        |ccmActualHeadMatchedWallLightIncidenceSymbol p e xi| := by
  intro h
  have hzero := h 0
  rw [ccmActualHeadMatchedWallLightIncidenceSymbol_zero] at hzero
  simp only [abs_zero] at hzero
  exact (not_le_of_gt
    (normSq_suzukiCriticalWallNegativeLightAmplitude_two_pi_zero_pos p e)) hzero

/-- Finite packet of critical-weighted actual matched CCM cells. -/
def ccmActualHeadMatchedPrimePowerWallLightFiniteBlock
    (F : Finset (Nat.Primes × ℕ)) (f : SoninL2) : ℝ :=
  ∑ pe ∈ F,
    let n := xiGammaEulerValuationNat pe
    criticalMellinAtomWeight n *
      (criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f -
        ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f)

/-- Aggregate wall-light incidence symbol of a finite prime-power packet. -/
def ccmActualHeadMatchedWallLightFiniteIncidenceSymbol
    (F : Finset (Nat.Primes × ℕ)) (xi : ℝ) : ℝ :=
  ∑ pe ∈ F,
    ccmActualHeadMatchedWallLightIncidenceSymbol pe.1 pe.2 xi

/-- Finite rectangular source assembly preserves exact division-free wall-light occurrence. -/
theorem ccmActualHeadMatchedPrimePowerWallLightFiniteBlock_eq
    (F : Finset (Nat.Primes × ℕ)) (f : SoninL2) :
    ccmActualHeadMatchedPrimePowerWallLightFiniteBlock F f =
      -2 * ∫ xi : ℝ,
        ccmActualHeadMatchedWallLightFiniteIncidenceSymbol F xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  unfold ccmActualHeadMatchedPrimePowerWallLightFiniteBlock
  rw [show (∑ pe ∈ F,
      let n := xiGammaEulerValuationNat pe
      criticalMellinAtomWeight n *
        (criticalMellinAtomWeight n *
            ccmActualHeadTranslationDefect (Real.log n) f -
          ccmActualHeadOutgoingPolarSymmetricCell
            (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f)) =
      ∑ pe ∈ F, -2 * ∫ xi : ℝ,
        ccmActualHeadMatchedWallLightIncidenceSymbol pe.1 pe.2 xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 by
    apply Finset.sum_congr rfl
    intro pe hpe
    simpa only [Prod.eta] using
      criticalMellinAtomWeight_mul_matchedCell_eq_wallLightIncidence
        pe.1 pe.2 f]
  rw [← Finset.mul_sum]
  congr 1
  rw [← MeasureTheory.integral_finsetSum F
    (fun pe _ =>
      integrable_ccmActualHeadMatchedWallLightIncidenceSymbol_mul_density
        pe.1 pe.2 f)]
  apply integral_congr_ae
  filter_upwards with xi
  unfold ccmActualHeadMatchedWallLightFiniteIncidenceSymbol
  rw [Finset.sum_mul]

end RHTower
