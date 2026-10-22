import GaloisForLFunctions.RHTower.CCM.CCMActualHeadWallGramLightConeJetRecovery
import GaloisForLFunctions.HTGeometry.L2PairingEnergy

/-!
# Actual-head pairing of the wall-Gram light-cone jet

Spectral differentiation of the actual scalar wall chord survives pairing with the literal
Fourier density of an arbitrary actual head.  The two Suzuki light energies are complementary
positive remainders around this jet current, giving a sharp finite-packet contraction with no
phase choice, division, regularity hypothesis, or RH input.
-/

open Complex MeasureTheory
open scoped BigOperators

noncomputable section
namespace RHTower

/-- Positive center-reserve rate of one prime-power wall. -/
def ccmActualHeadWallCenterReserveRate
    (p : Nat.Primes) (e : ℕ) : ℝ :=
  let n := xiGammaEulerValuationNat (p, e)
  4 * Real.pi * Real.log n * criticalMellinAtomWeight n

/-- Actual-head pairing of the positive Suzuki light channel. -/
def ccmActualHeadWallPositiveLightRateEnergy
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) : ℝ :=
  ∫ xi : ℝ,
    (8 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) *
      normSq (suzukiCriticalWallPositiveLightAmplitude
        (2 * Real.pi * xi) p e)) *
      ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)

/-- Actual-head pairing of the negative Suzuki light channel. -/
def ccmActualHeadWallNegativeLightRateEnergy
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) : ℝ :=
  ∫ xi : ℝ,
    (8 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) *
      normSq (suzukiCriticalWallNegativeLightAmplitude
        (2 * Real.pi * xi) p e)) *
      ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)

/-- Spectral derivative current of the actual scalar wall chord on one actual head. -/
def ccmActualHeadWallChordJetCurrent
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) : ℝ :=
  ∫ xi : ℝ,
    deriv (fun x : ℝ =>
      normSq (ccmActualHeadMellinWallChord x
        (xiGammaEulerValuationNat (p, e)))) xi *
      ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)

/-- Positive light is the complementary center-reserve sheet to negative light. -/
theorem normSq_suzukiCriticalWallPositiveLightAmplitude_eq_centerReserve_add_imbalance
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) :
    normSq (suzukiCriticalWallPositiveLightAmplitude (2 * Real.pi * xi) p e) =
      (criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) +
        ccmActualHeadMatchedWallLightImbalance p e xi) / 2 := by
  let n := xiGammaEulerValuationNat (p, e)
  have hsum := normSq_suzukiCriticalWallLightAmplitudes_eq_vonMangoldt_div_sqrt
    (2 * Real.pi * xi) p e
  have hweight :
      ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) =
        criticalMellinAtomWeight n := by
    dsimp only [n]
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude,
      sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt]
  dsimp only [n] at hsum hweight ⊢
  rw [hweight] at hsum
  unfold ccmActualHeadMatchedWallLightImbalance
  linarith

/-- Positive-light division-free recovery is the opposite orientation of the negative sheet. -/
theorem positiveLight_sub_actualWallChord_deriv_eq_centerReserve
    (xi : ℝ) (p : Nat.Primes) (e : ℕ) :
    let n := xiGammaEulerValuationNat (p, e)
    8 * Real.pi * Real.log n *
          normSq (suzukiCriticalWallPositiveLightAmplitude
            (2 * Real.pi * xi) p e) -
        deriv (fun x : ℝ =>
          normSq (ccmActualHeadMellinWallChord x n)) xi =
      4 * Real.pi * Real.log n * criticalMellinAtomWeight n := by
  let n := xiGammaEulerValuationNat (p, e)
  have hpositive :=
    normSq_suzukiCriticalWallPositiveLightAmplitude_eq_centerReserve_add_imbalance
      p e xi
  have hderiv := congrFun
    (deriv_normSq_ccmActualHeadMellinWallChord_primePower p e) xi
  dsimp only [n] at hpositive hderiv ⊢
  rw [hpositive, hderiv]
  ring

theorem ccmActualHeadWallCenterReserveRate_pos
    (p : Nat.Primes) (e : ℕ) :
    0 < ccmActualHeadWallCenterReserveRate p e := by
  have hlog : 0 < Real.log (xiGammaEulerValuationNat (p, e) : ℝ) :=
    Real.log_pos (by exact_mod_cast (one_lt_xiGammaEulerValuationNat p e))
  have hw : 0 < criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) := by
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  unfold ccmActualHeadWallCenterReserveRate
  positivity

theorem integrable_ccmActualHeadMatchedWallLightImbalance_mul_density
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      ccmActualHeadMatchedWallLightImbalance p e xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) := by
  let n := xiGammaEulerValuationNat (p, e)
  let w := criticalMellinAtomWeight n
  let D : ℝ → ℝ := fun xi => ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)
  have hD : Integrable D := by
    dsimp only [D]
    exact integrable_norm_sq (fourierUnitary f)
  have hw : 0 ≤ w := by
    dsimp only [w]
    exact criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n
  have h := Integrable.mul_bdd (c := w) hD
    (by
      exact (by fun_prop : Continuous fun xi : ℝ =>
        w * Real.sin (2 * Real.pi * Real.log n * xi)).aestronglyMeasurable)
    (by
      filter_upwards with xi
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
      exact mul_le_of_le_one_right hw (Real.abs_sin_le_one _))
  refine h.congr (Filter.Eventually.of_forall fun xi => ?_)
  change D xi * (w * Real.sin (2 * Real.pi * Real.log n * xi)) =
    ccmActualHeadMatchedWallLightImbalance p e xi * D xi
  rw [ccmActualHeadMatchedWallLightImbalance_eq]
  dsimp only [n, w]
  ring

theorem integrable_ccmActualHeadWallPositiveLight_mul_density
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      normSq (suzukiCriticalWallPositiveLightAmplitude
        (2 * Real.pi * xi) p e) *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) := by
  let w := criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e))
  let D : ℝ → ℝ := fun xi => ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)
  have hD : Integrable D := by
    dsimp only [D]
    exact integrable_norm_sq (fourierUnitary f)
  have hB := integrable_ccmActualHeadMatchedWallLightImbalance_mul_density p e f
  have h := (hD.const_mul (w / 2)).add (hB.const_mul (1 / 2))
  refine h.congr (Filter.Eventually.of_forall fun xi => ?_)
  change w / 2 * D xi +
      1 / 2 * (ccmActualHeadMatchedWallLightImbalance p e xi * D xi) =
    normSq (suzukiCriticalWallPositiveLightAmplitude
      (2 * Real.pi * xi) p e) * D xi
  rw [normSq_suzukiCriticalWallPositiveLightAmplitude_eq_centerReserve_add_imbalance]
  dsimp only [w]
  ring

theorem integrable_ccmActualHeadWallNegativeLight_mul_density
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      normSq (suzukiCriticalWallNegativeLightAmplitude
        (2 * Real.pi * xi) p e) *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) := by
  let w := criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e))
  let D : ℝ → ℝ := fun xi => ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)
  have hD : Integrable D := by
    dsimp only [D]
    exact integrable_norm_sq (fourierUnitary f)
  have hB := integrable_ccmActualHeadMatchedWallLightImbalance_mul_density p e f
  have h := (hD.const_mul (w / 2)).sub (hB.const_mul (1 / 2))
  refine h.congr (Filter.Eventually.of_forall fun xi => ?_)
  change w / 2 * D xi -
      1 / 2 * (ccmActualHeadMatchedWallLightImbalance p e xi * D xi) =
    normSq (suzukiCriticalWallNegativeLightAmplitude
      (2 * Real.pi * xi) p e) * D xi
  rw [normSq_suzukiCriticalWallNegativeLightAmplitude_eq_centerReserve_sub_imbalance]
  dsimp only [w]
  ring

theorem integrable_ccmActualHeadWallPositiveLightRateEnergy_integrand
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      (8 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) *
        normSq (suzukiCriticalWallPositiveLightAmplitude
          (2 * Real.pi * xi) p e)) *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) := by
  have h := (integrable_ccmActualHeadWallPositiveLight_mul_density p e f).const_mul
    (8 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)))
  exact h.congr (Filter.Eventually.of_forall fun _ => by ring)

theorem integrable_ccmActualHeadWallNegativeLightRateEnergy_integrand
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      (8 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) *
        normSq (suzukiCriticalWallNegativeLightAmplitude
          (2 * Real.pi * xi) p e)) *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) := by
  have h := (integrable_ccmActualHeadWallNegativeLight_mul_density p e f).const_mul
    (8 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)))
  exact h.congr (Filter.Eventually.of_forall fun _ => by ring)

theorem integrable_ccmActualHeadWallChordJetCurrent_integrand
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    Integrable (fun xi : ℝ =>
      deriv (fun x : ℝ =>
        normSq (ccmActualHeadMellinWallChord x
          (xiGammaEulerValuationNat (p, e)))) xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) := by
  have h :=
    (integrable_ccmActualHeadMatchedWallLightImbalance_mul_density p e f).const_mul
      (4 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)))
  refine h.congr (Filter.Eventually.of_forall fun xi => ?_)
  change
    4 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) *
        (ccmActualHeadMatchedWallLightImbalance p e xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) =
      deriv (fun x : ℝ =>
        normSq (ccmActualHeadMellinWallChord x
          (xiGammaEulerValuationNat (p, e)))) xi *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)
  rw [congrFun (deriv_normSq_ccmActualHeadMellinWallChord_primePower p e) xi]
  ring

/-- Negative light is the exact positive remainder above the actual-head wall-chord jet. -/
theorem wallNegativeLightRateEnergy_add_chordJetCurrent_eq_centerReserve
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    ccmActualHeadWallNegativeLightRateEnergy p e f +
        ccmActualHeadWallChordJetCurrent p e f =
      ccmActualHeadWallCenterReserveRate p e * ‖f‖ ^ (2 : ℕ) := by
  rw [ccmActualHeadWallNegativeLightRateEnergy, ccmActualHeadWallChordJetCurrent,
    ← integral_add
      (integrable_ccmActualHeadWallNegativeLightRateEnergy_integrand p e f)
      (integrable_ccmActualHeadWallChordJetCurrent_integrand p e f)]
  calc
    (∫ xi : ℝ,
      (8 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) *
          normSq (suzukiCriticalWallNegativeLightAmplitude
            (2 * Real.pi * xi) p e)) *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) +
        deriv (fun x : ℝ =>
          normSq (ccmActualHeadMellinWallChord x
            (xiGammaEulerValuationNat (p, e)))) xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) =
      ∫ xi : ℝ, ccmActualHeadWallCenterReserveRate p e *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) := by
      apply integral_congr_ae
      filter_upwards with xi
      have hpoint := actualWallChord_deriv_add_negativeLight_eq_centerReserve xi p e
      dsimp only at hpoint
      unfold ccmActualHeadWallCenterReserveRate
      calc
        8 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) *
                normSq (suzukiCriticalWallNegativeLightAmplitude
                  (2 * Real.pi * xi) p e) *
              ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) +
            deriv (fun x : ℝ =>
              normSq (ccmActualHeadMellinWallChord x
                (xiGammaEulerValuationNat (p, e)))) xi *
              ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) =
          (8 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) *
                normSq (suzukiCriticalWallNegativeLightAmplitude
                  (2 * Real.pi * xi) p e) +
            deriv (fun x : ℝ =>
              normSq (ccmActualHeadMellinWallChord x
                (xiGammaEulerValuationNat (p, e)))) xi) *
              ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) := by ring
        _ = (4 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) *
              criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e))) *
              ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) := by rw [hpoint]
    _ = ccmActualHeadWallCenterReserveRate p e * ‖f‖ ^ (2 : ℕ) := by
      rw [integral_const_mul,
        ← HTGeometry.norm_l2_sq_eq_integral_norm_sq,
        fourierUnitary.norm_map]

/-- Positive light is the exact positive remainder below the actual-head wall-chord jet. -/
theorem wallPositiveLightRateEnergy_sub_chordJetCurrent_eq_centerReserve
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    ccmActualHeadWallPositiveLightRateEnergy p e f -
        ccmActualHeadWallChordJetCurrent p e f =
      ccmActualHeadWallCenterReserveRate p e * ‖f‖ ^ (2 : ℕ) := by
  rw [ccmActualHeadWallPositiveLightRateEnergy, ccmActualHeadWallChordJetCurrent,
    ← integral_sub
      (integrable_ccmActualHeadWallPositiveLightRateEnergy_integrand p e f)
      (integrable_ccmActualHeadWallChordJetCurrent_integrand p e f)]
  calc
    (∫ xi : ℝ,
      (8 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) *
          normSq (suzukiCriticalWallPositiveLightAmplitude
            (2 * Real.pi * xi) p e)) *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) -
        deriv (fun x : ℝ =>
          normSq (ccmActualHeadMellinWallChord x
            (xiGammaEulerValuationNat (p, e)))) xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ)) =
      ∫ xi : ℝ, ccmActualHeadWallCenterReserveRate p e *
        ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) := by
      apply integral_congr_ae
      filter_upwards with xi
      have hpoint := positiveLight_sub_actualWallChord_deriv_eq_centerReserve xi p e
      dsimp only at hpoint
      unfold ccmActualHeadWallCenterReserveRate
      calc
        8 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) *
                normSq (suzukiCriticalWallPositiveLightAmplitude
                  (2 * Real.pi * xi) p e) *
              ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) -
            deriv (fun x : ℝ =>
              normSq (ccmActualHeadMellinWallChord x
                (xiGammaEulerValuationNat (p, e)))) xi *
              ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) =
          (8 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) *
                normSq (suzukiCriticalWallPositiveLightAmplitude
                  (2 * Real.pi * xi) p e) -
            deriv (fun x : ℝ =>
              normSq (ccmActualHeadMellinWallChord x
                (xiGammaEulerValuationNat (p, e)))) xi) *
              ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) := by ring
        _ = (4 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) *
              criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e))) *
              ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ (2 : ℕ) := by rw [hpoint]
    _ = ccmActualHeadWallCenterReserveRate p e * ‖f‖ ^ (2 : ℕ) := by
      rw [integral_const_mul,
        ← HTGeometry.norm_l2_sq_eq_integral_norm_sq,
        fourierUnitary.norm_map]

theorem ccmActualHeadWallPositiveLightRateEnergy_nonneg
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    0 ≤ ccmActualHeadWallPositiveLightRateEnergy p e f := by
  unfold ccmActualHeadWallPositiveLightRateEnergy
  apply integral_nonneg
  intro xi
  have hlog : 0 ≤ Real.log (xiGammaEulerValuationNat (p, e) : ℝ) :=
    (Real.log_pos (by exact_mod_cast (one_lt_xiGammaEulerValuationNat p e))).le
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hlog)
        (Complex.normSq_nonneg _))
    (sq_nonneg _)

theorem ccmActualHeadWallNegativeLightRateEnergy_nonneg
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    0 ≤ ccmActualHeadWallNegativeLightRateEnergy p e f := by
  unfold ccmActualHeadWallNegativeLightRateEnergy
  apply integral_nonneg
  intro xi
  have hlog : 0 ≤ Real.log (xiGammaEulerValuationNat (p, e) : ℝ) :=
    (Real.log_pos (by exact_mod_cast (one_lt_xiGammaEulerValuationNat p e))).le
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hlog)
        (Complex.normSq_nonneg _))
    (sq_nonneg _)

/-- Sharp atomwise light-cone contraction of the actual-head wall-chord jet current. -/
theorem abs_ccmActualHeadWallChordJetCurrent_le_centerReserve
    (p : Nat.Primes) (e : ℕ) (f : SoninL2) :
    |ccmActualHeadWallChordJetCurrent p e f| ≤
      ccmActualHeadWallCenterReserveRate p e * ‖f‖ ^ (2 : ℕ) := by
  rw [abs_le]
  constructor
  · have hpos := ccmActualHeadWallPositiveLightRateEnergy_nonneg p e f
    have hbalance :=
      wallPositiveLightRateEnergy_sub_chordJetCurrent_eq_centerReserve p e f
    linarith
  · have hneg := ccmActualHeadWallNegativeLightRateEnergy_nonneg p e f
    have hbalance :=
      wallNegativeLightRateEnergy_add_chordJetCurrent_eq_centerReserve p e f
    linarith

/-- Total center reserve of a finite labeled prime-power packet. -/
def ccmActualHeadWallPacketCenterReserveRate
    (S : Finset (Nat.Primes × ℕ)) : ℝ :=
  ∑ pe ∈ S, ccmActualHeadWallCenterReserveRate pe.1 pe.2

/-- Total wall-chord jet current of a finite labeled prime-power packet. -/
def ccmActualHeadWallPacketChordJetCurrent
    (S : Finset (Nat.Primes × ℕ)) (f : SoninL2) : ℝ :=
  ∑ pe ∈ S, ccmActualHeadWallChordJetCurrent pe.1 pe.2 f

/-- Finite-packet contraction, retaining every prime-power label. -/
theorem abs_ccmActualHeadWallPacketChordJetCurrent_le_centerReserve
    (S : Finset (Nat.Primes × ℕ)) (f : SoninL2) :
    |ccmActualHeadWallPacketChordJetCurrent S f| ≤
      ccmActualHeadWallPacketCenterReserveRate S * ‖f‖ ^ (2 : ℕ) := by
  rw [ccmActualHeadWallPacketChordJetCurrent]
  calc
    |∑ pe ∈ S, ccmActualHeadWallChordJetCurrent pe.1 pe.2 f| ≤
        ∑ pe ∈ S, |ccmActualHeadWallChordJetCurrent pe.1 pe.2 f| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ pe ∈ S,
        ccmActualHeadWallCenterReserveRate pe.1 pe.2 * ‖f‖ ^ (2 : ℕ) := by
      gcongr with pe hpe
      exact abs_ccmActualHeadWallChordJetCurrent_le_centerReserve pe.1 pe.2 f
    _ = ccmActualHeadWallPacketCenterReserveRate S * ‖f‖ ^ (2 : ℕ) := by
      rw [ccmActualHeadWallPacketCenterReserveRate]
      simp only [Finset.sum_mul]

end RHTower
