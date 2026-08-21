import GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseDiskSchurCompletion
import GaloisForLFunctions.RHTower.SuzukiCofinalPositiveFinitePartNoGo

/-!
# Cofinal center-gauge obstruction for matched phase-disk completions

The two rotated Schur channels of the matched phase Gram disk are pointwise nonnegative and have
fixed trace `2 * criticalMellinAtomWeight n`.  Hence subtracting the center trace from the first
channel does not yield a trace-free positive completion: it is exactly the negative of the
orthogonal Schur channel.

At spectral center the first channel contains the entire trace and the orthogonal channel
vanishes.  On prime coordinates that center trace is exactly twice the Suzuki critical sharp
mass, so it is nonsummable.  The universal cofinal finite-part obstruction then shows that no
finite-valued positive linear functional can preserve all finite center-gauge cutoffs.  Thus any
global use of the local phase disks must cancel trace before positivity in a genuinely coupled
channel; scalar positive finite-part assembly is impossible.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate

noncomputable section
namespace RHTower

def ccmActualHeadMatchedPhaseSchurTraceComplementProfile (n : ℕ) (xi : ℝ) : ℝ :=
  criticalMellinAtomWeight n *
      (1 - Real.cos (2 * Real.pi * Real.log n * xi)) +
    (Real.cos (2 * Real.pi * Real.log n * xi) *
        ccmActualHeadMatchedCosinePhaseProfile n xi +
      Real.sin (2 * Real.pi * Real.log n * xi) *
        ccmActualHeadMatchedSinePhaseProfile n xi)

theorem ccmActualHeadMatchedPhaseSchurTraceComplementProfile_nonneg
    (n : ℕ) (xi : ℝ) :
    0 ≤ ccmActualHeadMatchedPhaseSchurTraceComplementProfile n xi := by
  let theta := 2 * Real.pi * Real.log n * xi
  let v : Fin 2 → ℝ :=
    ![Real.cos (theta / 2), Real.sin (theta / 2)]
  have hq :=
    (ccmActualHeadMatchedPhaseGramMatrix_posSemidef n xi).dotProduct_mulVec_nonneg v
  simp [ccmActualHeadMatchedPhaseGramMatrix, v, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two] at hq
  have hsum := ccmActualHeadMatchedPhaseProfiles_add_complement_eq_two_weight n xi
  have hcomplement : ccmActualHeadMatchedComplementaryCosinePhaseProfile n xi =
      2 * criticalMellinAtomWeight n -
        ccmActualHeadMatchedCosinePhaseProfile n xi := by linarith
  rw [hcomplement] at hq
  have htrig := Real.sin_sq_add_cos_sq (theta / 2)
  have hsin := Real.sin_two_mul (theta / 2)
  have hcos := Real.cos_two_mul (theta / 2)
  have htheta : 2 * (theta / 2) = theta := by ring
  rw [htheta] at hsin hcos
  unfold ccmActualHeadMatchedPhaseSchurTraceComplementProfile
  change 0 ≤ criticalMellinAtomWeight n * (1 - Real.cos theta) +
    (Real.cos theta * ccmActualHeadMatchedCosinePhaseProfile n xi +
      Real.sin theta * ccmActualHeadMatchedSinePhaseProfile n xi)
  have heq :
      criticalMellinAtomWeight n * (1 - Real.cos theta) +
          (Real.cos theta * ccmActualHeadMatchedCosinePhaseProfile n xi +
            Real.sin theta * ccmActualHeadMatchedSinePhaseProfile n xi) =
        Real.cos (theta / 2) *
            (ccmActualHeadMatchedCosinePhaseProfile n xi * Real.cos (theta / 2) +
              ccmActualHeadMatchedSinePhaseProfile n xi * Real.sin (theta / 2)) +
          Real.sin (theta / 2) *
            (ccmActualHeadMatchedSinePhaseProfile n xi * Real.cos (theta / 2) +
              (2 * criticalMellinAtomWeight n -
                ccmActualHeadMatchedCosinePhaseProfile n xi) * Real.sin (theta / 2)) := by
    rw [hsin, hcos]
    ring_nf at htrig ⊢
    linear_combination
      (ccmActualHeadMatchedCosinePhaseProfile n xi -
        2 * criticalMellinAtomWeight n) * htrig
  rw [heq]
  exact hq

theorem ccmActualHeadMatchedPhaseSchurCompletion_add_traceComplement_eq_two_weight
    (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseSchurCompletionProfile n xi +
        ccmActualHeadMatchedPhaseSchurTraceComplementProfile n xi =
      2 * criticalMellinAtomWeight n := by
  unfold ccmActualHeadMatchedPhaseSchurCompletionProfile
    ccmActualHeadMatchedPhaseSchurTraceComplementProfile
  ring

theorem ccmActualHeadMatchedPhaseSchurCompletion_sub_centerGauge_eq_neg_traceComplement
    (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseSchurCompletionProfile n xi -
        2 * criticalMellinAtomWeight n =
      -ccmActualHeadMatchedPhaseSchurTraceComplementProfile n xi := by
  linarith [ccmActualHeadMatchedPhaseSchurCompletion_add_traceComplement_eq_two_weight n xi]

theorem ccmActualHeadMatchedPhaseSchurCompletion_sub_centerGauge_nonpos
    (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedPhaseSchurCompletionProfile n xi -
        2 * criticalMellinAtomWeight n ≤ 0 := by
  rw [ccmActualHeadMatchedPhaseSchurCompletion_sub_centerGauge_eq_neg_traceComplement]
  exact neg_nonpos.mpr
    (ccmActualHeadMatchedPhaseSchurTraceComplementProfile_nonneg n xi)

theorem ccmActualHeadMatchedPhaseSchurCompletionProfile_zero (n : ℕ) :
    ccmActualHeadMatchedPhaseSchurCompletionProfile n 0 =
      2 * criticalMellinAtomWeight n := by
  unfold ccmActualHeadMatchedPhaseSchurCompletionProfile
  simp [ccmActualHeadMatchedCosinePhaseProfile]
  ring

theorem ccmActualHeadMatchedPhaseSchurTraceComplementProfile_zero (n : ℕ) :
    ccmActualHeadMatchedPhaseSchurTraceComplementProfile n 0 = 0 := by
  linarith [
    ccmActualHeadMatchedPhaseSchurCompletion_add_traceComplement_eq_two_weight n 0,
    ccmActualHeadMatchedPhaseSchurCompletionProfile_zero n]

/-- Center gauge carried by one prime coordinate of the local Schur completion. -/
def ccmActualHeadMatchedPhaseSchurPrimeCenterGauge (p : Nat.Primes) : ℝ :=
  ccmActualHeadMatchedPhaseSchurCompletionProfile (p : ℕ) 0

theorem ccmActualHeadMatchedPhaseSchurCompletionProfile_prime_zero
    (p : Nat.Primes) :
    ccmActualHeadMatchedPhaseSchurCompletionProfile (p : ℕ) 0 =
      2 * suzukiCriticalSharpPrimeMass p := by
  rw [ccmActualHeadMatchedPhaseSchurCompletionProfile_zero,
    suzukiCriticalSharpPrimeMass]
  have h :=
    criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude p 0
  simp only [xiGammaEulerValuationNat, zero_add, pow_one] at h
  rw [h]

theorem not_summable_ccmActualHeadMatchedPhaseSchurCompletionProfile_prime_zero :
    ¬ Summable (fun p : Nat.Primes =>
      ccmActualHeadMatchedPhaseSchurCompletionProfile (p : ℕ) 0) := by
  intro hsum
  have hscaled : Summable (fun p : Nat.Primes =>
      2 * suzukiCriticalSharpPrimeMass p) :=
    hsum.congr (fun p => ccmActualHeadMatchedPhaseSchurCompletionProfile_prime_zero p)
  exact not_summable_suzukiCriticalSharpPrimeMass
    ((summable_mul_left_iff (by norm_num : (2 : ℝ) ≠ 0)).mp hscaled)

theorem ccmActualHeadMatchedPhaseSchurPrimeCenterGauge_nonneg (p : Nat.Primes) :
    0 ≤ ccmActualHeadMatchedPhaseSchurPrimeCenterGauge p := by
  exact ccmActualHeadMatchedPhaseSchurCompletionProfile_nonneg (p : ℕ) 0

theorem not_summable_ccmActualHeadMatchedPhaseSchurPrimeCenterGauge :
    ¬ Summable ccmActualHeadMatchedPhaseSchurPrimeCenterGauge := by
  exact not_summable_ccmActualHeadMatchedPhaseSchurCompletionProfile_prime_zero

/-- Exact finite-cutoff extension condition for the center trace of the matched Schur disks. -/
def ExtendsCCMActualHeadMatchedPhaseSchurPrimeCenterGauge
    (Φ : (Nat.Primes → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ExtendsFiniteCoordinateWeight ccmActualHeadMatchedPhaseSchurPrimeCenterGauge Φ

/-- No finite-valued positive linear functional can preserve every finite matched-disk center
trace.  Therefore the local Schur completions cannot be globally assembled by a positive linear
finite part. -/
theorem not_exists_positive_ccmActualHeadMatchedPhaseSchurPrimeCenterGauge_extension :
    ¬ ∃ Φ : (Nat.Primes → ℝ) →ₗ[ℝ] ℝ,
      ExtendsCCMActualHeadMatchedPhaseSchurPrimeCenterGauge Φ ∧
        PositiveOnCoordinateCone Φ := by
  exact not_exists_positive_linear_extension_of_not_summable
    ccmActualHeadMatchedPhaseSchurPrimeCenterGauge_nonneg
    not_summable_ccmActualHeadMatchedPhaseSchurPrimeCenterGauge

/-- Every exact finite-valued center-gauge extension is unbounded below on pointwise nonnegative
prime observables. -/
theorem ccmActualHeadMatchedPhaseSchurPrimeCenterGauge_extension_unboundedBelow
    (Φ : (Nat.Primes → ℝ) →ₗ[ℝ] ℝ)
    (hext : ExtendsCCMActualHeadMatchedPhaseSchurPrimeCenterGauge Φ) (L : ℝ) :
    ∃ f : Nat.Primes → ℝ, (∀ p, 0 ≤ f p) ∧ Φ f < L := by
  exact finite_weight_extension_unboundedBelow_of_not_summable
    ccmActualHeadMatchedPhaseSchurPrimeCenterGauge_nonneg
    not_summable_ccmActualHeadMatchedPhaseSchurPrimeCenterGauge Φ hext L

end RHTower
