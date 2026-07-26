import GaloisForLFunctions.HilbertMetric.GaussianMetricRankOneFracture
import GaloisForLFunctions.RHTower.XiMobiusIntegralApertureHilbertConnector
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances

/-!
# Gaussian completion of the transverse valuation aperture

The first transverse valuation increment already embeds every integral aperture injectively into
one real coordinate. Applying the HilbertMetric Gaussian distance kernel to that coordinate gives
a strictly positive Gram for every finite packet of distinct shifts, including a packet containing
the zero aperture.

This produces an exact radical comparison. The nonlinear Gaussian completion removes the zero
loop but retains every collision: its Gram is positive definite exactly when the shift labels are
distinct. The finite linear valuation Gram, completed Szegő Gram, continuous Möbius integral slice,
cofinite prime-jet geometry, and actual Xi differential matroid all add exactly one condition to
the Gaussian phase--the absence of a zero shift.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HilbertMetric
open Matrix
open scoped ComplexOrder Differential

open scoped UpperEndDifferentialInstances

/-- One-coordinate feature given by the first transverse valuation increment. -/
def xiTransversePrimeFirstValuationGaussianFeature
    (a : ℕ) (p : Nat.Primes) : Fin 1 → ℝ :=
  fun _ => xiTransversePrimeValuationIncrement a 0 p

/-- The first valuation increment separates every integral aperture, including zero. -/
theorem xiTransversePrimeFirstValuationGaussianFeature_injective (p : Nat.Primes) :
    Function.Injective
      (fun a : ℕ => xiTransversePrimeFirstValuationGaussianFeature a p) := by
  intro a b hab
  apply xiTransversePrimeApertureDiskNode_injective p
  have h0 := congrFun hab (0 : Fin 1)
  simpa [xiTransversePrimeFirstValuationGaussianFeature,
    xiTransversePrimeValuationIncrement] using h0

/-- Gaussian distance Gram of the first valuation-increment coordinates at bandwidth `t`. -/
def xiTransversePrimeFirstValuationGaussianGramMatrixAt
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  finiteGaussianDistanceGram
    (fun j => xiTransversePrimeFirstValuationGaussianFeature (shift j) p) t

/-- The bandwidth-`t` kernel depends only on squared separation of the two prime disk nodes. -/
theorem xiTransversePrimeFirstValuationGaussianGramMatrixAt_apply
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (t : ℝ) (i j : Fin N) :
    xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t i j =
      Real.exp (-t * (xiTransversePrimeApertureDiskNode (shift i) p -
        xiTransversePrimeApertureDiskNode (shift j) p) ^ 2) := by
  simp only [xiTransversePrimeFirstValuationGaussianGramMatrixAt,
    finiteGaussianDistanceGram, Fin.sum_univ_one]
  congr 2
  simp only [xiTransversePrimeFirstValuationGaussianFeature,
    xiTransversePrimeValuationIncrement, pow_zero, mul_one]
  ring

/-- **Positive-bandwidth Gaussian collision classification.** At every positive bandwidth, the
first-increment Gaussian Gram is strictly positive exactly when the integral shifts are distinct. -/
theorem xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t) :
    (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).PosDef ↔
      Function.Injective shift := by
  rw [xiTransversePrimeFirstValuationGaussianGramMatrixAt,
    finiteGaussianDistanceGram_posDef_iff_injective_of_pos _ ht]
  constructor
  · intro hcomp i j hij
    apply hcomp
    exact congrArg
      (fun a => xiTransversePrimeFirstValuationGaussianFeature a p) hij
  · intro hshift
    exact (xiTransversePrimeFirstValuationGaussianFeature_injective p).comp hshift

/-- Strict positivity is independent of the choice of positive Gaussian bandwidth. -/
theorem xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_bandwidth_invariant
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p s).PosDef ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).PosDef := by
  rw [xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective _ _ hs,
    xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective _ _ ht]

/-- At positive bandwidth, strict positivity is also independent of the chosen prime. -/
theorem xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_prime_invariant
    {N : ℕ} (shift : Fin N → ℕ) (p r : Nat.Primes)
    {t : ℝ} (ht : 0 < t) :
    (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).PosDef ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift r t).PosDef := by
  rw [xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective _ _ ht,
    xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective _ _ ht]

/-- The literal Gaussian matrix rank is the number of distinct integral shift labels, independently
of prime and positive bandwidth. -/
theorem xiTransversePrimeFirstValuationGaussianGramMatrixAt_rank_eq_image_card
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t) :
    (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).rank =
      (Finset.univ.image shift).card := by
  rw [xiTransversePrimeFirstValuationGaussianGramMatrixAt,
    finiteGaussianDistanceGram_rank_eq_image_card_of_pos _ ht]
  calc
    (Finset.univ.image
        (fun i => xiTransversePrimeFirstValuationGaussianFeature (shift i) p)).card =
        ((Finset.univ.image shift).image
          (fun a => xiTransversePrimeFirstValuationGaussianFeature a p)).card := by
      congr 1
      ext b
      simp
    _ = (Finset.univ.image shift).card :=
      Finset.card_image_of_injective _
        (xiTransversePrimeFirstValuationGaussianFeature_injective p)

/-- Unit-scale Gaussian distance Gram of the first valuation-increment coordinates. -/
def xiTransversePrimeFirstValuationGaussianGramMatrix
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    Matrix (Fin N) (Fin N) ℝ :=
  xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p 1

/-- The Gaussian kernel depends only on squared separation of the two prime disk nodes. -/
theorem xiTransversePrimeFirstValuationGaussianGramMatrix_apply
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) (i j : Fin N) :
    xiTransversePrimeFirstValuationGaussianGramMatrix shift p i j =
      Real.exp (-(xiTransversePrimeApertureDiskNode (shift i) p -
        xiTransversePrimeApertureDiskNode (shift j) p) ^ 2) := by
  simpa [xiTransversePrimeFirstValuationGaussianGramMatrix] using
    xiTransversePrimeFirstValuationGaussianGramMatrixAt_apply shift p 1 i j

/-- **Exact Gaussian collision classification.** The nonlinear Gaussian Gram is strictly positive
exactly when no two integral shift labels coincide; zero is an ordinary separated point rather
than a metric loop. -/
theorem xiTransversePrimeFirstValuationGaussianGramMatrix_posDef_iff_injective
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    (xiTransversePrimeFirstValuationGaussianGramMatrix shift p).PosDef ↔
      Function.Injective shift := by
  simpa [xiTransversePrimeFirstValuationGaussianGramMatrix] using
    xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective
      shift p (by norm_num : (0 : ℝ) < 1)

/-- Strict positivity of the first-increment Gaussian Gram is independent of the chosen prime. -/
theorem xiTransversePrimeFirstValuationGaussianGramMatrix_posDef_prime_invariant
    {N : ℕ} (shift : Fin N → ℕ) (p r : Nat.Primes) :
    (xiTransversePrimeFirstValuationGaussianGramMatrix shift p).PosDef ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrix shift r).PosDef := by
  rw [xiTransversePrimeFirstValuationGaussianGramMatrix_posDef_iff_injective,
    xiTransversePrimeFirstValuationGaussianGramMatrix_posDef_iff_injective]

/-- **Finite linear/Gaussian radical law.** The finite valuation Gram has exactly the Gaussian
collision condition plus exclusion of the zero aperture. -/
theorem
    xiTransversePrimeValuationGramMatrix_posDef_iff_firstGaussian_posDef_and_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    (xiTransversePrimeValuationGramMatrix shift p).PosDef ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrix shift p).PosDef ∧
        ∀ j, shift j ≠ 0 := by
  rw [xiTransversePrimeValuationGramMatrix_posDef_iff_injective_ne_zero,
    xiTransversePrimeFirstValuationGaussianGramMatrix_posDef_iff_injective]

/-- The completed transverse Szegő Gram adds exactly the same zero-aperture exclusion to the
Gaussian collision phase. -/
theorem
    xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_firstGaussian_posDef_and_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrix shift p).PosDef ∧
        ∀ j, shift j ≠ 0 := by
  rw [xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_injective_ne_zero,
    xiTransversePrimeFirstValuationGaussianGramMatrix_posDef_iff_injective]

/-- The continuous Möbius integral slice has the same exact radical comparison with the first
valuation Gaussian completion. -/
theorem
    xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_firstValuationGaussian_posDef_and_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p).PosDef ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrix shift p).PosDef ∧
        ∀ j, shift j ≠ 0 := by
  rw [xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_injective_ne_zero,
    xiTransversePrimeFirstValuationGaussianGramMatrix_posDef_iff_injective]

/-- **Gaussian/cofinite HTGeometry connector.** Deletion-robust prime-jet positivity is exactly
Gaussian collision separation together with exclusion of the zero shift. -/
theorem
    xiTransversePrimeJetApertureGram_cofinite_posDef_iff_firstValuationGaussian_posDef_and_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes) :
    (∀ forbidden : Set Nat.Primes, forbidden.Finite →
      ∃ points : Fin N × Fin (m + 1) → {r : Nat.Primes // r ∉ forbidden},
        (xiTransversePrimeJetApertureGram shift m forbidden points).PosDef) ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrix shift p).PosDef ∧
        ∀ j, shift j ≠ 0 := by
  rw [xiTransversePrimeJetApertureGram_cofinite_posDef_iff_injective_ne_zero,
    xiTransversePrimeFirstValuationGaussianGramMatrix_posDef_iff_injective]

/-- **Gaussian/analytic matroid connector.** Differential independence of the actual Xi shift
carriers is exactly Gaussian collision separation plus exclusion of the zero shift. -/
theorem
    xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_firstValuationGaussian_posDef_and_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrix shift p).PosDef ∧
        ∀ j, shift j ≠ 0 := by
  rw [
    xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_mobiusIntegralApertureSzegoGram_posDef,
    xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_firstValuationGaussian_posDef_and_ne_zero]

/-- The same Gaussian radical classification holds after adjoining every scalar prime-valuation
layer to the differential base. -/
theorem
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_firstValuationGaussian_posDef_and_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrix shift p).PosDef ∧
        ∀ j, shift j ≠ 0 := by
  rw [
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_mobiusIntegralApertureSzegoGram_posDef,
    xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_firstValuationGaussian_posDef_and_ne_zero]

/-! ### Bandwidth-universal radical laws -/

/-- At every positive bandwidth, the finite linear valuation Gram adds exactly exclusion of the
zero aperture to Gaussian collision separation. -/
theorem xiTransversePrimeValuationGramMatrix_posDef_iff_firstGaussianAt_posDef_and_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t) :
    (xiTransversePrimeValuationGramMatrix shift p).PosDef ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).PosDef ∧
        ∀ j, shift j ≠ 0 := by
  rw [xiTransversePrimeValuationGramMatrix_posDef_iff_injective_ne_zero,
    xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective _ _ ht]

/-- The same positive-bandwidth radical law holds for the completed transverse Szegő Gram. -/
theorem
    xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_firstGaussianAt_posDef_and_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t) :
    (xiTransversePrimeValuationSzegoGramMatrix shift p).PosDef ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).PosDef ∧
        ∀ j, shift j ≠ 0 := by
  rw [xiTransversePrimeValuationSzegoGramMatrix_posDef_iff_injective_ne_zero,
    xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective _ _ ht]

/-- The continuous Möbius integral slice obeys the same radical law at every positive Gaussian
bandwidth. -/
theorem
    xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_firstValuationGaussianAt_posDef_and_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t) :
    (xiMobiusPrimeIntegralApertureSzegoGramMatrix shift p).PosDef ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).PosDef ∧
        ∀ j, shift j ≠ 0 := by
  rw [xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_injective_ne_zero,
    xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective _ _ ht]

/-- Deletion-robust HTGeometry prime-jet positivity has the positive-bandwidth Gaussian radical
plus exactly exclusion of the zero shift. -/
theorem
    xiTransversePrimeJetApertureGram_cofinite_posDef_iff_firstValuationGaussianAt_posDef_and_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (p : Nat.Primes)
    {t : ℝ} (ht : 0 < t) :
    (∀ forbidden : Set Nat.Primes, forbidden.Finite →
      ∃ points : Fin N × Fin (m + 1) → {r : Nat.Primes // r ∉ forbidden},
        (xiTransversePrimeJetApertureGram shift m forbidden points).PosDef) ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).PosDef ∧
        ∀ j, shift j ≠ 0 := by
  rw [xiTransversePrimeJetApertureGram_cofinite_posDef_iff_injective_ne_zero,
    xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective _ _ ht]

/-- Differential independence over the rational-coordinate base has the same exact radical
description for every positive Gaussian bandwidth. -/
theorem
    xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_firstValuationGaussianAt_posDef_and_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).PosDef ∧
        ∀ j, shift j ≠ 0 := by
  rw [
    xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_mobiusIntegralApertureSzegoGram_posDef,
    xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_firstValuationGaussianAt_posDef_and_ne_zero
      shift p ht]

/-- The bandwidth-universal Gaussian radical law persists after adjoining all scalar valuation
layers to the differential base. -/
theorem
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_firstValuationGaussianAt_posDef_and_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun j => xiTransverseShiftUpperEndCarrier (shift j)) ↔
      (xiTransversePrimeFirstValuationGaussianGramMatrixAt shift p t).PosDef ∧
        ∀ j, shift j ≠ 0 := by
  rw [
    xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff_mobiusIntegralApertureSzegoGram_posDef,
    xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_firstValuationGaussianAt_posDef_and_ne_zero
      shift p ht]

end

end RHTower
