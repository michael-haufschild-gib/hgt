import GaloisForLFunctions.RHTower.XiHeatCassiniMassCriticalSmoothingWall
import GaloisForLFunctions.RHTower.XiMassHalfDensityAdjacentPrimeConnection

/-!
# Bounded Wold coframe of the Route-T half-density current

At the raw critical coefficient scale, the depth-one Wold profile is a compact diagonal smoothing.
Route T already carries a canonical half-density gauge, however.  After moving `sqrt(p)` into the
mass profile, the remaining arithmetic coefficient is `log(p)/p`; the Wold coefficient differs
from it only by the Euler factor `(1-1/p)^3`.  That factor and its inverse are uniformly bounded.

Thus the apparent compactness wall is entirely in the half-density conjugation, not in the
valuation-one arithmetic coframe.  This module gives the exact atomwise and cofinal source bridge.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Uniformly bounded inverse Euler factor converting depth-one Wold coefficients to the
half-density-gauged Route-T harmonic coefficients. -/
def xiHeatCassiniWoldInverseEulerFactor (p : Nat.Primes) : ℝ :=
  ((1 - 1 / (p : ℝ)) ^ 3)⁻¹

/-- Real harmonic coefficient of one prime in the Route-T half-density gauge. -/
def xiMassPrimeHarmonicRealCoefficient (p : Nat.Primes) : ℝ :=
  Real.log (p : ℝ) / (p : ℝ)

/-- The inverse Euler coframe is positive. -/
theorem xiHeatCassiniWoldInverseEulerFactor_pos (p : Nat.Primes) :
    0 < xiHeatCassiniWoldInverseEulerFactor p := by
  have hfactor : 0 < (1 - 1 / (p : ℝ)) ^ 3 := by
    linarith [(woldFactor_mem p).1]
  exact inv_pos.mpr hfactor

/-- Exact Wold-to-harmonic coframe conversion. -/
theorem xiHeatCassiniWoldInverseEulerFactor_mul_woldCoeff_one
    (p : Nat.Primes) :
    xiHeatCassiniWoldInverseEulerFactor p * woldCoeff 1 p =
      xiMassPrimeHarmonicRealCoefficient p := by
  have hfactor : (1 - 1 / (p : ℝ)) ^ 3 ≠ 0 :=
    (by linarith [(woldFactor_mem p).1] :
      0 < (1 - 1 / (p : ℝ)) ^ 3).ne'
  rw [xiHeatCassiniWoldInverseEulerFactor,
    xiMassPrimeHarmonicRealCoefficient, woldCoeff]
  simp only [pow_one]
  calc
    ((1 - 1 / (p : ℝ)) ^ 3)⁻¹ *
          ((1 - 1 / (p : ℝ)) ^ 3 * Real.log (p : ℝ) / (p : ℝ)) =
        (((1 - 1 / (p : ℝ)) ^ 3)⁻¹ *
          (1 - 1 / (p : ℝ)) ^ 3) *
            (Real.log (p : ℝ) / (p : ℝ)) := by ring
    _ = Real.log (p : ℝ) / (p : ℝ) := by
      rw [inv_mul_cancel₀ hfactor, one_mul]

/-- The inverse coframe never contracts a coordinate. -/
theorem one_le_xiHeatCassiniWoldInverseEulerFactor (p : Nat.Primes) :
    1 ≤ xiHeatCassiniWoldInverseEulerFactor p := by
  have hfactor : 0 < (1 - 1 / (p : ℝ)) ^ 3 := by
    linarith [(woldFactor_mem p).1]
  exact (one_le_inv₀ hfactor).2 (woldFactor_mem p).2

/-- Sharp uniform conditioning bound inherited from `1/8 ≤ (1-1/p)^3`. -/
theorem xiHeatCassiniWoldInverseEulerFactor_le_eight (p : Nat.Primes) :
    xiHeatCassiniWoldInverseEulerFactor p ≤ 8 := by
  have hfactor : 0 < (1 - 1 / (p : ℝ)) ^ 3 := by
    linarith [(woldFactor_mem p).1]
  have hinv : ((1 - 1 / (p : ℝ)) ^ 3)⁻¹ ≤ ((1 / 8 : ℝ))⁻¹ :=
    (inv_le_inv₀ hfactor (by norm_num : (0 : ℝ) < 1 / 8)).2
      (woldFactor_mem p).1
  simpa [xiHeatCassiniWoldInverseEulerFactor] using hinv

/-- The half-density harmonic coefficient and Wold coefficient are uniformly equivalent. -/
theorem woldCoeff_one_le_harmonic_le_eight_mul_woldCoeff_one
    (p : Nat.Primes) :
    woldCoeff 1 p ≤ xiMassPrimeHarmonicRealCoefficient p ∧
      xiMassPrimeHarmonicRealCoefficient p ≤ 8 * woldCoeff 1 p := by
  have hwold : 0 ≤ woldCoeff 1 p := woldCoeff_nonneg 1 p
  rw [← xiHeatCassiniWoldInverseEulerFactor_mul_woldCoeff_one]
  constructor
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_xiHeatCassiniWoldInverseEulerFactor p) hwold
  · exact mul_le_mul_of_nonneg_right
      (xiHeatCassiniWoldInverseEulerFactor_le_eight p) hwold

/-- Trace correction between logarithmic prime-cell mass and its Wold Euler depletion. -/
def xiHeatCassiniWoldEulerTraceCorrection (p : Nat.Primes) : ℝ :=
  xiMassPrimeHarmonicRealCoefficient p - woldCoeff 1 p

/-- Euler depletion correction is positive. -/
theorem xiHeatCassiniWoldEulerTraceCorrection_nonneg (p : Nat.Primes) :
    0 ≤ xiHeatCassiniWoldEulerTraceCorrection p := by
  exact sub_nonneg.mpr
    (woldCoeff_one_le_harmonic_le_eight_mul_woldCoeff_one p).1

/-- Euler depletion costs one full extra prime power. -/
theorem xiHeatCassiniWoldEulerTraceCorrection_le (p : Nat.Primes) :
    xiHeatCassiniWoldEulerTraceCorrection p ≤
      3 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
  let x : ℝ := 1 / (p : ℝ)
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    rw [div_le_one hp]
    linarith [two_le_prime_cast p]
  have hpoly : 1 - (1 - x) ^ 3 ≤ 3 * x := by
    have hmul : x ^ 2 * (x - 3) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) (by linarith)
    nlinarith
  have hlogdiv : 0 ≤ Real.log (p : ℝ) / (p : ℝ) := by
    exact div_nonneg (Real.log_nonneg (by linarith [two_le_prime_cast p])) hp.le
  rw [xiHeatCassiniWoldEulerTraceCorrection,
    xiMassPrimeHarmonicRealCoefficient, woldCoeff]
  simp only [pow_one]
  change Real.log (p : ℝ) / (p : ℝ) -
      (1 - x) ^ 3 * Real.log (p : ℝ) / (p : ℝ) ≤ _
  calc
    Real.log (p : ℝ) / (p : ℝ) -
        (1 - x) ^ 3 * Real.log (p : ℝ) / (p : ℝ) =
      (1 - (1 - x) ^ 3) *
        (Real.log (p : ℝ) / (p : ℝ)) := by ring
    _ ≤ (3 * x) * (Real.log (p : ℝ) / (p : ℝ)) :=
      mul_le_mul_of_nonneg_right hpoly hlogdiv
    _ = 3 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
      dsimp [x]
      field_simp [hp.ne']

/-- Wold depletion changes the logarithmic prime measure only by a positive finite measure. -/
theorem summable_xiHeatCassiniWoldEulerTraceCorrection :
    Summable xiHeatCassiniWoldEulerTraceCorrection := by
  have hmajor : Summable (fun p : Nat.Primes =>
      3 * xiMassPrimeSquareEulerWeight (1 / 2) p) :=
    (summable_xiMassPrimeSquareEulerWeight (by norm_num)).mul_left 3
  apply hmajor.of_nonneg_of_le xiHeatCassiniWoldEulerTraceCorrection_nonneg
  intro p
  calc
    xiHeatCassiniWoldEulerTraceCorrection p ≤
        3 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) :=
      xiHeatCassiniWoldEulerTraceCorrection_le p
    _ = 3 * xiMassPrimeSquareEulerWeight (1 / 2) p := by
      rw [xiMassPrimeSquareEulerWeight_eq]
      norm_num
      rw [div_eq_mul_inv]
      rfl

/-- Harmonic Route-T coefficient is square summable in the same coframe as Wold depth one. -/
theorem summable_xiMassPrimeHarmonicRealCoefficient_sq :
    Summable (fun p : Nat.Primes => xiMassPrimeHarmonicRealCoefficient p ^ 2) := by
  exact GaloisForLFunctions.HTGeometry.summable_logSq_div_sq.comp_injective
    Subtype.val_injective

/-- Exact arithmetic coefficient identity at the `n`th ordered prime. -/
theorem xiMassNthPrimeHarmonicCoefficient_eq_inverseEuler_mul_woldCoeff
    (n : ℕ) :
    xiMassNthPrimeHarmonicCoefficient n =
      ((xiHeatCassiniWoldInverseEulerFactor (nthPrimeSubtype n) *
        woldCoeff 1 (nthPrimeSubtype n) : ℝ) : ℂ) := by
  rw [xiMassNthPrimeHarmonicCoefficient]
  exact_mod_cast
    (xiHeatCassiniWoldInverseEulerFactor_mul_woldCoeff_one
      (nthPrimeSubtype n)).symm

/-- Every Route-T valuation-one prime atom is exactly a bounded inverse-Euler Wold coefficient
paired with the half-density mass profile. -/
theorem xiMassCenteredPrimeAtom_eq_inverseEulerWold_mul_halfDensityProfile
    (a : ℝ) (τ : ℂ) (n : ℕ) :
    xiMassCenteredPrimeAtom a τ (nthPrimeSubtype n : ℕ) =
      ((xiHeatCassiniWoldInverseEulerFactor (nthPrimeSubtype n) *
        woldCoeff 1 (nthPrimeSubtype n) : ℝ) : ℂ) *
        xiMassPrimeHalfDensityProfile a τ n := by
  rw [← xiMassHarmonicCoefficient_mul_halfDensityProfile_eq_centeredAtom,
    xiMassNthPrimeHarmonicCoefficient_eq_inverseEuler_mul_woldCoeff]

/-- Finite Wold-coframed Route-T source. -/
def xiHeatCassiniWoldHalfDensityPartialSource
    (a : ℝ) (τ : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N,
    ((xiHeatCassiniWoldInverseEulerFactor (nthPrimeSubtype n) *
      woldCoeff 1 (nthPrimeSubtype n) : ℝ) : ℂ) *
      xiMassPrimeHalfDensityProfile a τ n

/-- Wold coframe preserves every finite valuation-one Route-T source prefix exactly. -/
theorem xiHeatCassiniWoldHalfDensityPartialSource_eq_centeredAtom_sum
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    xiHeatCassiniWoldHalfDensityPartialSource a τ N =
      ∑ n ∈ Finset.range N,
        xiMassCenteredPrimeAtom a τ (nthPrimeSubtype n : ℕ) := by
  unfold xiHeatCassiniWoldHalfDensityPartialSource
  apply Finset.sum_congr rfl
  intro n hn
  exact (xiMassCenteredPrimeAtom_eq_inverseEulerWold_mul_halfDensityProfile
    a τ n).symm

/-- Cofinal Wold-coframed source prefixes land on the complete Route-T valuation-one layer. -/
theorem tendsto_xiHeatCassiniWoldHalfDensityPartialSource
    {a d : ℝ} (hhalf : 1 / 2 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto (fun N => xiHeatCassiniWoldHalfDensityPartialSource a τ (N + 1))
      atTop (nhds (xiMassValuationOnePrimeLayer a τ)) := by
  have hsource := tendsto_sum_range_xiMassNthPrimeCenteredAtom hhalf hda hτ
  exact hsource.congr' (Eventually.of_forall fun N =>
    (xiHeatCassiniWoldHalfDensityPartialSource_eq_centeredAtom_sum
      a τ (N + 1)).symm)

end

end RHTower
