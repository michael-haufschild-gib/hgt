import GaloisForLFunctions.RHTower.CCM.CCMPrimeGammaSourceEnergySpectrum
import GaloisForLFunctions.RHTower.CCM.CCMRectangularFullObservableDivisorTomography

/-!
# Off-critical Xi divisor tomography from one prime--Gamma source tail

The sharp rectangular explicit formula identifies every admissible prime--Gamma source sample
with the real part of the corresponding observable Weil sample.  The observable sample is real,
so the complex Dirichlet coefficients agree exactly.  The source L-series therefore inherits the
canonical meromorphic continuation, complete shifted right-Xi pole support, multiplicity-exact
residues, and RH holomorphy criterion of the observable tail.
-/

open Complex Filter Function Set
open scoped Topology

namespace RHTower

noncomputable section

/-- The real prime--Gamma source tail regarded as a complex Dirichlet coefficient. -/
def xiRectangularPrimeGammaTailDirichletCoefficient
    (L : ℝ) (N n : ℕ) : ℂ :=
  ((xiRectangularPrimeGammaTailCoefficient L N n : ℝ) : ℂ)

/-- Every observable rectangular tail coefficient is real. -/
theorem xiRectangularWeilTailCoefficient_im_eq_zero
    (L : ℝ) (N n : ℕ) :
    (xiRectangularWeilTailCoefficient L N n).im = 0 := by
  rw [xiRectangularWeilTailCoefficient]
  split
  · exact xiRectangularWeilLogCoefficient_im_eq_zero L n
  · rfl

/-- On every admissible tail, the complexified prime--Gamma coefficient is exactly the
observable Weil coefficient. -/
theorem xiRectangularPrimeGammaTailDirichletCoefficient_eq_weil
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    xiRectangularPrimeGammaTailDirichletCoefficient L N =
      xiRectangularWeilTailCoefficient L N := by
  funext n
  apply Complex.ext
  · simp only [xiRectangularPrimeGammaTailDirichletCoefficient,
      Complex.ofReal_re]
    exact congrFun
      (xiRectangularPrimeGammaTailCoefficient_eq_weilTail_re hL hN) n
  · simp only [xiRectangularPrimeGammaTailDirichletCoefficient,
      Complex.ofReal_im]
    exact (xiRectangularWeilTailCoefficient_im_eq_zero L N n).symm

/-- Canonical meromorphic continuation of the prime--Gamma source-tail L-series. -/
abbrev xiRectangularPrimeGammaTailContinuation
    (L : ℝ) (N : ℕ) : ℂ → ℂ :=
  xiRectangularWeilTailContinuation L N

/-- On its initial half-plane of absolute convergence, the prime--Gamma source-tail L-series
equals its canonical continuation. -/
theorem LSeries_xiRectangularPrimeGammaTailDirichletCoefficient_eq_continuation
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    {s : ℂ} (hs : 1 + delta < s.re) :
    LSeries (xiRectangularPrimeGammaTailDirichletCoefficient L N) s =
      xiRectangularPrimeGammaTailContinuation L N s := by
  rw [xiRectangularPrimeGammaTailDirichletCoefficient_eq_weil hL hN]
  exact LSeries_xiRectangularWeilTailCoefficient_eq_continuation
    hN hdelta0 hupper hs

/-- The prime--Gamma source continuation is meromorphic throughout `Re s > 1`. -/
theorem meromorphicOn_xiRectangularPrimeGammaTailContinuation_rightOne
    {L : ℝ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    MeromorphicOn (xiRectangularPrimeGammaTailContinuation L N)
      {s : ℂ | 1 < s.re} := by
  exact meromorphicOn_xiRectangularWeilTailContinuation_rightOne hN

/-- In `Re s > 1`, the source continuation has a simple pole exactly at each shifted right Xi
divisor point. -/
theorem meromorphicOrderAt_xiRectangularPrimeGammaTailContinuation_eq_neg_one_iff
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    {s : ℂ} (hs : 1 < s.re) :
    meromorphicOrderAt (xiRectangularPrimeGammaTailContinuation L N) s =
        ((-1 : ℤ) : WithTop ℤ) ↔
      ∃ q : XiRightZeroCopy, xiRightShiftedPole q = s := by
  exact meromorphicOrderAt_xiRectangularWeilTailContinuation_eq_neg_one_iff
    hL hN hs

/-- The source residue is twice the analytic multiplicity times the nonvanishing rectangular
window weight. -/
theorem meromorphicTrailingCoeffAt_xiRectangularPrimeGammaTailContinuation
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (q : XiRightZeroCopy) :
    meromorphicTrailingCoeffAt
        (xiRectangularPrimeGammaTailContinuation L N)
        (xiRightShiftedPole q) =
      2 * (xiRightMultiplicity q : ℂ) *
        xiRectangularRightCoefficient L q := by
  exact meromorphicTrailingCoeffAt_xiRectangularWeilTailContinuation
    hL hN q

/-- Normalized source residue recovers the exact analytic multiplicity. -/
theorem normalizedPrimeGammaTailResidue_eq_xiRightMultiplicity
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (q : XiRightZeroCopy) :
    meromorphicTrailingCoeffAt
        (xiRectangularPrimeGammaTailContinuation L N)
        (xiRightShiftedPole q) /
        (2 * xiRectangularRightCoefficient L q) =
      (xiRightMultiplicity q : ℂ) := by
  exact normalizedObservableResidue_eq_xiRightMultiplicity hL hN q

/-- Deleting different admissible finite prefixes changes only the holomorphic part of the
source continuation. -/
theorem meromorphicTrailingCoeffAt_xiRectangularPrimeGammaTailContinuation_cutoff_invariant
    {L : ℝ} (hL : 0 < L) {N₁ N₂ : ℕ}
    (hN₁ : ∀ n : ℕ, N₁ ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (hN₂ : ∀ n : ℕ, N₂ ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (q : XiRightZeroCopy) :
    meromorphicTrailingCoeffAt
        (xiRectangularPrimeGammaTailContinuation L N₁)
        (xiRightShiftedPole q) =
      meromorphicTrailingCoeffAt
        (xiRectangularPrimeGammaTailContinuation L N₂)
        (xiRightShiftedPole q) := by
  exact
    meromorphicTrailingCoeffAt_xiRectangularWeilTailContinuation_cutoff_invariant
      hL hN₁ hN₂ q

/-- RH is equivalent to holomorphy of one fixed-width prime--Gamma source-tail continuation
throughout `Re s > 1`. -/
theorem riemannHypothesis_iff_primeGammaTailContinuation_analytic_rightOne
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    RiemannHypothesis ↔
      ∀ s : ℂ, 1 < s.re →
        AnalyticAt ℂ
          (xiRectangularPrimeGammaTailContinuation L N) s := by
  exact riemannHypothesis_iff_observableTailContinuation_analytic_rightOne
    hL hN

end

end RHTower
