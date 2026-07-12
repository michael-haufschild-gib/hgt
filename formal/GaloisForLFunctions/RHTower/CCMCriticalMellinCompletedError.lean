import GaloisForLFunctions.RHTower.PolarPrimeMellinDefect

/-!
# The completed critical-Mellin error as a Chebyshev potential

The square-root main terms in the polar and von Mangoldt channels cancel exactly.  What remains
is a normalized potential of the genuine Chebyshev error `psi(X) - X`.  Consequently the
equal-scale adjacent-block coefficient used by the rectangular RH detector is exactly a Haar
coefficient of this Chebyshev potential.

This is an unconditional source identity.  It does not assert the remaining one-sided subpower
estimate.
-/

open scoped BigOperators
open Finset MeasureTheory ArithmeticFunction Set

noncomputable section

namespace RHTower

/-- The completed critical-Mellin prime-polar error in logarithmic coordinates. -/
def criticalMellinCompletedError (h : ℝ) : ℝ :=
  4 * Real.sinh (h / 2) -
    ∑ k ∈ Icc 0 ⌊Real.exp h⌋₊,
      ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k

/-- The same completed error written entirely through the Chebyshev remainder. -/
def criticalMellinChebyshevPotential (h : ℝ) : ℝ :=
  1 - 2 / Real.sqrt (Real.exp h) -
    criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp h) /
      Real.sqrt (Real.exp h) -
    (1 / 2 : ℝ) * ∫ t in Ioc (1 : ℝ) (Real.exp h),
      criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) t *
        t ^ (-3 / 2 : ℝ)

/-- **Completed-error reduction.**  On the nonnegative logarithmic ray, the polar main term and
the critical von Mangoldt main term cancel exactly, leaving only the normalized Chebyshev error
and its critical Mellin primitive. -/
theorem criticalMellinCompletedError_eq_chebyshevPotential
    {h : ℝ} (hh : 0 ≤ h) :
    criticalMellinCompletedError h = criticalMellinChebyshevPotential h := by
  have hX : 1 ≤ Real.exp h := Real.one_le_exp hh
  have hsum := vonMangoldt_criticalMellinError_identity (Real.exp h) hX
  have hpolar := polarMultiplier_zero_eq_sqrtExp (h / 2)
  rw [polarMultiplier_zero, show 2 * (h / 2) = h by ring] at hpolar
  rw [criticalMellinCompletedError, criticalMellinChebyshevPotential, hsum]
  linear_combination (1 / 2 : ℝ) * hpolar

/-- Equal-scale adjacent logarithmic block imbalance of the completed error. -/
def criticalMellinAdjacentBlock (L x : ℝ) : ℝ :=
  (∫ h in Ioc (x - L) x, criticalMellinCompletedError h) -
    ∫ h in Ioc (x - 2 * L) (x - L), criticalMellinCompletedError h

/-- The corresponding adjacent block imbalance after Chebyshev reduction. -/
def criticalMellinChebyshevAdjacentBlock (L x : ℝ) : ℝ :=
  (∫ h in Ioc (x - L) x, criticalMellinChebyshevPotential h) -
    ∫ h in Ioc (x - 2 * L) (x - L), criticalMellinChebyshevPotential h

/-- **Adjacent-block Chebyshev law.**  Once both blocks lie on the nonnegative logarithmic ray,
the completed prime-polar Haar coefficient is exactly the Haar coefficient of the normalized
Chebyshev potential. -/
theorem criticalMellinAdjacentBlock_eq_chebyshevAdjacentBlock
    {L x : ℝ} (hL : 0 ≤ L) (hx : 2 * L ≤ x) :
    criticalMellinAdjacentBlock L x =
      criticalMellinChebyshevAdjacentBlock L x := by
  have hright :
      (∫ h in Ioc (x - L) x, criticalMellinCompletedError h) =
        ∫ h in Ioc (x - L) x, criticalMellinChebyshevPotential h := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hhmem
    apply criticalMellinCompletedError_eq_chebyshevPotential
    linarith [hhmem.1]
  have hleft :
      (∫ h in Ioc (x - 2 * L) (x - L), criticalMellinCompletedError h) =
        ∫ h in Ioc (x - 2 * L) (x - L), criticalMellinChebyshevPotential h := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hhmem
    apply criticalMellinCompletedError_eq_chebyshevPotential
    linarith [hhmem.1]
  rw [criticalMellinAdjacentBlock, criticalMellinChebyshevAdjacentBlock,
    hright, hleft]

/-- Logarithmic integer specialization of the adjacent-block Chebyshev law. -/
theorem criticalMellinAdjacentBlock_logSample_eq_chebyshevAdjacentBlock
    {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 2 * L ≤ Real.log n) :
    criticalMellinAdjacentBlock L (Real.log n) =
      criticalMellinChebyshevAdjacentBlock L (Real.log n) :=
  criticalMellinAdjacentBlock_eq_chebyshevAdjacentBlock hL hn

/-- The all-epsilon one-sided subpower problem for the completed adjacent blocks is literally the
same problem for the normalized Chebyshev potential.  This removes the polar main term and the
raw von Mangoldt sum from the remaining RH-bearing estimate without weakening its quantifiers. -/
theorem completedAdjacentBlock_subpowerLower_iff_chebyshevAdjacentBlock
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 2 * L ≤ Real.log n) :
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        0 ≤ criticalMellinAdjacentBlock L (Real.log n) + C * (n : ℝ) ^ epsilon) ↔
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        0 ≤ criticalMellinChebyshevAdjacentBlock L (Real.log n) +
          C * (n : ℝ) ^ epsilon) := by
  constructor
  · intro hlower epsilon hepsilon
    obtain ⟨C, hC, hlowerC⟩ := hlower epsilon hepsilon
    refine ⟨C, hC, fun n hn => ?_⟩
    rw [← criticalMellinAdjacentBlock_logSample_eq_chebyshevAdjacentBlock
      hL (hN n hn)]
    exact hlowerC n hn
  · intro hlower epsilon hepsilon
    obtain ⟨C, hC, hlowerC⟩ := hlower epsilon hepsilon
    refine ⟨C, hC, fun n hn => ?_⟩
    rw [criticalMellinAdjacentBlock_logSample_eq_chebyshevAdjacentBlock
      hL (hN n hn)]
    exact hlowerC n hn

end RHTower
