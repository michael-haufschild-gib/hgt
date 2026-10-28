import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFullWeilMatrixIsTheActualAtomicForm
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSeparatedMarkovMatrixHasExactCrossEntries
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheUniformMarginPaysThePoleOnlyUpToARootLogarithm

/-!
# Exact separation of the complete Weil matrix

The literal normalized matrix consists of the common self-energy, the full
prime kernel, the actual archimedean cross integral, and the two pole products.
The positive-integer index shift preserves every entry, including the diagonal.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticLorentzianGeometry ArithmeticElectrostatics
  ArithmeticEffectivityTheory SpacingScaleHarmonicAnalysis

theorem primeHorizonFinEquiv_val_add_one {N : ℕ} (n : PrimeHorizonIndex N) :
    ((primeHorizonFinEquiv N n : Fin N) : ℕ) + 1 = n := by
  change (n : ℕ) - 1 + 1 = n
  have h := mem_Icc.mp n.property
  omega

/-- The two actual pole rows become reciprocal square-root and square-root rows. -/
theorem atomPoleRow_primeHorizonFinEquiv_zero (g : ℝ → ℝ) {N : ℕ}
    (n : PrimeHorizonIndex N) :
    atomPoleRow g N 0 (primeHorizonFinEquiv N n) =
      (∫ u, g u * Real.exp (-(u / 2))) / Real.sqrt (n : ℕ) := by
  have hn0 : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (mem_Icc.mp n.property).1
  rw [atomPoleRow_zero_apply, primeHorizonFinEquiv_val_add_one,
    Real.exp_neg, ← Real.log_sqrt hn0.le, Real.exp_log (Real.sqrt_pos.mpr hn0)]
  ring

theorem atomPoleRow_primeHorizonFinEquiv_one (g : ℝ → ℝ) {N : ℕ}
    (n : PrimeHorizonIndex N) :
    atomPoleRow g N 1 (primeHorizonFinEquiv N n) =
      Real.sqrt (n : ℕ) * (∫ u, g u * Real.exp (u / 2)) := by
  have hn0 : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (mem_Icc.mp n.property).1
  rw [atomPoleRow_one_apply, primeHorizonFinEquiv_val_add_one,
    ← Real.log_sqrt hn0.le, Real.exp_log (Real.sqrt_pos.mpr hn0)]

/-- The arithmetic pole kernel is the sum of its two outer products. -/
def arithmeticPoleKernel (n j : ℕ) : ℝ :=
  Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n

/-- Exact complete matrix entries below the logarithmic atom spacing. -/
theorem fullWeilHorizonMatrix_apply_of_separated {g : ℝ → ℝ} {w : ℝ} {N : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w < atomSpacing N)
    (n j : PrimeHorizonIndex N) :
    fullWeilHorizonMatrix g N n j =
      (if (n : ℕ) = j then 2 * gammaHardyPhaseRate 0 * (∫ u, g u ^ 2) + levyEnergy g
       else -atomCrossTerm g |Real.log (j : ℕ) - Real.log (n : ℕ)|) -
      (∫ u, g u ^ 2) * weilPrimeKernel n j +
      ((∫ u, g u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2))) *
        arithmeticPoleKernel n j := by
  simp only [fullWeilHorizonMatrix, atomicWeilGram, atomicMarkovGram, Matrix.of_apply,
    primeHorizonFinEquiv_val_add_one,
    markovPair_atom_eq hsupp hw n.property j.property,
    atomPoleRow_primeHorizonFinEquiv_zero, atomPoleRow_primeHorizonFinEquiv_one,
    arithmeticPoleKernel]
  ring

/-- Atom-mass normalization leaves the literal prime kernel with coefficient minus one. -/
theorem normalizedFullWeilHorizonMatrix_apply_of_separated
    {g : ℝ → ℝ} {w : ℝ} {N : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w < atomSpacing N)
    (hG : (∫ u, g u ^ 2) ≠ 0) (n j : PrimeHorizonIndex N) :
    normalizedFullWeilHorizonMatrix g N n j =
      (if (n : ℕ) = j then 2 * gammaHardyPhaseRate 0 + levyEnergy g / (∫ u, g u ^ 2)
       else -atomCrossTerm g |Real.log (j : ℕ) - Real.log (n : ℕ)| / (∫ u, g u ^ 2)) -
      weilPrimeKernel n j +
      ((∫ u, g u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2)) /
        (∫ u, g u ^ 2)) * arithmeticPoleKernel n j := by
  rw [normalizedFullWeilHorizonMatrix, fullWeilHorizonMatrix_apply_of_separated hsupp hw]
  split_ifs <;> field_simp [hG]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

