import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanNonrectangularErrors
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanCellIteration
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenErrorGrowth

/-!
# Exact rectangularized Harman minorant

This module rewrites the original Harman minorant into its exact good-cell pair/triple families and
two literal nonrectangular errors.  The source carrier remains `primesIco z D`; the larger aligned
schedule appears only in the proved error majorant.
-/

namespace RHTower.Sieve

open Filter Topology Finset

noncomputable section

theorem primesIco_subset_of_left_le
    {a b c : ℕ} (hab : a ≤ b) : primesIco b c ⊆ primesIco a c := by
  intro p hp
  have hp' := mem_primesIco.mp hp
  exact mem_primesIco.mpr ⟨hab.trans hp'.1, hp'.2⟩

/-- Good-cell part of the literal Harman minorant. -/
def mtHarmanRectangularMinorantMain {t : ℕ}
    (endpoint : ℕ → ℕ) (z Q D E n : ℕ) : ℂ :=
  (rho n z : ℂ) - (harmanS1 z Q n : ℂ) +
    mtHarmanPairCellFamilySiftSum (t := t) endpoint
      (primesIco z D) (E : ℝ) z n -
    mtHarmanTripleCellFamilySiftSum (t := t) endpoint
      (primesIco z D) (E : ℝ) z n

/-- Literal bad-cell remainder of the Harman minorant. -/
def mtHarmanRectangularMinorantError {t : ℕ}
    (endpoint : ℕ → ℕ) (z D E n : ℕ) : ℂ :=
  mtHarmanPairNonrectangularError (t := t) endpoint
      (primesIco z D) (E : ℝ) z n -
    mtHarmanTripleNonrectangularError (t := t) endpoint
      (primesIco z D) (E : ℝ) z n

/-- Exact source-faithful rectangularization of `rhoMinus`. -/
theorem rhoMinus_eq_rectangularMinorantMain_add_error
    {t : ℕ} {endpoint : ℕ → ℕ}
    (hendpoint : ∀ i, 1 ≤ endpoint i) (hmono : Monotone endpoint)
    (z Q D E n : ℕ) :
    ((rhoMinus z Q D E n : ℤ) : ℂ) =
      mtHarmanRectangularMinorantMain (t := t) endpoint z Q D E n +
        mtHarmanRectangularMinorantError (t := t) endpoint z D E n := by
  have hpair := mtHarmanAdmissiblePairSiftSum_eq_cells_add_error
    (t := t) hendpoint hmono (primesIco z D) (E : ℝ) z n
  rw [mtHarmanAdmissiblePairSiftSum_primesIco] at hpair
  have htriple := mtHarmanAdmissibleTripleSiftSum_eq_cells_add_error
    (t := t) hendpoint hmono (primesIco z D) (E : ℝ) z n
  rw [mtHarmanAdmissibleTripleSiftSum_primesIco] at htriple
  unfold rhoMinus mtHarmanRectangularMinorantMain mtHarmanRectangularMinorantError
  push_cast
  rw [hpair, htriple]
  ring

/-- Actual pair source `[z,D)` inherits the complete aligned-schedule `66δ_A` error bound. -/
theorem eventually_sum_normSq_mtHarmanPairNonrectangularError_actualSource_le
    (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (z D Y : ℕ) (E : ℝ),
      mtLowerCutoffNat X ≤ z → z ≤ D → (D : ℝ) ≤ X → 1 ≤ Y →
      let endpoint :=
        mtPaperAlignedEndpoint (mtLowerCutoffNat X) D (mtPaperWidth A X)
      let P := primesIco (mtLowerCutoffNat X) D
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtHarmanPairNonrectangularError
            (t := D - mtLowerCutoffNat X) endpoint (primesIco z D) E z n‖ ^ 2 ≤
        (4 : ℝ) ^ 2 * (Y : ℝ) *
          (1 + Real.log (Y : ℝ)) ^ (2 ^ 2 - 1) *
            (66 * mtPaperWidth A X) * ∑ q ∈ P, 1 / (q : ℝ) := by
  filter_upwards [
    eventually_sum_normSq_mtHarmanPairNonrectangularError_sourceSubset_paperAligned_le A]
    with X hX
  intro z D Y E hz hD hDX hY
  exact hX D Y E z (primesIco z D) (hz.trans hD) hDX hY
    (primesIco_subset_of_left_le hz)

/-- Actual triple source `[z,D)` inherits the complete aligned-schedule `68δ_A` error bound. -/
theorem eventually_sum_normSq_mtHarmanTripleNonrectangularError_actualSource_le
    (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (z D Y : ℕ) (E : ℝ),
      mtLowerCutoffNat X ≤ z → z ≤ D → (D : ℝ) ≤ X → 1 ≤ Y →
      let endpoint :=
        mtPaperAlignedEndpoint (mtLowerCutoffNat X) D (mtPaperWidth A X)
      let P := primesIco (mtLowerCutoffNat X) D
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtHarmanTripleNonrectangularError
            (t := D - mtLowerCutoffNat X) endpoint (primesIco z D) E z n‖ ^ 2 ≤
        (4 : ℝ) ^ 4 * (Y : ℝ) *
          (1 + Real.log (Y : ℝ)) ^ (2 ^ 4 - 1) *
            (68 * mtPaperWidth A X) * ∑ q ∈ P, 1 / (q : ℝ) := by
  filter_upwards [
    eventually_sum_normSq_mtHarmanTripleNonrectangularError_sourceSubset_paperAligned_le A]
    with X hX
  intro z D Y E hz hD hDX hY
  exact hX D Y E z (primesIco z D) (hz.trans hD) hDX hY
    (primesIco_subset_of_left_le hz)

def mtHarmanPairRectangularizationBudget
    (A : ℕ) (X : ℝ) (Y : ℕ) (P : Finset ℕ) : ℝ :=
  (4 : ℝ) ^ 2 * (Y : ℝ) *
    (1 + Real.log (Y : ℝ)) ^ (2 ^ 2 - 1) *
      (66 * mtPaperWidth A X) * ∑ q ∈ P, 1 / (q : ℝ)

def mtHarmanTripleRectangularizationBudget
    (A : ℕ) (X : ℝ) (Y : ℕ) (P : Finset ℕ) : ℝ :=
  (4 : ℝ) ^ 4 * (Y : ℝ) *
    (1 + Real.log (Y : ℝ)) ^ (2 ^ 4 - 1) *
      (68 * mtPaperWidth A X) * ∑ q ∈ P, 1 / (q : ℝ)

/-- The two literal bad-cell errors combine with only the sharp two-term Hilbert cost. -/
theorem eventually_sum_normSq_mtHarmanRectangularMinorantError_actualSource_le
    (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (z D Y E : ℕ),
      mtLowerCutoffNat X ≤ z → z ≤ D → (D : ℝ) ≤ X → 1 ≤ Y →
      let endpoint :=
        mtPaperAlignedEndpoint (mtLowerCutoffNat X) D (mtPaperWidth A X)
      let P := primesIco (mtLowerCutoffNat X) D
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtHarmanRectangularMinorantError
            (t := D - mtLowerCutoffNat X) endpoint z D E n‖ ^ 2 ≤
        2 * mtHarmanPairRectangularizationBudget A X Y P +
          2 * mtHarmanTripleRectangularizationBudget A X Y P := by
  filter_upwards [
    eventually_sum_normSq_mtHarmanPairNonrectangularError_actualSource_le A,
    eventually_sum_normSq_mtHarmanTripleNonrectangularError_actualSource_le A]
    with X hpairX htripleX
  intro z D Y E hz hD hDX hY
  dsimp only
  let endpoint :=
    mtPaperAlignedEndpoint (mtLowerCutoffNat X) D (mtPaperWidth A X)
  let P := primesIco (mtLowerCutoffNat X) D
  have hpair := hpairX z D Y (E : ℝ) hz hD hDX hY
  have htriple := htripleX z D Y (E : ℝ) hz hD hDX hY
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        ‖mtHarmanRectangularMinorantError
          (t := D - mtLowerCutoffNat X) endpoint z D E n‖ ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 Y,
        (2 * ‖mtHarmanPairNonrectangularError
            (t := D - mtLowerCutoffNat X) endpoint (primesIco z D) (E : ℝ) z n‖ ^ 2 +
          2 * ‖mtHarmanTripleNonrectangularError
            (t := D - mtLowerCutoffNat X) endpoint (primesIco z D) (E : ℝ) z n‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      unfold mtHarmanRectangularMinorantError
      simpa only [sub_eq_add_neg, norm_neg] using norm_add_sq_le_two
        (mtHarmanPairNonrectangularError
          (t := D - mtLowerCutoffNat X) endpoint (primesIco z D) (E : ℝ) z n)
        (-mtHarmanTripleNonrectangularError
          (t := D - mtLowerCutoffNat X) endpoint (primesIco z D) (E : ℝ) z n)
    _ = 2 * (∑ n ∈ Finset.Icc 1 Y,
          ‖mtHarmanPairNonrectangularError
            (t := D - mtLowerCutoffNat X) endpoint (primesIco z D) (E : ℝ) z n‖ ^ 2) +
        2 * (∑ n ∈ Finset.Icc 1 Y,
          ‖mtHarmanTripleNonrectangularError
            (t := D - mtLowerCutoffNat X) endpoint (primesIco z D) (E : ℝ) z n‖ ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * mtHarmanPairRectangularizationBudget A X Y P +
        2 * mtHarmanTripleRectangularizationBudget A X Y P := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa only [endpoint, P, mtHarmanPairRectangularizationBudget] using hpair
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa only [endpoint, P, mtHarmanTripleRectangularizationBudget] using htriple

end

end RHTower.Sieve
