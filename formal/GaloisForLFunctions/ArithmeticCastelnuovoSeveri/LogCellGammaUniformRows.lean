import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCellGammaNearFiniteRows
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCellGammaDistantRows
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCellGammaBoundaryRows

/-!
# Uniform complete logarithmic Gamma rows

Nearby endpoint differences telescope, touching cells have finite boundary
moments, and distant cells sum inside two fixed integrable tails. These four
classes cover every off-diagonal cell at every finite horizon.
-/

noncomputable section
open Finset
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry MeanZeroIntervals

private theorem ennreal_sum_union_le (f : ℕ → ℝ≥0∞) (A B : Finset ℕ) :
    (∑ b ∈ A ∪ B, f b) ≤ (∑ b ∈ A, f b) + ∑ b ∈ B, f b := by
  exact (le_self_add : (∑ b ∈ A ∪ B, f b) ≤
    (∑ b ∈ A ∪ B, f b) + ∑ b ∈ A ∩ B, f b).trans_eq
      (Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f))

/-- The integrated endpoint-error row has one uniform bound for every finite positive cell family. -/
theorem gamma_logCell_pairRow_le {a : ℕ} (ha : 1 ≤ a) (s : ℝ) (S : Finset ℕ)
    (hS : ∀ b ∈ S, 1 ≤ b) :
    (∑ b ∈ S.erase a, gammaIntervalPairDefect (s + Real.log (a : ℝ))
      (s + Real.log ((a + 1 : ℕ) : ℝ)) (s + Real.log (b : ℝ))
      (s + Real.log ((b + 1 : ℕ) : ℝ))) ≤
      ENNReal.ofReal ((12 * Real.exp (1 / 2) +
        2 * gammaTailMass (Real.log (3 / 2 : ℝ))) * logCellWidth a) := by
  let P : ℕ → ℝ≥0∞ := fun b => gammaIntervalPairDefect (s + Real.log (a : ℝ))
    (s + Real.log ((a + 1 : ℕ) : ℝ)) (s + Real.log (b : ℝ)) (s + Real.log ((b + 1 : ℕ) : ℝ))
  let U := S.filter (fun b => a + 2 ≤ b ∧ b ≤ 2 * a)
  let L := S.filter (fun b => b + 2 ≤ a ∧ a ≤ 2 * b)
  let F := S.filter (fun b => 2 * b < a ∨ 2 * a < b)
  let A := S.filter (fun b => b + 1 = a ∨ a + 1 = b)
  -- These four arithmetic ranges cover the row; overlaps only enlarge its bound.
  have hcover : S.erase a = ((U ∪ L) ∪ F) ∪ A := by
    ext b
    simp only [mem_erase, U, L, F, A, mem_union, mem_filter]
    by_cases hb : b ∈ S
    · have hb1 := hS b hb
      simp only [hb, true_and, and_true]
      omega
    · simp only [hb, and_false, false_and, or_self]
  have hU : (∑ b ∈ U, P b) ≤ ENNReal.ofReal (6 * Real.exp (1 / 2) * logCellWidth a) :=
    gamma_logCell_nearUpper_sum_le ha s U fun b hb => (mem_filter.mp hb).2
  have hL : (∑ b ∈ L, P b) ≤ ENNReal.ofReal (2 * Real.exp (1 / 2) * logCellWidth a) :=
    gamma_logCell_nearLower_sum_le ha s L fun b hb =>
      ⟨hS b (mem_filter.mp hb).1, (mem_filter.mp hb).2⟩
  have hF : (∑ b ∈ F, P b) ≤
      ENNReal.ofReal (2 * logCellWidth a * gammaTailMass (Real.log (3 / 2 : ℝ))) := by
    refine (sum_le_sum fun b (_hb : b ∈ F) =>
      show P b ≤ gammaIntervalKernel (s + Real.log (a : ℝ)) (s + Real.log ((a + 1 : ℕ) : ℝ))
        (s + Real.log (b : ℝ)) (s + Real.log ((b + 1 : ℕ) : ℝ)) from tsub_le_self).trans ?_
    exact gamma_logCell_distant_sum_le ha s F fun b hb =>
      ⟨hS b (mem_filter.mp hb).1, (mem_filter.mp hb).2⟩
  have hA : (∑ b ∈ A, P b) ≤ ENNReal.ofReal (4 * Real.exp (1 / 2) * logCellWidth a) :=
    gamma_logCell_adjacent_sum_le ha s A fun b hb => (mem_filter.mp hb).2
  have hw : 0 ≤ logCellWidth a := (logCellWidth_pos ha).le
  have ht : 0 ≤ gammaTailMass (Real.log (3 / 2 : ℝ)) :=
    gammaTailMass_nonneg (Real.log_pos (by norm_num))
  calc
    _ = ∑ b ∈ ((U ∪ L) ∪ F) ∪ A, P b := by rw [hcover]
    _ ≤ ((∑ b ∈ U, P b) + ∑ b ∈ L, P b) +
        (∑ b ∈ F, P b) + ∑ b ∈ A, P b :=
      (ennreal_sum_union_le P ((U ∪ L) ∪ F) A).trans
        (add_le_add ((ennreal_sum_union_le P (U ∪ L) F).trans
          (add_le_add (ennreal_sum_union_le P U L) le_rfl)) le_rfl)
    _ ≤ (ENNReal.ofReal (6 * Real.exp (1 / 2) * logCellWidth a) +
        ENNReal.ofReal (2 * Real.exp (1 / 2) * logCellWidth a)) +
        ENNReal.ofReal (2 * logCellWidth a * gammaTailMass (Real.log (3 / 2 : ℝ))) +
        ENNReal.ofReal (4 * Real.exp (1 / 2) * logCellWidth a) :=
      add_le_add (add_le_add (add_le_add hU hL) hF) hA
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

#print axioms gamma_logCell_pairRow_le

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
