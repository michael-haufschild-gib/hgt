import GaloisForLFunctions.SignedArithmeticHodgeTheory.PaddedGradedGridsHaveUniformGammaControl
import GaloisForLFunctions.SignedArithmeticHodgeTheory.StoppingCellsFormAUniformlyGradedPartition
import GaloisForLFunctions.SignedArithmeticHodgeTheory.ActualGeneratorHeadsAreLocalIntervalMeans
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.DisjointStepsHaveLogarithmicGammaCost

/-!
# One original Gamma reserve pays the actual generator head and tail

The whole-orbit cutoff is averaging on a uniformly graded stopping partition.
A finite source permits zero padding at both ends. The averaged-kernel bound
then pays the complete head, and the quadratic triangle inequality pays the
discarded profile. The constant is independent of the generator cutoff, source
horizon, coefficients and every retained translation level.
-/

noncomputable section
open MeasureTheory Set RHTower

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open HTGeometry ArithmeticCastelnuovoSeveri.LogCells
open ArithmeticCastelnuovoSeveri.IntervalVariance

private theorem stoppingGrid_cell (A : ℕ+) {k : ℕ} (hk : 0 < k) :
    ∃ (j : ℕ) (a : ℕ+), (a : ℕ) < 2 * (A : ℕ) ∧
      (j = 0 ∨ (A : ℕ) ≤ (a : ℕ)) ∧
      stoppingGridBoundary A k = dyadicBlockLeft j a ∧
      stoppingGridBoundary A (k + 1) = dyadicBlockRight j a := by
  by_cases hka : k < (A : ℕ)
  · let a : ℕ+ := ⟨k, hk⟩
    refine ⟨0, a, by change k < 2 * (A : ℕ); omega, Or.inl rfl, ?_, ?_⟩
    · rw [stoppingGridBoundary_initial A hk hka.le, dyadicBlockLeft_eq]
      simp only [Nat.cast_zero, zero_mul, zero_add]
      rfl
    · rw [stoppingGridBoundary_initial A (by omega) (by omega), dyadicBlockRight_eq]
      simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_add, Nat.cast_one]
      rfl
  · let j := (k - (A : ℕ)) / (A : ℕ)
    let r := (k - (A : ℕ)) % (A : ℕ)
    have hr : r < (A : ℕ) := Nat.mod_lt _ A.pos
    have he : k = (A : ℕ) + j * (A : ℕ) + r := by
      have hd := Nat.mod_add_div (k - (A : ℕ)) (A : ℕ)
      dsimp only [j, r]
      rw [Nat.mul_comm] at hd
      omega
    let a : ℕ+ := ⟨(A : ℕ) + r, by have := A.pos; omega⟩
    refine ⟨j, a, by change (A : ℕ) + r < 2 * (A : ℕ); omega,
      Or.inr (by change (A : ℕ) ≤ (A : ℕ) + r; omega), ?_, ?_⟩
    · rw [he, stoppingGridBoundary_band A j r hr.le, dyadicBlockLeft_eq]
      rfl
    · rw [he, show (A : ℕ) + j * (A : ℕ) + r + 1 =
        (A : ℕ) + j * (A : ℕ) + (r + 1) by omega,
        stoppingGridBoundary_band A j (r + 1) (by omega), dyadicBlockRight_eq]
      congr 1
      congr 1
      change (((A : ℕ) + (r + 1) : ℕ) : ℝ) = (((A : ℕ) + r : ℕ) : ℝ) + 1
      push_cast
      ring

private theorem intervalMean_zero_of_zero {a b : ℝ} {f : ℝ → ℝ}
    (hz : ∀ x ∈ Ioo a b, f x = 0) : intervalMean a b f = 0 := by
  have hi : (∫ x in Ioo a b, f x) = 0 := by
    calc
      _ = ∫ _x in Ioo a b, (0 : ℝ) := setIntegral_congr_fun measurableSet_Ioo hz
      _ = 0 := by simp only [integral_zero]
  rw [intervalMean, hi, zero_div]

private theorem stoppingGrid_exists_padding (A : ℕ+) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ R < stoppingGridBoundary A (N - 1) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨j, hj⟩ := exists_nat_gt ((R + 2 - Real.log (A : ℝ)) / Real.log 2)
  let N := (A : ℕ) + (j + 2) * (A : ℕ)
  have hN : 2 ≤ N := by
    have hm := Nat.mul_le_mul_right (A : ℕ) (show 2 ≤ j + 2 by omega)
    have hA := A.pos
    dsimp only [N]
    omega
  have hB : R + 1 < stoppingGridBoundary A N := by
    have hm := mul_lt_mul_of_pos_right hj hlog
    rw [div_mul_cancel₀ _ hlog.ne'] at hm
    dsimp only [N]
    rw [stoppingGridBoundary_band_start]
    push_cast
    linarith only [hm, hlog]
  have hw := stoppingGridWidth_le_one A (N - 1)
  have he := stoppingGridBoundary_succ A (N - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ N)] at he
  exact ⟨N, hN, by linarith only [hB, hw, he]⟩

/-- The literal all-level head is uniformly bounded in the original homogeneous Gamma energy. -/
theorem actualGeneratorHead_gamma_le {ι : Type*} [Fintype ι]
    (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) :
    levyEnergy (actualGeneratorHeadProfile A n c) ≤
      stoppingGammaKernelConstant * levyEnergy (finiteLogCellProfile n c) := by
  let L := stoppingGridBoundary A
  let f := finiteLogCellProfile n c
  let g := actualGeneratorHeadProfile A n c
  obtain ⟨Rf, hf⟩ := exists_finiteLogCellProfile_zero_above n c
  obtain ⟨Rg, hg⟩ := exists_finiteLogCellProfile_zero_above
    (stoppedLogCellLabel A n) (stoppedLogCellHeight A n c)
  obtain ⟨N, hN, hR⟩ := stoppingGrid_exists_padding A (max Rf Rg)
  have hL : StrictMono L := stoppingGridBoundary_strictMono A
  have hw (k : ℕ) : L (k + 1) - L k = stoppingGridWidth A k := by
    dsimp only [L]
    rw [stoppingGridBoundary_succ]
    ring
  have hfirst : intervalMean (L 0) (L 1) f = 0 := by
    apply intervalMean_zero_of_zero
    intro x hx
    have he : L 1 = 0 := by
      dsimp only [L]
      rw [stoppingGridBoundary_initial A (by omega) A.pos, Nat.cast_one, Real.log_one]
    exact finiteLogCellProfile_zero_of_neg n c (by linarith only [hx.2, he])
  have hlast : intervalMean (L (N - 1)) (L N) f = 0 := by
    apply intervalMean_zero_of_zero
    intro x hx
    exact hf x ((le_max_left Rf Rg).trans (hR.le.trans hx.1.le))
  have hleft : L 0 < 0 := by
    dsimp only [L]
    rw [stoppingGridBoundary_zero]
    exact neg_neg_of_pos (Real.log_pos (by norm_num))
  have hright : max Rf Rg < L N := hR.trans_le (hL.monotone (Nat.sub_le N 1))
  apply levyEnergy_padded_grid_average_le L N hN hL
    (fun k => by rw [hw]; exact stoppingGridWidth_le_one A k)
    (fun k => by
      rw [hw k, show k + 2 = (k + 1) + 1 by omega, hw (k + 1)]
      exact stoppingGridWidth_adjacent A k)
    f g (finiteLogCellProfile_bv n c) (finiteLogCellProfile_compact n c)
    (actualGeneratorHeadProfile_bv A n c) (actualGeneratorHeadProfile_compact A n c)
    ?_ ?_ ?_ hfirst hlast
  · intro k _ x hx
    by_cases hk : k = 0
    · subst k
      rw [hfirst]
      have he : L 1 = 0 := by
        dsimp only [L]
        rw [stoppingGridBoundary_initial A (by omega) A.pos, Nat.cast_one, Real.log_one]
      exact finiteLogCellProfile_zero_of_neg _ _ (by linarith only [hx.2, he])
    · obtain ⟨j, a, ha, hja, hl, hu⟩ := stoppingGrid_cell A (by omega : 0 < k)
      change g x = intervalMean (stoppingGridBoundary A k) (stoppingGridBoundary A (k + 1)) f
      change x ∈ Ioo (stoppingGridBoundary A k) (stoppingGridBoundary A (k + 1)) at hx
      rw [hl, hu] at hx ⊢
      exact actualGeneratorHead_eq_intervalMean A n c j a ha hja hx
  · intro y hy
    rcases hy with hy | hy
    · exact finiteLogCellProfile_zero_of_neg n c (hy.trans hleft)
    · exact hf y ((le_max_left Rf Rg).trans (hright.le.trans hy.le))
  · intro y hy
    rcases hy with hy | hy
    · exact finiteLogCellProfile_zero_of_neg _ _ (hy.trans hleft)
    · exact hg y ((le_max_right Rf Rg).trans (hright.le.trans hy.le))

/-- A universal constant for the sum of the actual head and tail Gamma energies. -/
def generatorGammaStabilityConstant : ℝ := 2 + 96 * Real.exp 2

theorem generatorGammaStabilityConstant_pos : 0 < generatorGammaStabilityConstant := by
  unfold generatorGammaStabilityConstant
  positivity

/-- One original Gamma reserve pays both physical pieces, uniformly over every cutoff and horizon. -/
theorem actualGeneratorHead_tail_gamma_le {ι : Type*} [Fintype ι]
    (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) :
    levyEnergy (actualGeneratorHeadProfile A n c) +
      levyEnergy (actualGeneratorTailProfile A n c) ≤
        generatorGammaStabilityConstant * levyEnergy (finiteLogCellProfile n c) := by
  have hh := actualGeneratorHead_gamma_le A n c
  have ht := levyEnergy_sub_le_two_bv (finiteLogCellProfile_bv n c)
    (actualGeneratorHeadProfile_bv A n c) (finiteLogCellProfile_compact n c)
    (actualGeneratorHeadProfile_compact A n c)
  change levyEnergy (actualGeneratorTailProfile A n c) ≤
    2 * levyEnergy (finiteLogCellProfile n c) + 2 * levyEnergy (actualGeneratorHeadProfile A n c) at ht
  dsimp only [stoppingGammaKernelConstant] at hh
  dsimp only [generatorGammaStabilityConstant]
  linarith only [hh, ht]

/-- The same constant applies directly to the original horizon-indexed complete-cell source. -/
theorem actualGeneratorHead_tail_gamma_wholeCell (A : ℕ+) (c : ℕ → ℝ) (X : ℕ) :
    levyEnergy (actualGeneratorHeadProfile A (wholeCellSourceLabel X) (fun i => c i.1)) +
      levyEnergy (actualGeneratorTailProfile A (wholeCellSourceLabel X) (fun i => c i.1)) ≤
        generatorGammaStabilityConstant * levyEnergy (wholeCellProfile c X) := by
  simpa only [finiteLogCellProfile_wholeCell] using
    actualGeneratorHead_tail_gamma_le A (wholeCellSourceLabel X) (fun i => c i.1)

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.actualGeneratorHead_gamma_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.actualGeneratorHead_tail_gamma_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.actualGeneratorHead_tail_gamma_wholeCell
