import GaloisForLFunctions.ArithmeticIndexDescent.FiniteGramDescent
import GaloisForLFunctions.ArithmeticIndexDescent.TheSectionComplementCarriesAllNegativeSquares
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteWeilSourceTransfer

/-!
# Complete arithmetic cells capture every finite Weil index

The common logarithmic cell exhaustion already recovers the full source form,
including every mixed entry of a finite compact C² family. Identifying its
polarization with the original bilinear Weil form transfers all finite negative
squares to sufficiently late complete-cell matrices. No upper index estimate
for those matrices is assumed or produced by this transfer.
-/

open Filter Matrix Topology RHTower Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticCastelnuovoSeveri.LogCells
open SpacingScaleHarmonicAnalysis HTGeometry

/-- The actual complete-cell source entries, retaining complex coefficient testing. -/
def completeCellSourceGram {n : ℕ} (f : Fin n → realTests) (R : ℝ) (N B : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (completeCellGram (f i).1 (f j).1 R N B : ℂ)

private theorem weilQuad_realTest (f : realTests) : weilQuad f.1 = realWeilForm f f := by
  rw [weilQuad_eq_zetaW f.2.1 f.2.2]
  change (zetaZeroConfig.W (cx f.1) (cx f.1)).re = realWeilForm f f
  rw [zeta_W_eq_weilFullFunctional (cx_contDiff f.2.1) (cx_hasCompactSupport f.2.2)]
  rfl

/-- Polarization of the complete real quadratic form is its literal bilinear pairing. -/
theorem completeCell_limit_pair (f g : realTests) :
    (weilQuad (fun u => f.1 u + g.1 u) - weilQuad (fun u => f.1 u - g.1 u)) / 4 =
      realWeilForm f g := by
  change (weilQuad (f + g).1 - weilQuad (f - g).1) / 4 = _
  rw [weilQuad_realTest, weilQuad_realTest]
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  rw [realWeilForm_symm g f]
  ring

/-- On a common source window, every complete-cell entry tends to the literal full Weil entry. -/
theorem tendsto_completeCellSourceGram {n : ℕ} (f : Fin n → realTests)
    (R : ℝ) {B : ℕ} (hB : 1 ≤ B)
    (hs : ∀ i u, u ≤ -R ∨ Real.log B - R ≤ u → (f i).1 u = 0)
    (i j : Fin n) :
    Tendsto (fun N : ℕ => completeCellSourceGram f R (N + 1) B i j) atTop
      (𝓝 (complexWeilMixed f f i j)) := by
  have ht := tendsto_completeCellGram (f i).2.1 (f j).2.1 (f i).2.2 (f j).2.2
    R hB (fun u hu => ⟨hs i u hu, hs j u hu⟩)
  rw [completeCell_limit_pair] at ht
  have hc := (Complex.continuous_ofReal.tendsto (realWeilForm (f i) (f j))).comp ht
  simpa only [Function.comp_def, completeCellSourceGram, complexWeilMixed] using hc

/-- Every finite smooth source family has a single actual cell exhaustion that
eventually carries all of its negative squares. -/
theorem exists_completeCell_index_capture {n : ℕ} (f : Fin n → realTests) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ, 1 ≤ B ∧
      (∀ i j, Tendsto (fun N : ℕ => completeCellSourceGram f R (N + 1) B i j) atTop
        (𝓝 (complexWeilMixed f f i j))) ∧
      ∀ᶠ N : ℕ in atTop,
        hermNegIndex (complexWeilMixed f f) ≤ hermNegIndex (completeCellSourceGram f R (N + 1) B) := by
  obtain ⟨R, hR, B, hB, hs⟩ := exists_common_logCell_window (fun i => (f i).1)
    (fun i => (f i).2.1) (fun i => (f i).2.2)
  have hconv := tendsto_completeCellSourceGram f R hB hs
  exact ⟨R, hR, B, hB, hconv,
    eventually_negIndex_limit_le (fun N : ℕ => completeCellSourceGram f R (N + 1) B)
      (complexWeilMixed f f) hconv⟩

/-- Index capture applies to the original prime–Gamma–pole Weil matrix. -/
theorem exists_completeCell_weilGram_index_capture {n : ℕ} (f : Fin n → realTests) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ, 1 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      hermNegIndex (weilGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
        (fun i => cx (f i).1)) ≤ hermNegIndex (completeCellSourceGram f R (N + 1) B) := by
  obtain ⟨R, hR, B, hB, _, hindex⟩ := exists_completeCell_index_capture f
  rw [complexWeilMixed_eq_weilGram] at hindex
  exact ⟨R, hR, B, hB, hindex⟩

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_completeCell_index_capture
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_completeCell_weilGram_index_capture
