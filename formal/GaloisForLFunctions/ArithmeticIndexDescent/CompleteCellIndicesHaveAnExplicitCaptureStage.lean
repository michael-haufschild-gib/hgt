import GaloisForLFunctions.ArithmeticIndexDescent.TheCompleteCellsCaptureEveryFiniteIndex
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.QuantitativeCompleteWeilSourceTransfer
import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.FiniteWeilFamiliesHaveExplicitIndexHorizonTests

/-! # An explicit capture stage for complete-cell indices

Canonical source bounds give every Gram entry an explicit `N^(-1/2)` rate.
The actual negative spectral compression then supplies a quadratic capture
stage, with no assumed convergence modulus or arithmetic error estimate.
-/

noncomputable section
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open MeasureTheory Matrix Finset Zeta23

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticCastelnuovoSeveri.LogCells
open HTGeometry SpacingScaleHarmonicAnalysis EffectiveArithmeticHodgeTheory

/-- Explicit entry constants obtained by polarization of the full source rate. -/
def completeCellEntryRate {n : ℕ} (f : Fin n → realTests) (R : ℝ) (B : ℕ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  (canonicalCompleteCellRate (fun u => (f i).1 u + (f j).1 u) R B +
    canonicalCompleteCellRate (fun u => (f i).1 u - (f j).1 u) R B) / 4

theorem completeCellEntryRate_nonneg {n : ℕ} (f : Fin n → realTests) (R : ℝ)
    {B : ℕ} (hB : 1 ≤ B) (i j : Fin n) : 0 ≤ completeCellEntryRate f R B i j :=
  div_nonneg (add_nonneg (canonicalCompleteCellRate_nonneg _ R hB)
    (canonicalCompleteCellRate_nonneg _ R hB)) (by norm_num)

private theorem abs_polarized_difference_le (a b c d : ℝ) :
    |(a - b) / 4 - (c - d) / 4| ≤ (|a - c| + |b - d|) / 4 := by
  calc _ = |((a - c) - (b - d)) / 4| := by congr 1; ring
    _ = |(a - c) - (b - d)| / 4 := by rw [abs_div]; norm_num
    _ ≤ _ := div_le_div_of_nonneg_right
      (by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (a - c) 0 (b - d))
      (by norm_num)

/-- Every entry of the literal complete-cell matrix has its source-derived rate. -/
theorem norm_completeCellSourceGram_sub_le {n : ℕ} (f : Fin n → realTests)
    (R : ℝ) {N B : ℕ} (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ i u, u ≤ -R ∨ Real.log B - R ≤ u → (f i).1 u = 0)
    (i j : Fin n) :
    ‖completeCellSourceGram f R N B i j - complexWeilMixed f f i j‖ ≤
      completeCellEntryRate f R B i j / Real.sqrt N := by
  have hplus := abs_completeCellWeil_sub_le_canonical
    (f := fun u => (f i).1 u + (f j).1 u) ((f i).2.1.add (f j).2.1)
    ((f i).2.2.add (f j).2.2) R hN hB
    (fun u hu => by rw [hs i u hu, hs j u hu, add_zero])
  have hminus := abs_completeCellWeil_sub_le_canonical
    (f := fun u => (f i).1 u - (f j).1 u) ((f i).2.1.sub (f j).2.1)
    ((f i).2.2.sub (f j).2.2) R hN hB
    (fun u hu => by rw [hs i u hu, hs j u hu, sub_self])
  simp only [completeCellSourceGram, complexWeilMixed, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  rw [← completeCell_limit_pair (f i) (f j)]
  unfold completeCellGram
  calc _ ≤ (|completeCellWeil (fun u => (f i).1 u + (f j).1 u) R N B -
          weilQuad (fun u => (f i).1 u + (f j).1 u)| +
        |completeCellWeil (fun u => (f i).1 u - (f j).1 u) R N B -
          weilQuad (fun u => (f i).1 u - (f j).1 u)|) / 4 :=
      abs_polarized_difference_le _ _ _ _
    _ ≤ (canonicalCompleteCellRate (fun u => (f i).1 u + (f j).1 u) R B / Real.sqrt N +
        canonicalCompleteCellRate (fun u => (f i).1 u - (f j).1 u) R B / Real.sqrt N) / 4 :=
      div_le_div_of_nonneg_right (add_le_add hplus hminus) (by norm_num)
    _ = completeCellEntryRate f R B i j / Real.sqrt N := by
      unfold completeCellEntryRate; ring

/-- Total entry error after the actual negative compression. -/
def completeCellCompressionRate {n r : ℕ} (f : Fin n → realTests) (R : ℝ) (B : ℕ)
    (S : Matrix (Fin n) (Fin r) ℂ) : ℝ :=
  ∑ i, ∑ j, compressedEntryBudget S (completeCellEntryRate f R B) i j

private theorem compressedEntryBudget_nonneg {n r : ℕ} (S : Matrix (Fin n) (Fin r) ℂ)
    (E : Matrix (Fin n) (Fin n) ℝ) (hE : ∀ a b, 0 ≤ E a b) (i j : Fin r) :
    0 ≤ compressedEntryBudget S E i j :=
  sum_nonneg fun a _ => sum_nonneg fun b _ =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (hE a b)) (norm_nonneg _)

theorem completeCellCompressionRate_nonneg {n r : ℕ} (f : Fin n → realTests)
    (R : ℝ) {B : ℕ} (hB : 1 ≤ B) (S : Matrix (Fin n) (Fin r) ℂ) :
    0 ≤ completeCellCompressionRate f R B S :=
  sum_nonneg fun i _ => sum_nonneg fun j _ =>
    compressedEntryBudget_nonneg S _ (completeCellEntryRate_nonneg f R hB) i j

/-- Quadratic stage dictated by the full source error and the negative spectral margin. -/
def completeCellCaptureStage {n r : ℕ} (f : Fin n → realTests) (R : ℝ) (B : ℕ)
    (S : Matrix (Fin n) (Fin r) ℂ) (δ : ℝ) : ℕ :=
  1 + ⌈(2 * ((r : ℝ) ^ 2 + 1) * completeCellCompressionRate f R B S / δ) ^ 2⌉₊

private theorem error_le_margin_at_captureStage {n r : ℕ} (f : Fin n → realTests)
    (R : ℝ) {B : ℕ} (hB : 1 ≤ B) (S : Matrix (Fin n) (Fin r) ℂ)
    {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : completeCellCaptureStage f R B S δ ≤ N) :
    completeCellCompressionRate f R B S / Real.sqrt N ≤ δ / (2 * ((r : ℝ) ^ 2 + 1)) := by
  have hN1 : 1 ≤ N := by unfold completeCellCaptureStage at hN; omega
  have hNs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN1)
  have hT := completeCellCompressionRate_nonneg f R hB S
  have hq : 0 ≤ 2 * ((r : ℝ) ^ 2 + 1) * completeCellCompressionRate f R B S / δ := by positivity
  have hceil : (2 * ((r : ℝ) ^ 2 + 1) * completeCellCompressionRate f R B S / δ) ^ 2 ≤
      (N : ℝ) := by
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (show ⌈(2 * ((r : ℝ) ^ 2 + 1) *
      completeCellCompressionRate f R B S / δ) ^ 2⌉₊ ≤ N by
        unfold completeCellCaptureStage at hN; omega)
  have hroot : 2 * ((r : ℝ) ^ 2 + 1) * completeCellCompressionRate f R B S / δ ≤
      Real.sqrt N := by
    apply (sq_le_sq₀ hq hNs.le).mp
    simpa only [Real.sq_sqrt (Nat.cast_nonneg N)] using hceil
  have hprod := (div_le_iff₀ hδ).mp hroot
  apply (div_le_div_iff₀ hNs (by positivity : (0 : ℝ) < 2 * ((r : ℝ) ^ 2 + 1))).mpr
  convert hprod using 1 <;> ring

/-- At the displayed stage, the literal cell matrix retains the given negative compression. -/
theorem completeCell_index_capture_at_stage {n r : ℕ} (f : Fin n → realTests)
    (R : ℝ) {B : ℕ} (hB : 1 ≤ B)
    (hs : ∀ i u, u ≤ -R ∨ Real.log B - R ≤ u → (f i).1 u = 0)
    (S : Matrix (Fin n) (Fin r) ℂ) (c : Fin r → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ i, c i ≤ -δ)
    (hdiag : Sᴴ * complexWeilMixed f f * S = diagonal (fun i => (c i : ℂ)))
    {N : ℕ} (hN : completeCellCaptureStage f R B S δ ≤ N) :
    r ≤ hermNegIndex (completeCellSourceGram f R N B) := by
  have hN1 : 1 ≤ N := by unfold completeCellCaptureStage at hN; omega
  apply le_index_of_compressed_entry_test (complexWeilMixed f f) _ S c hδ hc hdiag
    (fun a b => completeCellEntryRate f R B a b / Real.sqrt N)
    (norm_completeCellSourceGram_sub_le f R hN1 hB hs)
  intro i j
  have hE (a b : Fin r) :=
    compressedEntryBudget_nonneg S _ (completeCellEntryRate_nonneg f R hB) a b
  have htotal : compressedEntryBudget S (completeCellEntryRate f R B) i j ≤
      completeCellCompressionRate f R B S := by
    exact (single_le_sum (fun b _ => hE i b) (mem_univ j)).trans
      (single_le_sum (fun a _ => sum_nonneg fun b _ => hE a b) (mem_univ i))
  have hscale : compressedEntryBudget S
      (fun a b => completeCellEntryRate f R B a b / Real.sqrt N) i j =
      compressedEntryBudget S (completeCellEntryRate f R B) i j / Real.sqrt N := by
    simp only [compressedEntryBudget, sum_div]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    ring
  rw [hscale]
  exact (div_le_div_of_nonneg_right htotal (Real.sqrt_nonneg N)).trans
    (error_le_margin_at_captureStage f R hB S hδ hN)

/-- Every compact `C²` family supplies the window and spectral margin of an explicit
capture stage. No analytic rate or convergence modulus is assumed. -/
theorem exists_completeCell_explicit_index_capture {n : ℕ} (f : Fin n → realTests) :
    ∃ (R : ℝ) (B r : ℕ) (S : Matrix (Fin n) (Fin r) ℂ) (δ : ℝ),
      0 < R ∧ 1 ≤ B ∧ r = hermNegIndex (complexWeilMixed f f) ∧ 0 < δ ∧
      (∀ i u, u ≤ -R ∨ Real.log B - R ≤ u → (f i).1 u = 0) ∧
      (∃ c : Fin r → ℝ, (∀ i, c i ≤ -δ) ∧
        Sᴴ * complexWeilMixed f f * S = diagonal (fun i => (c i : ℂ))) ∧
      ∀ N : ℕ, completeCellCaptureStage f R B S δ ≤ N →
        hermNegIndex (complexWeilMixed f f) ≤ hermNegIndex (completeCellSourceGram f R N B) := by
  obtain ⟨R, hR, B, hB, hs⟩ := exists_common_logCell_window (fun i => (f i).1)
    (fun i => (f i).2.1) (fun i => (f i).2.2)
  obtain ⟨r, S, c, δ, hr, hδ, hc, hdiag⟩ := exists_complete_negative_compression
    (complexWeilMixed f f) (complexWeilMixed_isHermitian f)
  refine ⟨R, B, r, S, δ, hR, hB, hr, hδ, hs, ⟨c, hc, hdiag⟩, fun N hN => ?_⟩
  rw [← hr]
  exact completeCell_index_capture_at_stage f R hB hs S c hδ hc hdiag hN

/-- The same explicit stage captures the index of the original prime–Gamma–pole Gram. -/
theorem exists_completeCell_explicit_weilGram_capture {n : ℕ} (f : Fin n → realTests) :
    ∃ (R : ℝ) (B r : ℕ) (S : Matrix (Fin n) (Fin r) ℂ) (δ : ℝ),
      0 < R ∧ 1 ≤ B ∧
      r = hermNegIndex (weilGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
        (fun i => cx (f i).1)) ∧ 0 < δ ∧
      ∀ N : ℕ, completeCellCaptureStage f R B S δ ≤ N →
        r ≤ hermNegIndex (completeCellSourceGram f R N B) := by
  obtain ⟨R, B, r, S, δ, hR, hB, hr, hδ, _, _, hcapture⟩ :=
    exists_completeCell_explicit_index_capture f
  refine ⟨R, B, r, S, δ, hR, hB, ?_, hδ, fun N hN => ?_⟩
  · simpa only [complexWeilMixed_eq_weilGram] using hr
  · rw [hr]
    exact hcapture N hN

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.norm_completeCellSourceGram_sub_le
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.completeCell_index_capture_at_stage
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_completeCell_explicit_index_capture
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_completeCell_explicit_weilGram_capture
