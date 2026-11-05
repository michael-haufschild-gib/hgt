import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheWindowIndex
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.InwardDilationPreservesTheWindowIndex

/-!
# The window index counts critical lengths

The negative index of Weil's form is a left-continuous, integer-valued function of
window length. Its critical lengths are the endpoints of the sublevel sets. A negative
square is counted strictly after its critical length, with repeated lengths recording
the jump multiplicity. Only finitely many critical lengths lie in any bounded interval.
-/

noncomputable section

open Set Filter Topology Zeta23

namespace GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri SquareRootThreshold

/-- The index at a positive length is exhausted by strictly shorter windows. -/
theorem windowIndex_eq_iSup_lt {A : ℝ} (hA : 0 < A) :
    windowIndex A = ⨆ (B : ℝ) (_ : 0 < B ∧ B < A), windowIndex B := by
  refine le_antisymm ?_ (iSup_le fun B => iSup_le fun hB => windowIndex_mono hB.2.le)
  rw [windowIndex, hodgeDefectAt_eq_iSup_lt temperedConfig_zetaZeroConfig (by linarith)]
  refine iSup_le fun b => iSup_le fun hb => ?_
  have heq : hodgeDefectAt zetaZeroConfig b = windowIndex (2 * b) := by
    simp only [windowIndex, mul_div_cancel_left₀ b two_ne_zero]
  rw [heq]
  exact le_iSup₂_of_le (2 * b) ⟨by linarith [hb.1], by linarith [hb.2]⟩ le_rfl

/-- The endpoint of the lengths carrying at most `n` negative squares. -/
def windowIndexCriticalLength (n : ℕ) : EReal :=
  sSup {x : EReal | ∃ A : ℝ, x = A ∧ windowIndex A ≤ n}

theorem windowIndexCriticalLength_mono : Monotone windowIndexCriticalLength := by
  intro n m hnm
  apply sSup_le_sSup
  rintro x ⟨A, rfl, hA⟩
  exact ⟨A, rfl, hA.trans (ENat.coe_le_coe.mpr hnm)⟩

/-- The endpoint itself still has index at most `n`. -/
theorem le_windowIndexCriticalLength_iff (A : ℝ) (n : ℕ) :
    (A : EReal) ≤ windowIndexCriticalLength n ↔ windowIndex A ≤ n := by
  constructor
  · intro hA
    by_cases hpos : 0 < A
    · rw [windowIndex_eq_iSup_lt hpos]
      refine iSup_le fun B => iSup_le fun hB => ?_
      have hlt : (B : EReal) < windowIndexCriticalLength n :=
        (EReal.coe_lt_coe_iff.mpr hB.2).trans_le hA
      obtain ⟨x, ⟨C, rfl, hC⟩, hBC⟩ := lt_sSup_iff.mp hlt
      exact (windowIndex_mono (EReal.coe_lt_coe_iff.mp hBC).le).trans hC
    · rw [windowIndex_eq_zero_of_le (by linarith)]
      exact zero_le
  · intro hA
    exact le_sSup ⟨A, rfl, hA⟩

/-- Crossing a critical length is exactly the appearance of its negative square. -/
theorem windowIndexCriticalLength_lt_iff (A : ℝ) (n : ℕ) :
    windowIndexCriticalLength n < (A : EReal) ↔ (n : ℕ∞) < windowIndex A := by
  rw [← not_le, le_windowIndexCriticalLength_iff, not_le]

/-- Critical lengths already crossed form an initial segment of the natural numbers. -/
theorem criticalLengths_below_eq_range (A : ℝ) :
    {n : ℕ | windowIndexCriticalLength n < (A : EReal)} =
      (Finset.range (windowIndex A).toNat : Set ℕ) := by
  ext n
  simp only [mem_setOf_eq, windowIndexCriticalLength_lt_iff,
    Finset.mem_coe, Finset.mem_range]
  simpa only [ENat.coe_toNat (ne_of_lt (windowIndex_lt_top A))] using
    (ENat.coe_lt_coe : (n : ℕ∞) < ((windowIndex A).toNat : ℕ∞) ↔
      n < (windowIndex A).toNat)

/-- The window index counts critical lengths strictly below its length, with multiplicity. -/
theorem windowIndex_eq_encard_criticalLengths (A : ℝ) :
    windowIndex A = {n : ℕ | windowIndexCriticalLength n < (A : EReal)}.encard := by
  rw [criticalLengths_below_eq_range, Set.encard_coe_eq_coe_finsetCard, Finset.card_range,
    ENat.coe_toNat (ne_of_lt (windowIndex_lt_top A))]

/-- Even repeated critical lengths are locally finite. -/
theorem finite_criticalLengths_le (A : ℝ) :
    {n : ℕ | windowIndexCriticalLength n ≤ (A : EReal)}.Finite := by
  have hfinite : {n : ℕ | windowIndexCriticalLength n < ((A + 1 : ℝ) : EReal)}.Finite := by
    rw [criticalLengths_below_eq_range]
    exact Finset.finite_toSet _
  apply hfinite.subset
  intro n hn
  exact hn.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith : A < A + 1))

/-- A critical length is infinite exactly when there are too few right zeros to reach it. -/
theorem windowIndexCriticalLength_eq_top_iff (n : ℕ) :
    windowIndexCriticalLength n = ⊤ ↔
      (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard ≤ n := by
  rw [← iSup_windowIndex]
  constructor
  · intro h
    refine iSup_le fun A => (le_windowIndexCriticalLength_iff A n).mp ?_
    rw [h]
    exact le_top
  · intro h
    rw [EReal.eq_top_iff_forall_lt]
    intro A
    have hle := (le_windowIndexCriticalLength_iff (A + 1) n).mpr
      ((le_iSup windowIndex (A + 1)).trans h)
    exact (EReal.coe_lt_coe_iff.mpr (by linarith : A < A + 1)).trans_le hle

/-- The finite critical lengths enumerate exactly the available negative squares. -/
theorem windowIndexCriticalLength_lt_top_iff (n : ℕ) :
    windowIndexCriticalLength n < ⊤ ↔
      (n : ℕ∞) < (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard := by
  rw [lt_top_iff_ne_top]
  change (¬ windowIndexCriticalLength n = ⊤) ↔ _
  rw [windowIndexCriticalLength_eq_top_iff, not_le]

#print axioms ArithmeticCastelnuovoSeveri.tendsto_W_indexInwardScale
#print axioms ArithmeticCastelnuovoSeveri.hodgeDefectAt_eq_iSup_lt
#print axioms windowIndex_eq_iSup_lt
#print axioms le_windowIndexCriticalLength_iff
#print axioms windowIndex_eq_encard_criticalLengths
#print axioms finite_criticalLengths_le
#print axioms windowIndexCriticalLength_eq_top_iff
#print axioms windowIndexCriticalLength_lt_top_iff

end GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
