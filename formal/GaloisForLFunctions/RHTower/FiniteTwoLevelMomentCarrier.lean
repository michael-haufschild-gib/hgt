import GaloisForLFunctions.RHTower.XiPrimeMarkedCofinalTriangleNuclearCarrier

/-!
# Exact finite two-level moment carrier

For positive targets `E,F` in the strict finite atomic cone

`E² / N < F ≤ E²`,

one large nonnegative atom and `N-1` equal nonnegative atoms have first moment `E` and second
moment `F`.  This is the exact algebraic carrier needed to admit both quadratic and quartic
source traces after a small cofinite operator reserve has been fixed.

No source moment is evaluated.  The construction is symbolic and unconditional.
-/

namespace RHTower

noncomputable section

/-- Separation between the large atom and the `N-1` equal small atoms. -/
def twoLevelDeviation (E F : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (((N : ℝ) * F - E ^ 2) / ((N : ℝ) - 1))

/-- The unique large atom in the two-level carrier. -/
def twoLevelLarge (E F : ℝ) (N : ℕ) : ℝ :=
  (E + ((N : ℝ) - 1) * twoLevelDeviation E F N) / N

/-- Each of the `N-1` equal small atoms in the two-level carrier. -/
def twoLevelSmall (E F : ℝ) (N : ℕ) : ℝ :=
  (E - twoLevelDeviation E F N) / N

theorem twoLevelDeviation_sq
    {E F : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) :
    twoLevelDeviation E F N ^ 2 =
      ((N : ℝ) * F - E ^ 2) / ((N : ℝ) - 1) := by
  rw [twoLevelDeviation]
  apply Real.sq_sqrt
  have hNr : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hNr1 : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by
    linarith
  rw [div_nonneg_iff]
  left
  constructor
  · rw [div_lt_iff₀ hNr] at hlow
    linarith
  · exact hNm1.le

theorem twoLevelDeviation_nonneg (E F : ℝ) (N : ℕ) :
    0 ≤ twoLevelDeviation E F N :=
  Real.sqrt_nonneg _

theorem twoLevelDeviation_le
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2) :
    twoLevelDeviation E F N ≤ E := by
  have hsq := twoLevelDeviation_sq hN hlow
  have hNr1 : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by
    linarith
  have hdev : 0 ≤ twoLevelDeviation E F N :=
    twoLevelDeviation_nonneg E F N
  have hbound : twoLevelDeviation E F N ^ 2 ≤ E ^ 2 := by
    rw [hsq, div_le_iff₀ hNm1]
    nlinarith
  nlinarith

theorem twoLevelLarge_pos
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N) :
    0 < twoLevelLarge E F N := by
  rw [twoLevelLarge]
  have hNr : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  exact div_pos
    (add_pos_of_pos_of_nonneg hE
      (mul_nonneg (by
          have hNr1 : (1 : ℝ) ≤ N := by
            exact_mod_cast (show 1 ≤ N by omega)
          linarith)
        (twoLevelDeviation_nonneg E F N)))
    hNr

theorem twoLevelSmall_nonneg
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2) :
    0 ≤ twoLevelSmall E F N := by
  rw [twoLevelSmall]
  exact div_nonneg
    (sub_nonneg.mpr (twoLevelDeviation_le hE hN hlow hhigh))
    (by exact_mod_cast (show 0 ≤ N by omega))

/-- Exact first moment: one large atom plus `N-1` small atoms. -/
theorem twoLevel_firstMoment
    {E F : ℝ} {N : ℕ} (hN : 2 ≤ N) :
    twoLevelLarge E F N +
        ((N : ℝ) - 1) * twoLevelSmall E F N = E := by
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  rw [twoLevelLarge, twoLevelSmall]
  field_simp [hN0]
  ring

/-- Exact second moment: squares of the same finite atomic carrier. -/
theorem twoLevel_secondMoment
    {E F : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) :
    twoLevelLarge E F N ^ 2 +
        ((N : ℝ) - 1) * twoLevelSmall E F N ^ 2 = F := by
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  have hNm1 : (N : ℝ) - 1 ≠ 0 := by
    exact_mod_cast (show (N : ℤ) - 1 ≠ 0 by omega)
  have hsq := twoLevelDeviation_sq hN hlow
  rw [twoLevelLarge, twoLevelSmall]
  field_simp [hN0, hNm1] at hsq ⊢
  nlinarith

end

end RHTower
