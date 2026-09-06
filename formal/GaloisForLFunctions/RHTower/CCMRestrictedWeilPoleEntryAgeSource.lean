import GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimeAgeBalance

/-!
# Full Weil source balance from entry tangents and common aging

The actual odd source is its smooth Gamma–polar part plus positive entry
tangents minus the shared age loss. The even source subtracts both its entry
tangent magnitudes and that same loss. All three finite budgets are
nonnegative, and the shared loss is strictly positive after the first entry.
-/

open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower

/-- Sum of positive odd entry tangents at the actual aperture. -/
def ccmWeilOddEntryTangentBudget (a : SuzukiPositiveAperture) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,ccmWeilOddPrimeEntrySlope n*(a.1-Real.log n/2)

/-- Sum of even entry-tangent magnitudes at the actual aperture. -/
def ccmWeilEvenEntryTangentBudget (a : SuzukiPositiveAperture) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,ccmWeilEvenPrimeEntrySlopeMagnitude n*(a.1-Real.log n/2)

/-- The identical accumulated age loss in the two actual parity energies. -/
def ccmWeilPrimeAgeBudget (a : SuzukiPositiveAperture) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,ccmWeilPrimeAgeLoss n a.1

private theorem entry_le (a : SuzukiPositiveAperture) {n : ℕ}
    (hn : n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊) : Real.log n/2 ≤ a.1 := by
  have h2 := (Finset.mem_Icc.mp hn).1
  have hc := (Finset.mem_Icc.mp hn).2
  have h := (Real.log_le_iff_le_exp (show 0 < (n:ℝ) by exact_mod_cast (by omega : 0 < n))).mpr
    ((show (n:ℝ) ≤ (⌊Real.exp (2*a.1)⌋₊:ℝ) by exact_mod_cast hc).trans (Nat.floor_le (Real.exp_pos _).le))
  linarith

/-- All three literal finite budgets are nonnegative. -/
theorem ccmWeilEntryAgeBudgets_nonneg (a : SuzukiPositiveAperture) :
    0 ≤ ccmWeilOddEntryTangentBudget a ∧ 0 ≤ ccmWeilEvenEntryTangentBudget a ∧
      0 ≤ ccmWeilPrimeAgeBudget a := by
  refine ⟨?_,?_,?_⟩
  · apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (ccmWeilPrimeEntrySlopes_nonneg n).1 (sub_nonneg.mpr (entry_le a hn))
  · apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (ccmWeilPrimeEntrySlopes_nonneg n).2 (sub_nonneg.mpr (entry_le a hn))
  · apply Finset.sum_nonneg
    intro n hn
    exact ccmWeilPrimeAgeLoss_nonneg n (entry_le a hn)

/-- Actual odd source: exact smooth Gamma–polar part plus entry tangents minus the shared loss. -/
theorem ccmWeilOddPole_eq_entry_age_balance (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) =
      2*(ccmWeilPoleDiagonalSmooth a.1-ccmWeilPoleCrossSmooth a.1)+
        ccmWeilOddEntryTangentBudget a-ccmWeilPrimeAgeBudget a := by
  have hsum : (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
      2*(-ccmWeilPolePrimeDiagonalAtom n a.1+ccmWeilPolePrimeCrossAtom n a.1)) =
      ccmWeilOddEntryTangentBudget a-ccmWeilPrimeAgeBudget a := by
    unfold ccmWeilOddEntryTangentBudget ccmWeilPrimeAgeBudget
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n hn => ccmWeilOddPrimeAtom_eq_tangent_sub_age n (Finset.mem_Icc.mp hn).1 a.1
  have hsplit : (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
      2*(-ccmWeilPolePrimeDiagonalAtom n a.1+ccmWeilPolePrimeCrossAtom n a.1)) =
      -2*(∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,ccmWeilPolePrimeDiagonalAtom n a.1)+
      2*(∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,ccmWeilPolePrimeCrossAtom n a.1) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [ccmWeilPoleCompression_parity_energy a (Or.inr rfl),
    ccmWeilPoleDiagonal_eq_chamber_of_floor_eq a a rfl,
    ccmWeilPoleCross_eq_chamber_of_floor_eq a a rfl,
    ccmWeilPoleChamberDiagonal_eq_sum_atoms,ccmWeilPoleChamberCross_eq_sum_atoms]
  linarith

/-- Actual even source: exact smooth Gamma–polar part minus entry tangents and the same loss. -/
theorem ccmWeilEvenPole_eq_entry_age_balance (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) =
      2*(ccmWeilPoleDiagonalSmooth a.1+ccmWeilPoleCrossSmooth a.1)-
        ccmWeilEvenEntryTangentBudget a-ccmWeilPrimeAgeBudget a := by
  have hsum : (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
      2*(-ccmWeilPolePrimeDiagonalAtom n a.1-ccmWeilPolePrimeCrossAtom n a.1)) =
      -ccmWeilEvenEntryTangentBudget a-ccmWeilPrimeAgeBudget a := by
    unfold ccmWeilEvenEntryTangentBudget ccmWeilPrimeAgeBudget
    rw [← Finset.sum_neg_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simpa only [neg_mul] using ccmWeilEvenPrimeAtom_eq_tangent_sub_age n (Finset.mem_Icc.mp hn).1 a.1
  have hsplit : (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
      2*(-ccmWeilPolePrimeDiagonalAtom n a.1-ccmWeilPolePrimeCrossAtom n a.1)) =
      -2*(∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,ccmWeilPolePrimeDiagonalAtom n a.1)-
      2*(∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,ccmWeilPolePrimeCrossAtom n a.1) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [ccmWeilPoleCompression_parity_energy a (Or.inl rfl),
    ccmWeilPoleDiagonal_eq_chamber_of_floor_eq a a rfl,
    ccmWeilPoleCross_eq_chamber_of_floor_eq a a rfl,
    ccmWeilPoleChamberDiagonal_eq_sum_atoms,ccmWeilPoleChamberCross_eq_sum_atoms]
  linarith

/-- After the first prime enters, omitting aging strictly overestimates both actual energies. -/
theorem ccmWeilPrimeAgeBudget_pos (a : SuzukiPositiveAperture) (ha : Real.log 2/2 < a.1) :
    0 < ccmWeilPrimeAgeBudget a := by
  have h2 : 2 ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊ := by
    apply Finset.mem_Icc.mpr
    refine ⟨le_rfl,Nat.le_floor ?_⟩
    exact (Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 2)).mp
      (show Real.log (2:ℝ) ≤ 2*a.1 by linarith)
  apply Finset.sum_pos'
  · intro n hn
    exact ccmWeilPrimeAgeLoss_nonneg n (entry_le a hn)
  · exact ⟨2,h2,ccmWeilPrimeAgeLoss_pos Nat.prime_two.isPrimePow ha⟩

/-- Exact simultaneous prime–Gamma comparison required by the two actual parity tests. -/
theorem ccmWeilParity_nonneg_iff_entry_age_budgets (a : SuzukiPositiveAperture) :
    (0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) ∧
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1))) ↔
    (ccmWeilEvenEntryTangentBudget a+ccmWeilPrimeAgeBudget a ≤
        2*(ccmWeilPoleDiagonalSmooth a.1+ccmWeilPoleCrossSmooth a.1) ∧
      ccmWeilPrimeAgeBudget a ≤ 2*(ccmWeilPoleDiagonalSmooth a.1-ccmWeilPoleCrossSmooth a.1)+
        ccmWeilOddEntryTangentBudget a) := by
  rw [ccmWeilOddPole_eq_entry_age_balance,ccmWeilEvenPole_eq_entry_age_balance]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

end RHTower
