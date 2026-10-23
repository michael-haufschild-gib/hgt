import GaloisForLFunctions.SignedArithmeticEnergyIncidence.BalancedIncidenceIsLocallyPayable
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.FrustrationIsTheLocalGlobalGap

/-!
# Local payment is positivity of the comparison form

A local allocation sees only the sizes `|c_ij|` of the overlap charges.  The **comparison form**
keeps the budgets and replaces every overlap charge by `−|c_ij|`: it is the aligned form with the
same sizes.

* **Characterization** (`locallyPayable_iff_comparison_nonneg`): a form is locally payable iff its
  comparison form is nonnegative.  Allocations of a form and of its comparison form are the same
  shares (`PairAllocation.toComparison`, `PairAllocation.ofComparison`), and the comparison form is
  aligned, so `BalancedIncidenceIsLocallyPayable` applies to it.
* **Domination** (`incidenceEnergy_comparison_abs_le`): `E_comp(|f|) ≤ E_c(f)`; the comparison form
  is the worst sign pattern with the given sizes.  For a balanced form the comparison form *is* a
  switching of the form (`switchCoupling_eq_comparison`), so nothing is lost.
* **The cost of local payment** (`locallyPayable_regularized_iff`): raising every budget by `t`
  makes the form locally payable iff `E_comp(f) ≥ −t Σ f_i²`.  The least such `t` is minus the
  ground energy of the comparison form, while positivity needs only minus the ground energy of the
  form itself: the gap between the two ground energies is the exact price of frustration.  For the
  frustrated triangle (`comparison_triangleCoupling`) the comparison form is the aligned triangle
  `triangleCoupling (−|κ|)`, whose positivity window `|κ| ≤ ½` is the payment window.
-/

open Finset

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The comparison coupling: same budgets, overlap charges `−|c_ij|`. -/
def comparisonCoupling (c : ι → ι → ℝ) : ι → ι → ℝ :=
  fun i j => if i = j then c i i else -|c i j|

omit [Fintype ι] in
theorem IsSymmetricCoupling.comparison {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) :
    IsSymmetricCoupling (comparisonCoupling c) := by
  intro i j
  unfold comparisonCoupling
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), hc i j]

omit [Fintype ι] in
theorem comparisonCoupling_hasNonpositiveOverlaps (c : ι → ι → ℝ) :
    HasNonpositiveOverlaps (comparisonCoupling c) := by
  intro i j hij
  simp only [comparisonCoupling, hij, if_false]
  exact neg_nonpos.mpr (abs_nonneg _)

omit [Fintype ι] in
theorem comparisonCoupling_diag (c : ι → ι → ℝ) (i : ι) : comparisonCoupling c i i = c i i := by
  simp [comparisonCoupling]

omit [Fintype ι] in
theorem comparisonCoupling_sq (c : ι → ι → ℝ) {i j : ι} (hij : i ≠ j) :
    comparisonCoupling c i j ^ 2 = c i j ^ 2 := by
  simp [comparisonCoupling, hij, sq_abs]

/-- Allocations of a form pay its comparison form. -/
def PairAllocation.toComparison {c : ι → ι → ℝ} (A : PairAllocation c) :
    PairAllocation (comparisonCoupling c) where
  share := A.share
  share_nonneg := A.share_nonneg
  pays i j hij := by rw [comparisonCoupling_sq c hij]; exact A.pays i j hij
  within_budget i := by rw [comparisonCoupling_diag]; exact A.within_budget i

/-- Allocations of the comparison form pay the form. -/
def PairAllocation.ofComparison {c : ι → ι → ℝ} (A : PairAllocation (comparisonCoupling c)) :
    PairAllocation c where
  share := A.share
  share_nonneg := A.share_nonneg
  pays i j hij := by rw [← comparisonCoupling_sq c hij]; exact A.pays i j hij
  within_budget i := by rw [← comparisonCoupling_diag c i]; exact A.within_budget i

theorem locallyPayable_comparison_iff {c : ι → ι → ℝ} :
    LocallyPayable (comparisonCoupling c) ↔ LocallyPayable c :=
  ⟨fun ⟨A⟩ => ⟨A.ofComparison⟩, fun ⟨A⟩ => ⟨A.toComparison⟩⟩

/-- **Local payment is positivity of the comparison form.** -/
theorem locallyPayable_iff_comparison_nonneg {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) :
    LocallyPayable c ↔ ∀ f, 0 ≤ incidenceEnergy (comparisonCoupling c) f := by
  rw [← locallyPayable_comparison_iff]
  constructor
  · exact incidenceEnergy_nonneg_of_locallyPayable hc.comparison
  · exact locallyPayable_of_nonneg_of_nonpositiveOverlaps hc.comparison
      (comparisonCoupling_hasNonpositiveOverlaps c)

/-- **The comparison form is the worst sign pattern**: `E_comp(|f|) ≤ E_c(f)`. -/
theorem incidenceEnergy_comparison_abs_le (c : ι → ι → ℝ) (f : ι → ℝ) :
    incidenceEnergy (comparisonCoupling c) (fun i => |f i|) ≤ incidenceEnergy c f := by
  unfold incidenceEnergy
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  by_cases h : i = j
  · subst h
    simp only [comparisonCoupling, if_true]
    rw [mul_assoc, mul_assoc, abs_mul_abs_self]
  · simp only [comparisonCoupling, h, if_false]
    have := neg_abs_le (c i j * f i * f j)
    rw [abs_mul, abs_mul] at this
    linarith

omit [Fintype ι] in
/-- For a balanced form the comparison form is a switching of the form. -/
theorem switchCoupling_eq_comparison {c : ι → ι → ℝ} {s : ι → ℝ} (hs : ∀ i, s i ^ 2 = 1)
    (hz : HasNonpositiveOverlaps (switchCoupling s c)) :
    switchCoupling s c = comparisonCoupling c := by
  funext i j
  by_cases h : i = j
  · subst h
    simp only [switchCoupling, comparisonCoupling, if_true]
    rw [← sq, hs i, one_mul]
  · simp only [comparisonCoupling, h, if_false]
    have hz' := hz i j h
    have habs : |switchCoupling s c i j| = |c i j| := by
      simp only [switchCoupling, abs_mul]
      have h1 : |s i| = 1 := by
        have := hs i; rw [← sq_abs] at this; nlinarith [abs_nonneg (s i)]
      have h2 : |s j| = 1 := by
        have := hs j; rw [← sq_abs] at this; nlinarith [abs_nonneg (s j)]
      rw [h1, h2, one_mul, one_mul]
    rw [← habs, abs_of_nonpos hz', neg_neg]

omit [Fintype ι] in
theorem comparisonCoupling_regularized (c : ι → ι → ℝ) (t : ℝ) :
    comparisonCoupling (regularizedCoupling c t) = regularizedCoupling (comparisonCoupling c) t := by
  funext i j
  by_cases h : i = j
  · subst h; simp [comparisonCoupling, regularizedCoupling]
  · simp [comparisonCoupling, regularizedCoupling, h]

/-- **The cost of local payment.**  Raising every budget by `t` makes the form locally payable iff
the comparison form satisfies `E_comp(f) ≥ −t Σ f_i²`. -/
theorem locallyPayable_regularized_iff {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) (t : ℝ) :
    LocallyPayable (regularizedCoupling c t) ↔
      ∀ f, -(t * ∑ i, f i ^ 2) ≤ incidenceEnergy (comparisonCoupling c) f := by
  rw [locallyPayable_iff_comparison_nonneg (hc.regularized t), comparisonCoupling_regularized]
  constructor
  · intro h f
    have := h f
    rw [incidenceEnergy_regularized] at this
    linarith
  · intro h f
    rw [incidenceEnergy_regularized]
    linarith [h f]

/-- The comparison form of the frustrated triangle is the aligned triangle. -/
theorem comparison_triangleCoupling (κ : ℝ) :
    comparisonCoupling (triangleCoupling κ) = triangleCoupling (-|κ|) := by
  funext i j
  by_cases h : i = j
  · subst h; simp [comparisonCoupling, triangleCoupling]
  · simp [comparisonCoupling, triangleCoupling, h]

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
