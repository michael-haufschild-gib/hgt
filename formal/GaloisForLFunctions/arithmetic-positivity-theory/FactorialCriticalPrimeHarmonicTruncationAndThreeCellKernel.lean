import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeKernelDensity

/-!
# Harmonic Partial-Sum Monotonicity, `{2, 3, 5}` Positivity Criterion, and Three-Cell Kernel Localization

`FactorialCriticalTranslatedPrimeHarmonicDiagonal` proves that the complete translated
critical prime limit admits the absolutely convergent harmonic diagonal expansion
```
factorialCriticalTranslatedPrimeLimit S b
  = (4 / π^4) ∑' m : ℕ,
      factorialCriticalPrimeHarmonicCharge m * factorialCriticalPatternHarmonicMass S b m / m^4,
```
where `m = 2` is the **sole** harmonic with a negative arithmetic charge (`-2 log 2`),
`m = 1` and multiples of `4` have charge `0`, and every other harmonic `m > 2` (`m % 4 ≠ 0`)
has strictly positive arithmetic charge. However, the sign of the total sum for a general
pattern `(S, b)` was left open.

This module turns that single-negative-harmonic structure into two quantitative tools:

1. **Finite-Truncation Lower Bound & `{2, 3, 5}` Positivity Criterion
   (`factorialCriticalTranslatedPrimeLimit_ge_finset_sum`,
   `factorialCriticalTranslatedPrimeLimit_ge_two_three_five`,
   `factorialCriticalTranslatedPrimeLimit_nonneg_of_three_five`):**
   Because every harmonic term with `m ≠ 2` is nonnegative, any finite partial sum over
   `F : Finset ℕ` containing `2` is an unconditional lower bound for the full series
   `factorialCriticalTranslatedPrimeLimit S b`. Specializing to `F = {2, 3, 5}` yields the
   explicit finite lower bound
   ```
   (4 / π^4) * (log 3 / 27 * M_{S,b}(3) + log 5 / 125 * M_{S,b}(5) - log 2 / 8 * M_{S,b}(2))
     ≤ factorialCriticalTranslatedPrimeLimit S b,
   ```
   and hence a finite two-harmonic sufficient condition for `0 ≤ factorialCriticalTranslatedPrimeLimit S b`.

2. **Three-Cell Physical Kernel Localization (`factorialCriticalPrimeKernelDensity_eq_zero_of_lt_two`,
   `factorialCriticalPrimeKernelDensity_ge_of_five_le`,
   `factorialCriticalPrimeKernelDensity_ge_neg_log_two_div_four`):**
   In physical space `u ∈ ℝ`, `factorialCriticalPrimeKernelDensity u` vanishes identically
   on `(-∞, 2)`, is bounded below by `(log 2 / 150) * factorialCriticalPrimeKernelWeight u ≥ 0`
   on `[5, ∞)`, and satisfies the global lower bound
   `-(log 2 / 4) * factorialCriticalPrimeKernelWeight u ≤ factorialCriticalPrimeKernelDensity u`
   for all `u ≥ 0`. Thus the negative support of the physical prime kernel is strictly
   confined to the three-unit window `[2, 5)`.
-/

open MeasureTheory Set Filter Finset
open scoped BigOperators Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositivityTheory

set_option autoImplicit false

/-! ## 1. Harmonic Partial-Sum Monotonicity Away from `m = 2` -/

/-- The `m`-th harmonic diagonal term of the translated critical prime limit. -/
def factorialCriticalPrimeHarmonicTerm (S : Finset ℕ) (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  factorialCriticalPrimeHarmonicCharge m *
    factorialCriticalPatternHarmonicMass S b m / (m : ℝ) ^ 4

/-- Every harmonic diagonal term with `m ≠ 2` is nonnegative. -/
theorem factorialCriticalPrimeHarmonicTerm_nonneg_of_ne_two
    (S : Finset ℕ) (b : ℕ → ℝ) {m : ℕ} (hm : m ≠ 2) :
    0 ≤ factorialCriticalPrimeHarmonicTerm S b m := by
  unfold factorialCriticalPrimeHarmonicTerm
  have hA : 0 ≤ factorialCriticalPrimeHarmonicCharge m :=
    le_of_not_gt fun h => hm ((factorialCriticalPrimeHarmonicCharge_sign m).1.mp h)
  exact div_nonneg (mul_nonneg hA (factorialCriticalPatternHarmonicMass_nonneg S b m))
    (by positivity)

/-- Summability of the signed harmonic diagonal series. -/
theorem summable_factorialCriticalPrimeHarmonicTerm (S : Finset ℕ) (b : ℕ → ℝ) :
    Summable (factorialCriticalPrimeHarmonicTerm S b) :=
  (summable_factorialCriticalTranslatedPrimeHarmonicDiagonal S b).of_abs

/-- **Finite-Truncation Lower Bound:**
For any finite set of harmonics `F : Finset ℕ` with `2 ∈ F`, the finite partial sum over `F`
bounds the full infinite harmonic series from below. -/
theorem sum_le_tsum_factorialCriticalPrimeHarmonicTerm
    (S : Finset ℕ) (b : ℕ → ℝ) (F : Finset ℕ) (h2 : 2 ∈ F) :
    ∑ m ∈ F, factorialCriticalPrimeHarmonicTerm S b m ≤
      ∑' m : ℕ, factorialCriticalPrimeHarmonicTerm S b m := by
  have hsum := summable_factorialCriticalPrimeHarmonicTerm S b
  rw [← Finset.add_sum_erase F (factorialCriticalPrimeHarmonicTerm S b) h2,
    hsum.tsum_eq_add_tsum_ite 2]
  have hite_nonneg : ∀ m : ℕ,
      0 ≤ (if m = 2 then 0 else factorialCriticalPrimeHarmonicTerm S b m) := by
    intro m
    split_ifs with hm
    · exact le_rfl
    · exact factorialCriticalPrimeHarmonicTerm_nonneg_of_ne_two S b hm
  have hite_sum : Summable (fun m : ℕ =>
      if m = 2 then 0 else factorialCriticalPrimeHarmonicTerm S b m) :=
    Summable.of_nonneg_of_le hite_nonneg
      (fun m => by
        split_ifs
        · exact abs_nonneg _
        · exact le_abs_self _)
      (summable_factorialCriticalTranslatedPrimeHarmonicDiagonal S b)
  have hsub : ∑ m ∈ F.erase 2, factorialCriticalPrimeHarmonicTerm S b m =
      ∑ m ∈ F.erase 2, (if m = 2 then 0 else factorialCriticalPrimeHarmonicTerm S b m) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [if_neg (Finset.mem_erase.mp hm).1]
  rw [hsub]
  linarith [hite_sum.sum_le_tsum (F.erase 2) (fun m _ => hite_nonneg m)]

/-- **Finite-Truncation Lower Bound for `factorialCriticalTranslatedPrimeLimit`:**
Every finite harmonic set `F` containing `2` gives an unconditional lower bound for
`factorialCriticalTranslatedPrimeLimit S b`. -/
theorem factorialCriticalTranslatedPrimeLimit_ge_finset_sum
    (S : Finset ℕ) (b : ℕ → ℝ) (F : Finset ℕ) (h2 : 2 ∈ F) :
    (4 / Real.pi ^ 4) * ∑ m ∈ F, factorialCriticalPrimeHarmonicTerm S b m ≤
      factorialCriticalTranslatedPrimeLimit S b := by
  rw [factorialCriticalTranslatedPrimeLimit_eq_harmonic_diagonal]
  exact mul_le_mul_of_nonneg_left
    (sum_le_tsum_factorialCriticalPrimeHarmonicTerm S b F h2) (by positivity)

/-! ## 2. Explicit `{2, 3, 5}` Harmonic Lower Bound & Positivity Criterion -/

/-- Explicit evaluation of the `m = 2`, `3`, and `5` harmonic diagonal terms. -/
theorem factorialCriticalPrimeHarmonicTerm_two_three_five (S : Finset ℕ) (b : ℕ → ℝ) :
    factorialCriticalPrimeHarmonicTerm S b 2 =
      -(Real.log 2 / 8) * factorialCriticalPatternHarmonicMass S b 2 ∧
    factorialCriticalPrimeHarmonicTerm S b 3 =
      (Real.log 3 / 27) * factorialCriticalPatternHarmonicMass S b 3 ∧
    factorialCriticalPrimeHarmonicTerm S b 5 =
      (Real.log 5 / 125) * factorialCriticalPatternHarmonicMass S b 5 := by
  have h2 := factorialCriticalPrimeHarmonicCharge_two
  have h3 : factorialCriticalPrimeHarmonicCharge 3 = 3 * Real.log 3 :=
    factorialCriticalPrimeHarmonicCharge_odd_prime (by norm_num) (by norm_num)
  have h5 : factorialCriticalPrimeHarmonicCharge 5 = 5 * Real.log 5 :=
    factorialCriticalPrimeHarmonicCharge_odd_prime (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · unfold factorialCriticalPrimeHarmonicTerm
    rw [h2]
    ring
  · unfold factorialCriticalPrimeHarmonicTerm
    rw [h3]
    ring
  · unfold factorialCriticalPrimeHarmonicTerm
    rw [h5]
    ring

/-- **Explicit `{2, 3, 5}` Lower Bound for the Complete Critical Prime Limit:**
For every finite pattern `(S, b)`, the complete translated prime limit is bounded below by
its `{2, 3, 5}` harmonic truncation. -/
theorem factorialCriticalTranslatedPrimeLimit_ge_two_three_five
    (S : Finset ℕ) (b : ℕ → ℝ) :
    (4 / Real.pi ^ 4) *
        ((Real.log 3 / 27) * factorialCriticalPatternHarmonicMass S b 3 +
          (Real.log 5 / 125) * factorialCriticalPatternHarmonicMass S b 5 -
          (Real.log 2 / 8) * factorialCriticalPatternHarmonicMass S b 2) ≤
      factorialCriticalTranslatedPrimeLimit S b := by
  have h := factorialCriticalTranslatedPrimeLimit_ge_finset_sum S b ({2, 3, 5} : Finset ℕ)
    (by decide)
  obtain ⟨h2, h3, h5⟩ := factorialCriticalPrimeHarmonicTerm_two_three_five S b
  have hsum : ∑ m ∈ ({2, 3, 5} : Finset ℕ), factorialCriticalPrimeHarmonicTerm S b m =
      (Real.log 3 / 27) * factorialCriticalPatternHarmonicMass S b 3 +
        (Real.log 5 / 125) * factorialCriticalPatternHarmonicMass S b 5 -
        (Real.log 2 / 8) * factorialCriticalPatternHarmonicMass S b 2 := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      h2, h3, h5]
    ring
  rw [hsum] at h
  exact h

/-- **Two-Harmonic Positivity Criterion:**
If the third and fifth pattern harmonic masses dominate the second harmonic mass via
`(log 2 / 8) * M_{S,b}(2) ≤ (log 3 / 27) * M_{S,b}(3) + (log 5 / 125) * M_{S,b}(5)`,
then `0 ≤ factorialCriticalTranslatedPrimeLimit S b`. -/
theorem factorialCriticalTranslatedPrimeLimit_nonneg_of_three_five
    (S : Finset ℕ) (b : ℕ → ℝ)
    (hdom : (Real.log 2 / 8) * factorialCriticalPatternHarmonicMass S b 2 ≤
      (Real.log 3 / 27) * factorialCriticalPatternHarmonicMass S b 3 +
        (Real.log 5 / 125) * factorialCriticalPatternHarmonicMass S b 5) :
    0 ≤ factorialCriticalTranslatedPrimeLimit S b := by
  refine le_trans ?_ (factorialCriticalTranslatedPrimeLimit_ge_two_three_five S b)
  exact mul_nonneg (by positivity) (by linarith)

/-! ## 3. Three-Cell Physical Kernel Localization on `ℝ` -/

/-- The physical kernel weight `u^(-2) * (1 - cos(2πu / 12))` is nonnegative for `u ≥ 0`. -/
theorem factorialCriticalPrimeKernelWeight_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ factorialCriticalPrimeKernelWeight u := by
  unfold factorialCriticalPrimeKernelWeight
  exact mul_nonneg (Real.rpow_nonneg hu (-2)) (sub_nonneg.mpr (Real.cos_le_one _))

/-- The physical prime kernel density vanishes identically on `(-∞, 2)`. -/
theorem factorialCriticalPrimeKernelDensity_eq_zero_of_lt_two {u : ℝ} (hu : u < 2) :
    factorialCriticalPrimeKernelDensity u = 0 := by
  unfold factorialCriticalPrimeKernelDensity
  have hfloor : ⌊u⌋₊ ≤ 1 := by
    by_contra h
    have htwo : (2 : ℝ) ≤ u :=
      (Nat.le_floor_iff' (by decide : (2 : ℕ) ≠ 0)).mp (by omega : 2 ≤ ⌊u⌋₊)
    linarith
  rw [(factorialCriticalPrimeCumulativeCharge_sign ⌊u⌋₊).2.1.mpr hfloor, mul_zero]

/-- On `[5, ∞)`, the physical prime kernel density is bounded below by
`(log 2 / 150) * factorialCriticalPrimeKernelWeight u ≥ 0`. -/
theorem factorialCriticalPrimeKernelDensity_ge_of_five_le {u : ℝ} (hu : 5 ≤ u) :
    Real.log 2 / 150 * factorialCriticalPrimeKernelWeight u ≤
      factorialCriticalPrimeKernelDensity u ∧
    0 ≤ factorialCriticalPrimeKernelDensity u := by
  have hu0 : 0 ≤ u := by linarith
  have hw : 0 ≤ factorialCriticalPrimeKernelWeight u :=
    factorialCriticalPrimeKernelWeight_nonneg hu0
  have hfloor : 5 ≤ ⌊u⌋₊ := Nat.le_floor hu
  have hcharge : Real.log 2 / 150 ≤ factorialCriticalPrimeCumulativeCharge ⌊u⌋₊ :=
    (factorialCriticalPrimeCumulativeCharge_lower hfloor).le
  have hge : Real.log 2 / 150 * factorialCriticalPrimeKernelWeight u ≤
      factorialCriticalPrimeKernelDensity u := by
    unfold factorialCriticalPrimeKernelDensity
    rw [mul_comm (factorialCriticalPrimeKernelWeight u)]
    exact mul_le_mul_of_nonneg_right hcharge hw
  have hlog2 : 0 ≤ Real.log 2 / 150 := div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  exact ⟨hge, le_trans (mul_nonneg hlog2 hw) hge⟩

/-- Every cumulative charge `factorialCriticalPrimeCumulativeCharge N` is bounded below by
its global minimum `-Real.log 2 / 4` (attained at `N = 2`). -/
theorem factorialCriticalPrimeCumulativeCharge_ge_neg_log_two_div_four (N : ℕ) :
    -Real.log 2 / 4 ≤ factorialCriticalPrimeCumulativeCharge N := by
  have h2 : factorialCriticalPrimeCumulativeCharge 2 = -Real.log 2 / 4 := by
    have hI2 : Finset.Icc (1 : ℕ) 2 = {1, 2} := by decide
    have hA1 : factorialCriticalPrimeHarmonicCharge 1 = 0 :=
      (factorialCriticalPrimeHarmonicCharge_sign 1).2.1.mpr (Or.inl rfl)
    have hA2 := factorialCriticalPrimeHarmonicCharge_two
    norm_num [factorialCriticalPrimeCumulativeCharge, hI2, hA1, hA2]
    ring
  by_cases hN : 2 ≤ N
  · rw [← h2]
    exact factorialCriticalPrimeCumulativeCharge_mono le_rfl hN
  · have hN1 : N ≤ 1 := by omega
    rw [(factorialCriticalPrimeCumulativeCharge_sign N).2.1.mpr hN1]
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith

/-- Globally on `[0, ∞)`, the physical prime kernel density is bounded below by
`-(log 2 / 4) * factorialCriticalPrimeKernelWeight u`. -/
theorem factorialCriticalPrimeKernelDensity_ge_neg_log_two_div_four {u : ℝ} (hu : 0 ≤ u) :
    -(Real.log 2 / 4) * factorialCriticalPrimeKernelWeight u ≤
      factorialCriticalPrimeKernelDensity u := by
  unfold factorialCriticalPrimeKernelDensity
  rw [mul_comm (factorialCriticalPrimeKernelWeight u)]
  have h := mul_le_mul_of_nonneg_right
    (factorialCriticalPrimeCumulativeCharge_ge_neg_log_two_div_four ⌊u⌋₊)
    (factorialCriticalPrimeKernelWeight_nonneg hu)
  linarith

end GaloisForLFunctions.ArithmeticPositivityTheory

end
