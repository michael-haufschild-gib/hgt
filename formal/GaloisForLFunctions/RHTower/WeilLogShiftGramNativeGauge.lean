import GaloisForLFunctions.RHTower.WeilLogShiftGramCoordinates
import GaloisForLFunctions.RHTower.WeilLogShiftGramNativeCostMinimum

/-!
# The native Gram cost gauge and its exact triangle equality

Canonical weights define a definite, positively homogeneous subadditive cost.
Triangle equality has a geometric criterion independent of cost magnitudes:
both canonical representations omit a common test, unless the dictionary is
empty. Symmetry is not asserted.
-/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace RHTower
namespace FiniteWeilGramCoordinates

variable {s : Finset ℕ} (D : FiniteWeilGramCoordinates s)

theorem unit_tailCost_pos (w : D.tests) : 0 < finiteWeilGramTailCost 1 w.1 := by
  have hs : s ≠ ∅ := by
    intro he
    have ht : D.tests = ∅ := Finset.card_eq_zero.mp
      (by simpa only [if_pos he] using D.cardinality)
    exact (Finset.nonempty_iff_ne_empty.mp
      (show D.tests.Nonempty from ⟨w.1, w.2⟩)) ht
  have hc : D.tests.card = s.card + 1 := by
    simpa only [if_neg hs] using D.cardinality
  exact finiteWeilGram_minimal_tailCost_pos (Finset.nonempty_iff_ne_empty.mpr hs)
    D.certificate hc zero_lt_one w.1 w.2

noncomputable def nativeGauge (L : (s → ℝ) →ₗ[ℝ] ℝ) : ℝ :=
  ∑ w, D.weights L w * finiteWeilGramTailCost 1 w.1

theorem nativeGauge_nonneg (L : (s → ℝ) →ₗ[ℝ] ℝ) : 0 ≤ D.nativeGauge L := by
  exact Finset.sum_nonneg fun w _ => mul_nonneg (D.weights_nonneg L w) (D.unit_tailCost_pos w).le

theorem nativeGauge_zero_iff (L : (s → ℝ) →ₗ[ℝ] ℝ) :
    D.nativeGauge L = 0 ↔ L = 0 := by
  constructor
  · intro hz
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg
      (fun w _ => mul_nonneg (D.weights_nonneg L w) (D.unit_tailCost_pos w).le)).mp hz
    have hq : D.weights L = 0 := by
      funext w
      exact (mul_eq_zero.mp (hterms w (Finset.mem_univ w))).resolve_right
        (ne_of_gt (D.unit_tailCost_pos w))
    apply LinearMap.ext
    intro c
    change L c = 0
    rw [D.represents L c, hq]
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  · rintro rfl
    simp only [nativeGauge, D.weights_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

theorem nativeGauge_nnreal_smul (r : NNReal) (L : (s → ℝ) →ₗ[ℝ] ℝ) :
    D.nativeGauge ((r : ℝ) • L) = (r : ℝ) * D.nativeGauge L := by
  simp only [nativeGauge, D.weights_nnreal_smul, Pi.smul_apply, smul_eq_mul,
    mul_assoc, ← Finset.mul_sum]

theorem nativeGauge_add_le (L M : (s → ℝ) →ₗ[ℝ] ℝ) :
    D.nativeGauge (L + M) ≤ D.nativeGauge L + D.nativeGauge M := by
  calc
    D.nativeGauge (L + M) ≤
        ∑ w, (D.weights L w + D.weights M w) * finiteWeilGramTailCost 1 w.1 := by
      apply Finset.sum_le_sum
      intro w _
      exact mul_le_mul_of_nonneg_right (D.weights_add_le L M w) (D.unit_tailCost_pos w).le
    _ = D.nativeGauge L + D.nativeGauge M := by
      simp only [add_mul, Finset.sum_add_distrib, nativeGauge]

theorem nativeGauge_add_eq_iff (L M : (s → ℝ) →ₗ[ℝ] ℝ) :
    D.nativeGauge (L + M) = D.nativeGauge L + D.nativeGauge M ↔
      D.tests = ∅ ∨ ∃ w, D.weights L w = 0 ∧ D.weights M w = 0 := by
  have h := finiteWeilGram_weighted_cost_eq_iff (D.weights (L + M))
    (D.weights L + D.weights M) (fun w => finiteWeilGramTailCost 1 w.1)
    (D.weights_add_le L M) D.unit_tailCost_pos
  have hc : (D.nativeGauge L + D.nativeGauge M = D.nativeGauge (L + M)) ↔
      D.weights L + D.weights M = D.weights (L + M) := by
    simpa only [Pi.add_apply, add_mul, Finset.sum_add_distrib, nativeGauge] using h
  constructor
  · intro he
    exact (D.weights_add_eq_iff L M).mp (hc.mp he.symm).symm
  · intro he
    exact (hc.mpr ((D.weights_add_eq_iff L M).mpr he).symm).symm

end FiniteWeilGramCoordinates

/-- The coordinate system and actual Gram cost gauge exist without a new
model premise. All functional and scalar arguments come after that choice. -/
theorem exists_finiteWeilGram_native_gauge (s : Finset ℕ) :
    ∃ D : FiniteWeilGramCoordinates s,
      (∀ L, 0 ≤ D.nativeGauge L) ∧
      (∀ L, D.nativeGauge L = 0 ↔ L = 0) ∧
      (∀ (r : NNReal) L, D.nativeGauge ((r : ℝ) • L) = (r : ℝ) * D.nativeGauge L) ∧
      (∀ L M, D.nativeGauge (L + M) ≤ D.nativeGauge L + D.nativeGauge M) ∧
      ∀ L M, D.nativeGauge (L + M) = D.nativeGauge L + D.nativeGauge M ↔
        D.tests = ∅ ∨ ∃ w, D.weights L w = 0 ∧ D.weights M w = 0 := by
  let D := finiteWeilGramCoordinates s
  exact ⟨D, D.nativeGauge_nonneg, D.nativeGauge_zero_iff, D.nativeGauge_nnreal_smul,
    D.nativeGauge_add_le, D.nativeGauge_add_eq_iff⟩

end RHTower
