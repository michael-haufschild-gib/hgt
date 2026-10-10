import GaloisForLFunctions.RHTower.WeilLogShiftGramCostInflation

/-! Grouping amplitudes over coincident nodes preserves Gram forms and contracts
tail cost. Equality at positive scales detects exactly the absence of cancellation. -/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable section
namespace RHTower

def finiteWeilGramFiberAmplitude {ι κ : Type} [Fintype ι]
    (q : ι → κ) (u : ι → ℝ) (y : κ) : ℝ :=
  ∑ i ∈ Finset.univ with q i = y, u i

private theorem fiber_sum_mul {ι κ : Type} [Fintype ι] [Fintype κ]
    (q : ι → κ) (u : ι → ℝ) (f : κ → ℝ) :
    ∑ y, finiteWeilGramFiberAmplitude q u y * f y = ∑ i, u i * f (q i) := by
  simp only [finiteWeilGramFiberAmplitude, Finset.sum_mul]
  calc
    (∑ y, ∑ i ∈ Finset.univ with q i = y, u i * f y) =
        ∑ y, ∑ i ∈ Finset.univ with q i = y, u i * f (q i) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise Finset.univ q (fun i => u i * f (q i))

theorem finiteWeilGram_fiber_quadratic {ι κ : Type} [Fintype ι] [Fintype κ]
    (q : ι → κ) (u : ι → ℝ) (K : κ → κ → ℝ) :
    (∑ y, ∑ z, finiteWeilGramFiberAmplitude q u y *
      finiteWeilGramFiberAmplitude q u z * K y z) =
      ∑ i, ∑ j, u i * u j * K (q i) (q j) := by
  calc
    _ = ∑ y, finiteWeilGramFiberAmplitude q u y *
        ∑ z, finiteWeilGramFiberAmplitude q u z * K y z := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ y, finiteWeilGramFiberAmplitude q u y * ∑ j, u j * K y (q j) := by
      simp only [fiber_sum_mul]
    _ = ∑ i, u i * ∑ j, u j * K (q i) (q j) :=
      fiber_sum_mul q u (fun y => ∑ j, u j * K y (q j))
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

theorem finiteWeilGramForm_fiberAmplitude (s : Finset ℕ)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (q : ι → κ) (x : κ → ℝ) (u : ι → ℝ) (a : NNReal) :
    finiteWeilGramForm s (finiteWeilGramTestOfFinite x
      (finiteWeilGramFiberAmplitude q u) a) =
      finiteWeilGramForm s (finiteWeilGramTestOfFinite (x ∘ q) u a) := by
  apply LinearMap.ext
  intro c
  rw [finiteWeilGramCoefficientVector_pairing, finiteWeilGramCoefficientVector_pairing]
  apply Finset.sum_congr rfl
  intro k _
  simp only [finiteWeilGramCoefficientVector_ofFinite, Function.comp_apply,
    finiteWeilGram_fiber_quadratic]

theorem finiteWeilGramTailCost_fiber_expansion (B : ℝ)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (q : ι → κ) (x : κ → ℝ) (u : ι → ℝ) (a : NNReal) :
    finiteWeilGramTailCost B (finiteWeilGramTestOfFinite (x ∘ q) u a) =
      (a : ℝ) * ∑ y, ∑ z,
        finiteWeilGramFiberAmplitude q (fun i => |u i|) y *
        finiteWeilGramFiberAmplitude q (fun i => |u i|) z *
        (B * Real.exp (2 * |x z - x y|)) := by
  rw [finiteWeilGramTailCost_ofFinite, finiteWeilGram_fiber_quadratic]
  simp only [Function.comp_apply, abs_mul]

private theorem fiber_abs_le {ι κ : Type} [Fintype ι]
    (q : ι → κ) (u : ι → ℝ) (y : κ) :
    |finiteWeilGramFiberAmplitude q u y| ≤
      finiteWeilGramFiberAmplitude q (fun i => |u i|) y :=
  Finset.abs_sum_le_sum_abs _ _

private theorem fiber_cost_term_le {ι κ : Type} [Fintype ι]
    (q : ι → κ) (x : κ → ℝ) (u : ι → ℝ) {B : ℝ} (hB : 0 ≤ B) (y z : κ) :
    |finiteWeilGramFiberAmplitude q u y| * |finiteWeilGramFiberAmplitude q u z| *
        (B * Real.exp (2 * |x z - x y|)) ≤
      finiteWeilGramFiberAmplitude q (fun i => |u i|) y *
        finiteWeilGramFiberAmplitude q (fun i => |u i|) z *
        (B * Real.exp (2 * |x z - x y|)) := by
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg hB (Real.exp_pos _).le)
  exact mul_le_mul (fiber_abs_le q u y) (fiber_abs_le q u z) (abs_nonneg _)
    ((abs_nonneg _).trans (fiber_abs_le q u y))

theorem finiteWeilGramTailCost_fiberAmplitude_le {B : ℝ} (hB : 0 ≤ B)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (q : ι → κ) (x : κ → ℝ) (u : ι → ℝ) (a : NNReal) :
    finiteWeilGramTailCost B (finiteWeilGramTestOfFinite x
      (finiteWeilGramFiberAmplitude q u) a) ≤
      finiteWeilGramTailCost B (finiteWeilGramTestOfFinite (x ∘ q) u a) := by
  rw [finiteWeilGramTailCost_ofFinite, finiteWeilGramTailCost_fiber_expansion]
  simp only [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg a)
  exact Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun z _ =>
    fiber_cost_term_le q x u hB y z

theorem finiteWeilGramTailCost_fiberAmplitude_eq_iff {B : ℝ} (hB : 0 < B)
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (q : ι → κ) (x : κ → ℝ) (u : ι → ℝ) (a : NNReal) (ha : 0 < (a : ℝ)) :
    finiteWeilGramTailCost B (finiteWeilGramTestOfFinite x
      (finiteWeilGramFiberAmplitude q u) a) =
      finiteWeilGramTailCost B (finiteWeilGramTestOfFinite (x ∘ q) u a) ↔
      ∀ y, |finiteWeilGramFiberAmplitude q u y| =
        finiteWeilGramFiberAmplitude q (fun i => |u i|) y := by
  rw [finiteWeilGramTailCost_ofFinite, finiteWeilGramTailCost_fiber_expansion]
  simp only [abs_mul]
  constructor
  · intro h y
    have hs := mul_left_cancel₀ ha.ne' h
    have hy := (Finset.sum_eq_sum_iff_of_le (fun y _ =>
      Finset.sum_le_sum fun z _ => fiber_cost_term_le q x u hB.le y z)).mp hs y
        (Finset.mem_univ y)
    have hyy := (Finset.sum_eq_sum_iff_of_le (fun z _ =>
      fiber_cost_term_le q x u hB.le y z)).mp hy y (Finset.mem_univ y)
    have heq := mul_right_cancel₀ (mul_pos hB (Real.exp_pos _)).ne' hyy
    have hp := abs_nonneg (finiteWeilGramFiberAmplitude q u y)
    have hq := hp.trans (fiber_abs_le q u y)
    nlinarith
  · intro h
    simp only [h]

end RHTower
