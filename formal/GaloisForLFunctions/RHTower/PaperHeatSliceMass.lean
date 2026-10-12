import GaloisForLFunctions.RHTower.PaperHeatSliceCriterion
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# All-order negative Taylor mass of the actual heat source

The radius weights are the actual Taylor weights, and all orders are retained.
A Fourier-kernel Cauchy estimate gives uniform convergence over every real height.
-/

namespace RHTower.PaperHeatSlice
noncomputable section
open Complex MeasureTheory Filter Set
open RHTower.DeBruijn
open scoped Topology ComplexOrder NNReal

def massTerm (lam : ℝ≥0) (r : Radius) (t : ℝ) (n : ℕ) : ℝ :=
  max 0 (-(coeff lam t n).re) * (r : ℝ) ^ n

def mass (lam : ℝ≥0) (r : Radius) (t : ℝ) : ℝ := ∑' n, massTerm lam r t n

def massBudget (lam : ℝ≥0) (r : Radius) : ℝ := 2 * stripBudget lam (2 * r) ^ 2

theorem massTerm_nonneg (lam : ℝ≥0) (r : Radius) (t : ℝ) (n : ℕ) :
    0 ≤ massTerm lam r t n := mul_nonneg (le_max_left _ _) (pow_nonneg r.property.le _)

theorem continuous_massTerm (lam : ℝ≥0) (r : Radius) (n : ℕ) :
    Continuous fun t => massTerm lam r t n :=
  (continuous_const.max ((Complex.continuous_re.comp (continuous_coeff lam n)).neg)).mul_const _

theorem norm_massTerm_le (lam : ℝ≥0) (r : Radius) (t : ℝ) (n : ℕ) :
    ‖massTerm lam r t n‖ ≤ stripBudget lam (2 * r) ^ 2 * (1 / 2 : ℝ) ^ n := by
  rw [Real.norm_eq_abs, abs_of_nonneg (massTerm_nonneg lam r t n)]
  have hc := norm_coeff_le lam ⟨2 * r, mul_pos (by norm_num) r.property⟩ t n
  have hm : max 0 (-(coeff lam t n).re) ≤ ‖coeff lam t n‖ :=
    max_le (norm_nonneg _) ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
  calc
    massTerm lam r t n ≤ ‖coeff lam t n‖ * (r : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right hm (pow_nonneg r.property.le _)
    _ ≤ (stripBudget lam (2 * r) ^ 2 / (2 * (r : ℝ)) ^ n) * (r : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg r.property.le _)
    _ = stripBudget lam (2 * r) ^ 2 * (1 / 2 : ℝ) ^ n := by
      rw [div_mul_eq_mul_div, mul_div_assoc, ← div_pow, show (r : ℝ) / (2 * r) = 1 / 2 by
        field_simp [ne_of_gt r.property]]

theorem summable_massMajorant (lam : ℝ≥0) (r : Radius) :
    Summable fun n : ℕ => stripBudget lam (2 * r) ^ 2 * (1 / 2 : ℝ) ^ n :=
  (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _

theorem summable_massTerm (lam : ℝ≥0) (r : Radius) (t : ℝ) :
    Summable (massTerm lam r t) :=
  (summable_massMajorant lam r).of_norm_bounded (norm_massTerm_le lam r t)

theorem continuous_mass (lam : ℝ≥0) (r : Radius) : Continuous (mass lam r) :=
  continuous_tsum (continuous_massTerm lam r) (summable_massMajorant lam r)
    (fun n t => norm_massTerm_le lam r t n)

theorem mass_nonneg (lam : ℝ≥0) (r : Radius) (t : ℝ) : 0 ≤ mass lam r t :=
  tsum_nonneg (massTerm_nonneg lam r t)

theorem massBudget_nonneg (lam : ℝ≥0) (r : Radius) : 0 ≤ massBudget lam r := by
  unfold massBudget; positivity

theorem mass_le_budget (lam : ℝ≥0) (r : Radius) (t : ℝ) :
    mass lam r t ≤ massBudget lam r := by
  have h := (summable_massTerm lam r t).tsum_le_tsum
    (fun n => by simpa only [Real.norm_eq_abs, abs_of_nonneg (massTerm_nonneg lam r t n)]
      using norm_massTerm_le lam r t n)
    (summable_massMajorant lam r)
  refine h.trans_eq ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  unfold massBudget
  ring

theorem massTerm_eq_zero_iff (lam : ℝ≥0) (r : Radius) (t : ℝ) (n : ℕ) :
    massTerm lam r t n = 0 ↔ 0 ≤ (coeff lam t n).re := by
  rw [massTerm, mul_eq_zero]
  simp only [pow_ne_zero n r.property.ne', or_false]
  rw [max_eq_left_iff, neg_nonpos]

theorem mass_eq_zero_iff (lam : ℝ≥0) (r : Radius) (t : ℝ) :
    mass lam r t = 0 ↔ NonnegTaylorAtZero (source lam t) := by
  rw [nonnegTaylor_iff_coeff]
  constructor
  · intro h n
    apply (massTerm_eq_zero_iff lam r t n).mp
    apply le_antisymm _ (massTerm_nonneg lam r t n)
    have hn := (summable_massTerm lam r t).le_tsum n
      (fun i _ => massTerm_nonneg lam r t i)
    exact hn.trans_eq h
  · intro h
    have hz : massTerm lam r t = fun _ => 0 := funext fun n =>
      (massTerm_eq_zero_iff lam r t n).mpr (h n)
    simp only [mass, hz, tsum_zero]

theorem mass_eq_zero_iff_threshold (lam : ℝ≥0) (r : Radius) :
    mass lam r = 0 ↔ newmanConstant ≤ lam := by
  rw [← forall_nonnegTaylor_iff_threshold]
  simp only [funext_iff, Pi.zero_apply, mass_eq_zero_iff]

theorem mass_zero_eq_zero_iff_rh (r : Radius) : mass 0 r = 0 ↔ RiemannHypothesis := by
  rw [mass_eq_zero_iff_threshold, riemannHypothesis_iff_newmanConstant_eq_zero]
  exact ⟨fun h => le_antisymm h newmanConstant_nonneg, fun h => h.le⟩

/-- One height cutoff works for every Taylor order and every positive Taylor radius. -/
theorem exists_mass_support (lam : Radius) :
    ∃ T : ℝ, ∀ (r : Radius) (t : ℝ), T ≤ |t| → mass ⟨lam, lam.property.le⟩ r t = 0 := by
  obtain ⟨T, hT⟩ := exists_nonnegTaylorAtZero_riemannHeat_slice lam.property
  exact ⟨T, fun r t ht => (mass_eq_zero_iff _ r t).mpr (hT t ht)⟩

end
end RHTower.PaperHeatSlice
