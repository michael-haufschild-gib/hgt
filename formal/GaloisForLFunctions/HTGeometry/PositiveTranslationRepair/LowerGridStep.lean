import GaloisForLFunctions.HTGeometry.UniformGridStep

/-! A global Lipschitz bound supplies lower grid approximations with explicit error.
Their negative cells stay inside the region where the source is small. -/

open MeasureTheory Set

noncomputable section
namespace GaloisForLFunctions.HTGeometry.PositiveTranslationRepair

theorem exists_gridCell_of_mem {a h x : ℝ} (M : ℕ)
    (hx : x ∈ Ioc a (a + M * h)) : ∃ j ∈ Finset.range M, x ∈ gridCell a h j := by
  induction M with
  | zero => simp at hx
  | succ M ih =>
    by_cases he : x ≤ a + M * h
    · obtain ⟨j, hj, hxj⟩ := ih ⟨hx.1, he⟩
      exact ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hj)), hxj⟩
    · refine ⟨M, Finset.mem_range.mpr (Nat.lt_succ_self M), ?_⟩
      refine ⟨lt_of_not_ge he, ?_⟩
      simpa only [Nat.cast_add, Nat.cast_one] using hx.2

/-- Subtract one Lipschitz mesh error from each left endpoint value. -/
def lowerGridStep (f : ℝ → ℝ) (L a h : ℝ) (M : ℕ) : ℝ → ℝ :=
  gridStep (fun x => f x - L * h) a h M

/-- A Lipschitz lower step approximation loses at most twice the mesh times its constant. -/
theorem lowerGridStep_bounds {f : ℝ → ℝ} {L a h : ℝ} (hL : 0 ≤ L) (hh : 0 < h)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|) {M : ℕ} {x : ℝ}
    (hx : x ∈ Ioc a (a + M * h)) :
    lowerGridStep f L a h M x ≤ f x ∧ f x - lowerGridStep f L a h M x ≤ 2 * L * h := by
  obtain ⟨j, hj, hxj⟩ := exists_gridCell_of_mem M hx
  rw [lowerGridStep, gridStep_eq_of_mem hh hj hxj]
  have hd : |x - (a + j * h)| ≤ h := by
    rw [abs_of_nonneg (sub_nonneg.mpr hxj.1.le)]
    have hhx := hxj.2
    linarith only [hhx]
  have hb := (hf x (a + j * h)).trans (mul_le_mul_of_nonneg_left hd hL)
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  constructor <;> linarith only [hl, hu]

/-- Nonnegativity outside the grid turns the cellwise estimate into a global lower bound. -/
theorem lowerGridStep_le {f : ℝ → ℝ} {L a h : ℝ} (hL : 0 ≤ L) (hh : 0 < h)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|) {M : ℕ}
    (hout : ∀ x, x ∉ Ioc a (a + M * h) → 0 ≤ f x) (x : ℝ) :
    lowerGridStep f L a h M x ≤ f x := by
  by_cases hx : x ∈ Ioc a (a + M * h)
  · exact (lowerGridStep_bounds hL hh hf hx).1
  · rw [lowerGridStep, gridStep_eq_zero hh.le hx]
    exact hout x hx

/-- Negative cells can only occur where their left endpoint is below the Lipschitz margin. -/
theorem lowerGridStep_nonneg_of_left_margin {f : ℝ → ℝ} {L a h : ℝ}
    (hh : 0 < h) {M j : ℕ} (hj : j ∈ Finset.range M) {x : ℝ}
    (hx : x ∈ gridCell a h j) (hm : L * h ≤ f (a + j * h)) :
    0 ≤ lowerGridStep f L a h M x := by
  rw [lowerGridStep, gridStep_eq_of_mem hh hj hx]
  exact sub_nonneg.mpr hm

#print axioms lowerGridStep_bounds
#print axioms lowerGridStep_le

end GaloisForLFunctions.HTGeometry.PositiveTranslationRepair
