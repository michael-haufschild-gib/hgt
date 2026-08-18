import GaloisForLFunctions.RHTower.Sieve.AveragedSquarefreeTailSharp
import GaloisForLFunctions.RHTower.Sieve.FibreSquarefreeMass

/-!
# The fibre truncation tail with no truncation-level term

Aggregating the sharp averaged tail over the outer block bounds the total fibre tail by
`4(⌈h⌉+1)(⌈√x⌉+⌈h⌉+1)/R`.  Against the earlier budget this drops the term proportional to the
truncation level `⌈√(x+h√x)⌉`, which alone exceeded the size of the outer block; what remains is
smaller than the outer block by the factor `(⌈h⌉+1)/R` once `h` is small against `√x`.
-/

namespace RHTower.Sieve

open Finset

/-- The aggregate fibre tail bound with no dependence on the truncation level. -/
noncomputable def fibreTailBudgetSharp (x h : ℝ) (R : ℕ) : ℝ :=
  4 * ((⌈h⌉₊ + 1 : ℕ) : ℝ)
    * ((((⌈Real.sqrt x⌉₊ : ℕ) : ℝ) + ((⌈h⌉₊ + 1 : ℕ) : ℝ)) / (R : ℝ))

/-- **The shifted start range, bounded by the sharp averaged tail.** -/
theorem sum_shift_windowTail_le_sharp {A B : ℕ} (L R M : ℕ) (hA : 1 ≤ A) (hR : 1 ≤ R) :
    ∑ y ∈ Finset.Icc A B, windowTail (y - 1) L R M
      ≤ (L : ℝ) * (((B : ℝ) + L) / (R : ℝ)) := by
  classical
  have hinj : ∀ y ∈ Finset.Icc A B, ∀ y' ∈ Finset.Icc A B, y - 1 = y' - 1 → y = y' := by
    intro y hy y' hy' he
    rw [Finset.mem_Icc] at hy hy'
    omega
  have himg : (Finset.Icc A B).image (fun y => y - 1) ⊆ Finset.Ico (A - 1) B := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨y, hy, rfl⟩ := ht
    rw [Finset.mem_Icc] at hy
    rw [Finset.mem_Ico]
    omega
  have hreindex : ∑ t ∈ (Finset.Icc A B).image (fun y => y - 1), windowTail t L R M
      = ∑ y ∈ Finset.Icc A B, windowTail (y - 1) L R M := Finset.sum_image hinj
  have hgrow : ∑ t ∈ (Finset.Icc A B).image (fun y => y - 1), windowTail t L R M
      ≤ ∑ t ∈ Finset.Ico (A - 1) B, windowTail t L R M :=
    Finset.sum_le_sum_of_subset_of_nonneg himg
      (fun t _ _ => windowTail_nonneg _ _ _ _)
  have hbase := sum_tail_divisor_count_le_sharp (A - 1) B L R M hR
  rw [← hreindex]
  refine hgrow.trans ?_
  simpa [windowTail] using hbase

/-- **The fibre tails are bounded in aggregate, with no truncation-level term.** -/
theorem sum_fibre_windowTail_le_budget_sharp {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {R M' : ℕ}
    (hR : 1 ≤ R) :
    ∑ a ∈ outerBlock x h, windowTail (fibreStartIdx x a) (fibreLen x h a) R M'
      ≤ fibreTailBudgetSharp x h R := by
  have h1 := sum_fibre_windowTail_le hx hh R M'
  have hA : 1 ≤ ⌈Real.sqrt x / 2⌉₊ := by
    refine Nat.one_le_ceil_iff.2 ?_
    have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    positivity
  have h2 := sum_shift_windowTail_le_sharp (A := ⌈Real.sqrt x / 2⌉₊) (B := ⌈Real.sqrt x⌉₊)
    (⌈h⌉₊ + 1) R M' hA hR
  have h3 : 4 * ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
      windowTail (y - 1) (⌈h⌉₊ + 1) R M' ≤ fibreTailBudgetSharp x h R := by
    rw [fibreTailBudgetSharp]
    have := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 4)
    linarith
  linarith

/-- **The exceptional fibres are few.**  Markov against the sharp aggregate tail budget. -/
theorem card_fibre_bad_le_sharp {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {R M' : ℕ}
    (hR : 1 ≤ R) {θ : ℝ} (hθ : 0 < θ) :
    ((((outerBlock x h).filter (fun a =>
        θ ≤ windowTail (fibreStartIdx x a) (fibreLen x h a) R M')).card : ℕ) : ℝ)
      ≤ fibreTailBudgetSharp x h R / θ := by
  classical
  exact card_large_le_of_sum_le hθ
    (fun a _ => windowTail_nonneg _ _ _ _)
    (sum_fibre_windowTail_le_budget_sharp hx hh hR)

end RHTower.Sieve
