import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Shift-uniform Cauchy lattice bounds for Weil sampling

The proven scaled-Cauchy estimate in OpenAI/math,
`OAI/NumberTheory/DirichletL/GaussSum/MixedConversion.lean`, is extended from
the unshifted lattice to every real translate. Widths `1 / (k + 1)` are
positive by construction. The resulting bound controls all integer samples
at once and will be applied to the actual Weil deficit measures.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower.WeilSpectral

/-- A Cauchy probe with width `1 / (k + 1)` and peak value one. -/
def paperCauchyKernel (k : ℕ) (x : ℝ) : ℝ :=
  (1 + (((k : ℝ) + 1) * x) ^ 2)⁻¹

theorem paperCauchyKernel_nonneg (k : ℕ) (x : ℝ) :
    0 ≤ paperCauchyKernel k x := by
  unfold paperCauchyKernel
  positivity

theorem paperCauchyKernel_le_one (k : ℕ) (x : ℝ) :
    paperCauchyKernel k x ≤ 1 := by
  unfold paperCauchyKernel
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (((k : ℝ) + 1) * x)])

theorem paperCauchyKernel_neg (k : ℕ) (x : ℝ) :
    paperCauchyKernel k (-x) = paperCauchyKernel k x := by
  simp only [paperCauchyKernel, mul_neg, neg_sq]

theorem continuous_paperCauchyKernel (k : ℕ) : Continuous (paperCauchyKernel k) := by
  unfold paperCauchyKernel
  exact (continuous_const.add ((continuous_const.mul continuous_id).pow 2)).inv₀
    (fun x => by change 1 + (((k : ℝ) + 1) * x) ^ 2 ≠ 0; positivity)

private theorem kernel_antitone (k : ℕ) :
    AntitoneOn (paperCauchyKernel k) (Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  unfold paperCauchyKernel
  apply inv_anti₀ (by positivity)
  nlinarith [mul_nonneg (sq_nonneg ((k : ℝ) + 1))
    (show 0 ≤ y ^ 2 - x ^ 2 by nlinarith)]

theorem summable_paperCauchyKernel_nat (k : ℕ) :
    Summable (fun n : ℕ => paperCauchyKernel k n) :=
  (kernel_antitone k).summable_of_integrableOn_Ioi_zero
    (integrable_inv_one_add_sq.comp_mul_left' (by positivity : (k : ℝ) + 1 ≠ 0)).integrableOn
    (fun x _ => paperCauchyKernel_nonneg k x)

/-- The source's one-sided integral-test estimate at the native recovery widths. -/
theorem tsum_paperCauchyKernel_nat_le (k : ℕ) :
    (∑' n : ℕ, paperCauchyKernel k n) ≤ 1 + Real.pi / (2 * ((k : ℝ) + 1)) := by
  have hi := (integrable_inv_one_add_sq.comp_mul_left'
    (by positivity : (k : ℝ) + 1 ≠ 0)).integrableOn (s := Ioi 0)
  have ht := (kernel_antitone k).tsum_le_integral hi
    (fun x _ => paperCauchyKernel_nonneg k x)
  have he : (∫ x : ℝ in Ioi 0, paperCauchyKernel k x) =
      Real.pi / (2 * ((k : ℝ) + 1)) := by
    unfold paperCauchyKernel
    rw [integral_comp_mul_left_Ioi (fun x : ℝ => (1 + x ^ 2)⁻¹) 0
      (by positivity : 0 < (k : ℝ) + 1)]
    simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero, smul_eq_mul]
    field_simp
  rw [he] at ht
  simpa only [paperCauchyKernel, mul_zero, zero_pow (by decide : 2 ≠ 0),
    add_zero, inv_one] using ht

private theorem lattice_unit_shift (k : ℕ) (x : ℝ) (hx : x ∈ Icc 0 1) :
    Summable (fun n : ℤ => paperCauchyKernel k ((n : ℝ) + x)) ∧
      (∑' n : ℤ, paperCauchyKernel k ((n : ℝ) + x)) ≤
        2 + Real.pi / ((k : ℝ) + 1) := by
  have hs := summable_paperCauchyKernel_nat k
  have hp : ∀ n : ℕ, paperCauchyKernel k ((n : ℝ) + x) ≤ paperCauchyKernel k n := by
    intro n
    exact kernel_antitone k (show (n : ℝ) ∈ Ici 0 from Nat.cast_nonneg (α := ℝ) n)
      (show (n : ℝ) + x ∈ Ici 0 from add_nonneg (Nat.cast_nonneg (α := ℝ) n) hx.1)
      (by linarith [hx.1])
  have hn : ∀ n : ℕ,
      paperCauchyKernel k ((-(n + 1) : ℤ) + x) ≤ paperCauchyKernel k n := by
    intro n
    have he : ((-(n + 1) : ℤ) : ℝ) + x = -((n : ℝ) + 1 - x) := by push_cast; ring
    rw [he, paperCauchyKernel_neg]
    exact kernel_antitone k (show (n : ℝ) ∈ Ici 0 from Nat.cast_nonneg (α := ℝ) n)
      (by change 0 ≤ (n : ℝ) + 1 - x; linarith [hx.2, Nat.cast_nonneg (α := ℝ) n])
      (by linarith [hx.2])
  have hsp : Summable (fun n : ℕ => paperCauchyKernel k ((n : ℝ) + x)) :=
    Summable.of_nonneg_of_le (fun _ => paperCauchyKernel_nonneg _ _) hp hs
  have hsn : Summable (fun n : ℕ => paperCauchyKernel k ((-(n + 1) : ℤ) + x)) :=
    Summable.of_nonneg_of_le (fun _ => paperCauchyKernel_nonneg _ _) hn hs
  refine ⟨Summable.of_nat_of_neg_add_one
    (f := fun n : ℤ => paperCauchyKernel k ((n : ℝ) + x)) hsp hsn, ?_⟩
  rw [tsum_of_nat_of_neg_add_one
    (f := fun n : ℤ => paperCauchyKernel k ((n : ℝ) + x)) hsp hsn]
  have hbp := hsp.tsum_le_tsum hp hs
  have hbn := hsn.tsum_le_tsum hn hs
  have hb := tsum_paperCauchyKernel_nat_le k
  have he : Real.pi / (2 * ((k : ℝ) + 1)) = (Real.pi / ((k : ℝ) + 1)) / 2 := by
    rw [div_mul_eq_div_div_swap]
  rw [he] at hb
  simp only [Int.cast_natCast]
  linarith only [hbp, hbn, hb]

private theorem shifted_lattice (k : ℕ) (y : ℝ) :
    Summable (fun n : ℤ => paperCauchyKernel k ((n : ℝ) - y)) ∧
      (∑' n : ℤ, paperCauchyKernel k ((n : ℝ) - y)) ≤
        2 + Real.pi / ((k : ℝ) + 1) := by
  let j : ℤ := ⌈y⌉
  have hx : (j : ℝ) - y ∈ Icc 0 1 :=
    ⟨sub_nonneg.mpr (Int.le_ceil y), by have := Int.ceil_lt_add_one y; dsimp [j]; linarith⟩
  obtain ⟨hs, hb⟩ := lattice_unit_shift k ((j : ℝ) - y) hx
  let f : ℤ → ℝ := fun n => paperCauchyKernel k ((n : ℝ) - y)
  have he : (fun n : ℤ => paperCauchyKernel k ((n : ℝ) + ((j : ℝ) - y))) =
      fun n => f (Equiv.addRight j n) := by
    funext n
    change paperCauchyKernel k ((n : ℝ) + ((j : ℝ) - y)) =
      paperCauchyKernel k (((n + j : ℤ) : ℝ) - y)
    rw [Int.cast_add, add_sub_assoc]
  rw [he] at hs hb
  exact ⟨(Equiv.addRight j).summable_iff.mp hs,
    by simpa only [Equiv.tsum_eq] using hb⟩

/-- Every real translate of the Cauchy lattice is summable. -/
theorem summable_paperCauchyKernel_lattice (k : ℕ) (y : ℝ) :
    Summable (fun n : ℤ => paperCauchyKernel k ((n : ℝ) - y)) :=
  (shifted_lattice k y).1

/-- A shift-uniform bound, independent of how many lattice sites are sampled. -/
theorem tsum_paperCauchyKernel_lattice_le (k : ℕ) (y : ℝ) :
    (∑' n : ℤ, paperCauchyKernel k ((n : ℝ) - y)) ≤ 2 + Real.pi / ((k : ℝ) + 1) :=
  (shifted_lattice k y).2

theorem sum_paperCauchyKernel_lattice_le (k : ℕ) (y : ℝ) (s : Finset ℤ) :
    (∑ n ∈ s, paperCauchyKernel k ((n : ℝ) - y)) ≤ 2 + Real.pi / ((k : ℝ) + 1) :=
  (Summable.sum_le_tsum s (fun _ _ => paperCauchyKernel_nonneg _ _)
    (summable_paperCauchyKernel_lattice k y)).trans (tsum_paperCauchyKernel_lattice_le k y)

/-- An integer site within half a unit prevents the sampled mass from disappearing. -/
theorem paperCauchyKernel_half_le_lattice (k : ℕ) (y : ℝ) :
    paperCauchyKernel k (1 / 2) ≤ ∑' n : ℤ, paperCauchyKernel k ((n : ℝ) - y) := by
  have hd : |((round y : ℤ) : ℝ) - y| ≤ 1 / 2 := by
    rw [abs_sub_comm]
    exact abs_sub_round y
  have hk : paperCauchyKernel k (1 / 2) ≤
      paperCauchyKernel k (((round y : ℤ) : ℝ) - y) := by
    have h := kernel_antitone k (show |((round y : ℤ) : ℝ) - y| ∈ Ici 0 from
      abs_nonneg (((round y : ℤ) : ℝ) - y))
      (show (1 / 2 : ℝ) ∈ Ici 0 by change (0 : ℝ) ≤ 1 / 2; positivity) hd
    simpa only [paperCauchyKernel, mul_pow, sq_abs] using h
  exact hk.trans ((summable_paperCauchyKernel_lattice k y).le_tsum (round y)
    (fun _ _ => paperCauchyKernel_nonneg _ _))

end RHTower.WeilSpectral
