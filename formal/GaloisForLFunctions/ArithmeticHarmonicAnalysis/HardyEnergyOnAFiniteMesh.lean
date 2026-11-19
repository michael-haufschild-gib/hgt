import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quadratic Hardy energy on a finite mesh

A two-endpoint square completion proves the quadratic case of the finite
mesh Hardy inequality of Chen–Frank–Xiao–Yang–Yuan–Zhang
(arXiv:2611.22706, Lemma 3.5), with constant four and an outer boundary term.
-/

open Finset
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
noncomputable section

private theorem hardy_cell {a b x y : ℝ} (ha : 0 ≤ a) (hb : a < b) (hx : a = 0 → x = 0) :
    (b-a)*x^2/b^2 + 2*y^2/b ≤ 4*(y-x)^2/(b-a) + 2*x^2/a := by
  rcases ha.eq_or_lt with h | ha
  · subst a
    rw [hx rfl]
    simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_div, zero_add, add_zero]
    exact div_le_div_of_nonneg_right (by nlinarith only [sq_nonneg y]) hb.le
  have hd := sub_pos.mpr hb
  have hb' := ha.trans hb
  have hs := add_pos ha hb'
  have he : 4*(y-x)^2/(b-a) + 2*x^2/a - ((b-a)*x^2/b^2 + 2*y^2/b) =
      (2*a*b*((a+b)*y-2*b*x)^2 + (b-a)^3*(2*b+a)*x^2) / (a*(b-a)*b^2*(a+b)) := by
    field_simp [ha.ne', hb'.ne', hd.ne', hs.ne']
    ring
  exact sub_nonneg.mp (he ▸ (by positivity))

/-- Discrete quadratic Hardy estimate with both boundary terms on an arbitrary
strictly decreasing nonnegative mesh. A zero-radius vertex is grounded. -/
theorem mesh_hardy_energy (h z : ℕ → ℝ) (M : ℕ)
    (hh : ∀ i ∈ range M, 0 ≤ h (i+1) ∧ h (i+1) < h i)
    (hz : ∀ i ∈ range M, h (i+1) = 0 → z (i+1) = 0) :
    (∑ i ∈ range M, (h i-h (i+1))*z (i+1)^2/(h i)^2) + 2*z 0^2/h 0 ≤
      4*(∑ i ∈ range M, (z i-z (i+1))^2/(h i-h (i+1))) + 2*z M^2/h M := by
  let b (i : ℕ) := 2*z i^2/h i
  have H := sum_le_sum (s := range M) (fun i hi =>
    (show (h i-h (i+1))*z (i+1)^2/(h i)^2 ≤
      4*((z i-z (i+1))^2/(h i-h (i+1))) + (b (i+1)-b i) by
      dsimp only [b]
      rw [← mul_div_assoc]
      linarith only [hardy_cell (x:=z (i+1)) (y:=z i) (hh i hi).1 (hh i hi).2 (hz i hi)]))
  rw [sum_add_distrib, ← mul_sum, sum_range_sub] at H
  dsimp only [b] at H
  linarith only [H]

/-- The selected-mesh Hardy inequality with constant four. On each selected
cell the lost radius is at least a fraction β of its outer radius. -/
theorem hardy_on_large_mesh_steps (h z : ℕ → ℝ) (M : ℕ) (β : ℝ) (hβ : 0 < β)
    (hh : ∀ i ∈ range M, 0 ≤ h (i+1) ∧ h (i+1) < h i)
    (hz : ∀ i ∈ range M, h (i+1) = 0 → z (i+1) = 0) (hend : z M = 0) :
    β^2 * (∑ i ∈ (range M).filter (fun i => β*h i ≤ h i-h (i+1)),
      z (i+1)^2/(h i-h (i+1))) + 2*z 0^2/h 0 ≤
      4*(∑ i ∈ range M, (z i-z (i+1))^2/(h i-h (i+1))) := by
  let G := (range M).filter (fun i => β*h i ≤ h i-h (i+1))
  have hle : β^2 * (∑ i ∈ G, z (i+1)^2/(h i-h (i+1))) ≤
      ∑ i ∈ range M, (h i-h (i+1))*z (i+1)^2/(h i)^2 := by
    rw [mul_sum]
    apply le_trans (sum_le_sum (s:=G) (g:=fun i => (h i-h (i+1))*z (i+1)^2/(h i)^2) ?_)
    · exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) fun i hi _ =>
        div_nonneg (mul_nonneg (sub_nonneg.mpr (hh i hi).2.le) (sq_nonneg _)) (sq_nonneg _)
    · intro i hi
      obtain ⟨hm, hg⟩ := mem_filter.mp hi
      have hr := (hh i hm).1.trans_lt (hh i hm).2
      have hd := sub_pos.mpr (hh i hm).2
      have hs := mul_le_mul hg hg (mul_nonneg hβ.le hr.le) hd.le
      rw [le_div_iff₀ (sq_pos_of_pos hr)]
      field_simp [hd.ne']
      nlinarith only [mul_le_mul_of_nonneg_right hs (sq_nonneg (z (i+1)))]
  have H := mesh_hardy_energy h z M hh hz
  rw [hend] at H
  simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    add_zero] using (add_le_add hle (le_refl (2*z 0^2/h 0))).trans H

#print axioms mesh_hardy_energy
#print axioms hardy_on_large_mesh_steps
end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
