import GaloisForLFunctions.RHTower.HeatGridAliasingBoundary
import GaloisForLFunctions.RHTower.CCMPrimePoleFiniteCoherence

/-!
# Finite offset families cannot remove heat-grid aliasing

Simultaneous recurrence chooses arbitrarily high alias frequencies whose
cosines are positive at every prescribed finite offset. The complete
Hankel form on each offset grid is then a positive rank-one moment form,
although the underlying conjugate pair is nonreal and its continuous
heat trace takes negative values. Changing finitely many offsets cannot
replace the two incommensurate grid steps in the Xi source criterion.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- Arbitrarily late integer aliases have positive phase at every finite offset. -/
theorem exists_integer_alias_positive_cos {d : ℕ} (h : ℝ)
    (offset : Fin d → ℝ) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ 0 < n ∧
      ∀ i, 0 < Real.cos (2 * Real.pi * ((n : ℝ) * (offset i / h))) := by
  have hdelta : 0 < 1 / (2 * Real.pi) := by positivity
  obtain ⟨n, hn, r, hr⟩ := exists_fin_simultaneous_integer_approximation_of_lt
    (fun i => offset i / h) hdelta (B + 1)
  refine ⟨n, by omega, by omega, fun i => ?_⟩
  let x := 2 * Real.pi * ((n : ℝ) * (offset i / h))
  have hphase : |x - 2 * Real.pi * r i| ≤ 1 := by
    have heq : x - 2 * Real.pi * r i =
        (2 * Real.pi) * ((n : ℝ) * (offset i / h) - r i) := by dsimp [x]; ring
    rw [heq, abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    calc 2 * Real.pi * |(n : ℝ) * (offset i / h) - r i|
        ≤ 2 * Real.pi * (1 / (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left (hr i) (by positivity)
      _ = 1 := by field_simp
  have hc := one_sub_sq_phaseError_div_two_le_re_exp_I_mul_real
    x 1 (r i) zero_le_one hphase
  simp only [Complex.exp_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
    zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self,
    Real.exp_zero, Complex.mul_im, one_mul, zero_add] at hc
  dsimp [x] at hc
  linarith

/-- A high alias is a positive geometric sequence on each offset with positive cosine. -/
theorem heatGridAliasedTrace_offset {h : ℝ} (hh : 0 < h)
    {n : ℕ} (hn : 0 < n) (t : ℝ) (m : ℕ) :
    heatGridAliasedTrace (h / n) (t + (m : ℝ) * h) =
      (2 * Real.exp (-t * (1 + (2 * Real.pi / (h / n)) ^ 2)) *
        Real.cos (t * (2 * Real.pi / (h / n)))) *
      Real.exp (-h * (1 + (2 * Real.pi / (h / n)) ^ 2)) ^ m := by
  rw [heatGridAliasedTrace_eq]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hphase : (t + (m : ℝ) * h) * (2 * Real.pi / (h / n)) =
      t * (2 * Real.pi / (h / n)) + ((m * n : ℕ) : ℝ) * (2 * Real.pi) := by
    push_cast
    field_simp [ne_of_gt hh, hnR]
  rw [hphase, Real.cos_add_nat_mul_two_pi]
  have hexp : -(t + (m : ℝ) * h) * (1 + (2 * Real.pi / (h / n)) ^ 2) =
      -t * (1 + (2 * Real.pi / (h / n)) ^ 2) +
      (m : ℝ) * (-h * (1 + (2 * Real.pi / (h / n)) ^ 2)) := by ring
  rw [hexp, Real.exp_add, Real.exp_nat_mul]
  ring

theorem completeHankelCone_heatGridAliasedTrace_offset {h : ℝ} (hh : 0 < h)
    {n : ℕ} (hn : 0 < n) (t : ℝ)
    (ht : 0 < Real.cos (t * (2 * Real.pi / (h / n)))) :
    CompleteHankelCone (fun m : ℕ => heatGridAliasedTrace (h / n) (t + (m : ℝ) * h)) := by
  rw [completeHankelCone_iff_momentFunctional_square_nonnegative]
  intro p
  let c := 2 * Real.exp (-t * (1 + (2 * Real.pi / (h / n)) ^ 2)) *
    Real.cos (t * (2 * Real.pi / (h / n)))
  let r := Real.exp (-h * (1 + (2 * Real.pi / (h / n)) ^ 2))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hfunctional (P : ℝ[X]) :
      HTGeometry.momentFunctional
        (fun m : ℕ => heatGridAliasedTrace (h / n) (t + (m : ℝ) * h)) P =
      c * P.eval r := by
    rw [HTGeometry.momentFunctional_eq_support_sum, Polynomial.eval_eq_sum,
      Polynomial.sum_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [heatGridAliasedTrace_offset hh hn]
    dsimp [c, r]
    ring
  rw [hfunctional, Polynomial.eval_pow]
  exact mul_nonneg hc (sq_nonneg _)

/-- Every finite family of offset grids admits arbitrarily high nonreal aliases. -/
theorem heatGrid_finite_offsets_aliasing (h : {t : ℝ // 0 < t})
    {d : ℕ} (offset : Fin d → ℝ) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ 0 < n ∧
      (heatGridAliasedFrequency ((h : ℝ) / n)).im ≠ 0 ∧
      (heatGridAliasedFrequency ((h : ℝ) / n)).im ^ 2 <
        (heatGridAliasedFrequency ((h : ℝ) / n)).re ∧
      (∀ i, CompleteHankelCone (fun m : ℕ =>
        heatGridAliasedTrace ((h : ℝ) / n) (offset i + (m : ℝ) * (h : ℝ)))) ∧
      heatGridAliasedTrace ((h : ℝ) / n) (((h : ℝ) / n) / 2) < 0 := by
  obtain ⟨n, hnB, hn, hcos⟩ := exists_integer_alias_positive_cos h offset B
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hdelta : 0 < (h : ℝ) / n := div_pos h.property hnR
  have hbase := heatGrid_single_grid_aliasing ⟨(h : ℝ) / n, hdelta⟩
  refine ⟨n, hnB, hn, hbase.1, hbase.2.1, ?_, hbase.2.2.2⟩
  intro i
  apply completeHankelCone_heatGridAliasedTrace_offset h.property hn
  have heq : offset i * (2 * Real.pi / ((h : ℝ) / n)) =
      2 * Real.pi * ((n : ℝ) * (offset i / (h : ℝ))) := by
    field_simp [ne_of_gt h.property, ne_of_gt hnR]
  rw [heq]
  exact hcos i

end

end RHTower
