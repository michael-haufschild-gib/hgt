import GaloisForLFunctions.RHTower.SmoothAFEZetaSquarePrimalAffineMeanSquare

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

theorem measurable_smoothAFEZetaSquarePrimalSourceField (N : ℕ) :
    Measurable (smoothAFEZetaSquarePrimalSourceField N) := by
  unfold smoothAFEZetaSquarePrimalSourceField
  apply Measurable.tsum
  intro n
  letI : NeZero (n + 1 : ℂ) := ⟨by
    exact_mod_cast (show n + 1 ≠ 0 by omega)⟩
  exact (measurable_const.mul
    ((continuous_const_cpow (n + 1 : ℂ)).comp (by
      unfold linePt
      fun_prop)).measurable).mul measurable_const

theorem integrableOn_normSq_smoothAFEZetaSquarePrimalSourceField
    {N : ℕ} (hN : 4 ≤ N) :
    IntegrableOn (fun t : ℝ => ‖smoothAFEZetaSquarePrimalSourceField N t‖ ^ 2)
      (Set.Icc (N : ℝ) (2 * N : ℝ)) := by
  let a : ℕ → ℂ := smoothAFEZetaSquarePrimalNatCoefficient N 0
  have habs : Summable (fun k : ℕ => ‖a k‖) :=
    (summable_smoothAFEZetaSquarePrimalNatCoefficient_affine_masses hN 0).1
  let M : ℝ := ∑' k : ℕ, ‖a k‖
  have hM : 0 ≤ M := tsum_nonneg fun _ => norm_nonneg _
  have hbound : ∀ t : ℝ, ‖smoothAFEZetaSquarePrimalSourceField N t‖ ≤ M := by
    intro t
    have heq := smoothAFEZetaSquarePrimalLSeries_eq_sourceField hN 0 t
    simp only [sub_zero] at heq
    rw [← heq]
    let s : ℂ := (t : ℝ) * I
    have hterm : Summable (fun k : ℕ => LSeries.term a s k) := by
      rw [← summable_norm_iff]
      refine habs.congr (fun k => ?_)
      rw [LSeries.norm_term_eq]
      by_cases hk : k = 0
      · simp [hk, a]
      · simp [hk, s]
    calc
      ‖LSeries (smoothAFEZetaSquarePrimalNatCoefficient N 0) ((t : ℝ) * I)‖ =
          ‖∑' k : ℕ, LSeries.term a s k‖ := by rfl
      _ ≤ ∑' k : ℕ, ‖LSeries.term a s k‖ := norm_tsum_le_tsum_norm hterm.norm
      _ = ∑' k : ℕ, ‖a k‖ := by
        apply tsum_congr
        intro k
        rw [LSeries.norm_term_eq]
        by_cases hk : k = 0
        · simp [hk, a]
        · simp [hk, s]
      _ = M := rfl
  refine MeasureTheory.Measure.integrableOn_of_bounded
    (M := M ^ 2) isCompact_Icc.measure_lt_top.ne
    ((measurable_smoothAFEZetaSquarePrimalSourceField N).norm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbound t) 2

end RHTower
