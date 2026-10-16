import GaloisForLFunctions.HTGeometry.BoundedVariationNormAlgebra

/-! # Integrable primitive increments pay whole-line variation -/

noncomputable section
open MeasureTheory Set Filter

namespace GaloisForLFunctions.HTGeometry

theorem eVariationOn_le_integral_norm_of_integral_eq_sub {f g : ℝ → ℝ}
    (hg : Integrable g) (hfg : ∀ a b, (∫ t in a..b, g t) = f b - f a) :
    eVariationOn f univ ≤ ENNReal.ofReal (∫ t, ‖g t‖) := by
  apply eVariationOn_le_of_norm_partitions
  intro n u hu _
  calc
    _ ≤ ∑ i ∈ Finset.range n, ∫ t in u i..u (i + 1), ‖g t‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← hfg]
      exact intervalIntegral.norm_integral_le_integral_norm (hu (Nat.le_succ i))
    _ = ∫ t in u 0..u n, ‖g t‖ :=
      intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => hg.norm.intervalIntegrable)
    _ ≤ ∫ t, ‖g t‖ := by
      rw [intervalIntegral.integral_of_le (hu (Nat.zero_le n))]
      exact setIntegral_le_integral hg.norm (Eventually.of_forall fun _ => norm_nonneg _)

theorem boundedVariationOn_of_integral_eq_sub {f g : ℝ → ℝ}
    (hg : Integrable g) (hfg : ∀ a b, (∫ t in a..b, g t) = f b - f a) :
    BoundedVariationOn f univ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (eVariationOn_le_integral_norm_of_integral_eq_sub hg hfg)

theorem boundedVariationOn_integral_primitive {g : ℝ → ℝ} (hg : Integrable g) (a : ℝ) :
    BoundedVariationOn (fun x => ∫ t in a..x, g t) univ := by
  apply boundedVariationOn_of_integral_eq_sub hg
  intro x y
  have h := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (a := a) (b := x)) (hg.intervalIntegrable (a := x) (b := y))
  linarith

theorem boundedVariationOn_of_contDiff_compact {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) : BoundedVariationOn f univ := by
  have hi : Integrable (deriv f) :=
    (hf.continuous_deriv le_rfl).integrable_of_hasCompactSupport hc.deriv
  apply boundedVariationOn_of_integral_eq_sub hi
  intro a b
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => (hf.differentiable (by norm_num) x).hasDerivAt) hi.intervalIntegrable

end GaloisForLFunctions.HTGeometry
