import GaloisForLFunctions.RHTower.PaperWoldCompositeOperator
import GaloisForLFunctions.RHTower.PaperWoldEssentialFloor

/-! # A noncompact critical arithmetic operator with infinite paper ideal cost

The complete even-composite matrix has an actual bounded realization. Its
literal finite flat probes retain the positive mass already proved for TT.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators InnerProductSpace ENNReal

theorem paperWoldCriticalCompositeOperator_form (N : ℕ) :
    (inner ℂ (paperWoldFlat N) (paperWoldCriticalCompositeOperator (paperWoldFlat N))).re =
      ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1),
        ∑ j ∈ Finset.range (N + 1), (paperWoldCompositeEntry (1 / 2) n j).re := by
  rw [paperWoldFlat_quadratic]
  simp only [paperWoldCriticalCompositeOperator_single, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum]

theorem paperWoldCriticalCompositeOperator_form_floor (N : ℕ) :
    (1 / 24 : ℝ) ≤ (inner ℂ (paperWoldFlat (N + 1))
      (paperWoldCriticalCompositeOperator (paperWoldFlat (N + 1)))).re := by
  rw [paperWoldCriticalCompositeOperator_form]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show N + 1 + 1 = N + 2 by omega,
    show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]
  exact paperWoldCompositeEntry_normalized_mass ⟨1 / 2, le_rfl⟩ N

/-- The positive gap is attained by an actual bounded arithmetic operator. -/
theorem paperWoldCriticalCompositeOperator_norm_sub_compact_floor
    (K : compactOperatorStarAlgebra PaperWoldHistory) :
    (1 / 24 : ℝ) ≤ ‖paperWoldCriticalCompositeOperator - K.val‖ := by
  have hk := (Complex.continuous_re.tendsto 0).comp
    ((paperWoldFlat_compact_form_tendsto K).comp (tendsto_add_atTop_nat 1))
  simp only [Function.comp_def, Complex.zero_re] at hk
  have hl := (tendsto_const_nhds (x := (1 / 24 : ℝ))).sub hk
  rw [sub_zero] at hl
  apply le_of_tendsto hl
  apply Eventually.of_forall
  intro N
  let u := paperWoldFlat (N + 1)
  have hu : ‖u‖ = 1 := paperWoldFlat_norm _
  have hf : (1 / 24 : ℝ) ≤ (inner ℂ u (paperWoldCriticalCompositeOperator u)).re :=
    paperWoldCriticalCompositeOperator_form_floor N
  calc
    (1 / 24 : ℝ) - (inner ℂ u (K.val u)).re ≤
        (inner ℂ u ((paperWoldCriticalCompositeOperator - K.val) u)).re := by
      simp only [sub_apply, inner_sub_right, Complex.sub_re]
      linarith
    _ ≤ ‖inner ℂ u ((paperWoldCriticalCompositeOperator - K.val) u)‖ := Complex.re_le_norm _
    _ ≤ ‖u‖ * ‖(paperWoldCriticalCompositeOperator - K.val) u‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖paperWoldCriticalCompositeOperator - K.val‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left ((paperWoldCriticalCompositeOperator - K.val).le_opNorm u)
        (norm_nonneg _)
    _ = _ := by rw [hu, mul_one, one_mul]

theorem paperWoldCriticalCompositeOperator_not_compact :
    ¬ IsCompactOperator paperWoldCriticalCompositeOperator := by
  intro h
  have hf := paperWoldCriticalCompositeOperator_norm_sub_compact_floor
    ⟨paperWoldCriticalCompositeOperator, h⟩
  norm_num at hf

theorem paperWoldCriticalCompositeOperator_compactIdealDistance_floor :
    (1 / 24 : ℝ) ≤ compactIdealDistance paperWoldCriticalCompositeOperator :=
  le_compactIdealDistance _ _ fun K hK =>
    paperWoldCriticalCompositeOperator_norm_sub_compact_floor ⟨K, hK⟩

theorem paperWoldCriticalCompositeOperator_traceCost :
    compactOperatorTraceCost PaperWoldHistory paperWoldCriticalCompositeOperator = ∞ :=
  (compactOperatorTraceCost_eq_top_iff _).mpr paperWoldCriticalCompositeOperator_not_compact

theorem paperWoldCriticalCompositeOperator_add_compact_traceCost
    (K : compactOperatorStarAlgebra PaperWoldHistory) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldCriticalCompositeOperator + K.val) = ∞ := by
  rw [compactOperatorTraceCost_add_compact, paperWoldCriticalCompositeOperator_traceCost]

end
end RHTower
