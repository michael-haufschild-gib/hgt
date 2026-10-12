import GaloisForLFunctions.RHTower.PaperWoldCompactDomain

/-! # A quantitative compact-ideal gap for every admitted full Wold operator

At and above the half power, the literal composite probes retain a positive
operator-norm distance from every compact correction.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace

theorem paperWoldRealization_norm_sub_compact_floor
    (t : {t : ℝ // 1 / 2 ≤ t}) (T : PaperWoldRealization t)
    (K : compactOperatorStarAlgebra PaperWoldHistory) :
    (1 / 24 : ℝ) ≤ ‖T.val - K.val‖ := by
  have hk := (Complex.continuous_re.tendsto 0).comp
    ((paperWoldCompositeFlat_compact_form_tendsto K).comp (tendsto_add_atTop_nat 1))
  simp only [Function.comp_def, Complex.zero_re] at hk
  have hl := (tendsto_const_nhds (x := (1 / 24 : ℝ))).sub hk
  rw [sub_zero] at hl
  apply le_of_tendsto hl
  apply Eventually.of_forall
  intro N
  let u := paperWoldCompositeFlat (N + 1)
  have hu : ‖u‖ = 1 := paperWoldCompositeFlat_norm _
  have hf : (1 / 24 : ℝ) ≤ (inner ℂ u (T.val u)).re :=
    paperWoldRealization_composite_floor t T N
  calc
    (1 / 24 : ℝ) - (inner ℂ u (K.val u)).re ≤
        (inner ℂ u ((T.val - K.val) u)).re := by
      simp only [sub_apply, inner_sub_right, Complex.sub_re]
      linarith
    _ ≤ ‖inner ℂ u ((T.val - K.val) u)‖ := Complex.re_le_norm _
    _ ≤ ‖u‖ * ‖(T.val - K.val) u‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖T.val - K.val‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left ((T.val - K.val).le_opNorm u) (norm_nonneg _)
    _ = _ := by rw [hu, mul_one, one_mul]

theorem paperWoldRealization_compactIdealDistance_floor
    (t : {t : ℝ // 1 / 2 ≤ t}) (T : PaperWoldRealization t) :
    (1 / 24 : ℝ) ≤ compactIdealDistance T.val :=
  le_compactIdealDistance _ _ fun K hK =>
    paperWoldRealization_norm_sub_compact_floor t T ⟨K, hK⟩

/-- The distance to compact operators vanishes on precisely the admitted strict-half domain. -/
theorem paperWoldRealization_compactIdealDistance_zero_iff (t : ℝ) (T : PaperWoldRealization t) :
    compactIdealDistance T.val = 0 ↔ t < 1 / 2 := by
  constructor
  · intro h
    by_contra ht
    have hf := paperWoldRealization_compactIdealDistance_floor ⟨t, le_of_not_gt ht⟩ T
    rw [h] at hf
    norm_num at hf
  · intro ht
    exact compactIdealDistance_eq_zero_of_isCompactOperator _
      ((paperWoldRealization_compact_iff t T).mpr ht)

/-- Every finite observation retains exactly the original entries in its square. -/
def paperWoldFiniteCutoff (t : ℝ) (s : Finset ℕ) : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  HilbertSchmidt.toOperator (paperWoldDirectedKernel_finite_isHS t s)

theorem paperWoldFiniteCutoff_single (t : ℝ) (s : Finset ℕ) (n j : ℕ) :
    paperWoldFiniteCutoff t s (lp.single 2 j (1 : ℂ)) n =
      if n ∈ s ∧ j ∈ s then paperWoldDirectedKernel t (n, j) else 0 :=
  HilbertSchmidt.toOperator_single (paperWoldDirectedKernel_finite_isHS t s) n j

theorem paperWoldFiniteCutoff_compact (t : ℝ) (s : Finset ℕ) :
    IsCompactOperator (paperWoldFiniteCutoff t s) :=
  (HilbertSchmidt.isHilbertSchmidt_toOperator (paperWoldDirectedKernel_finite_isHS t s)).isCompactOperator

theorem paperWoldFiniteCutoff_traceCost (t : ℝ) (s : Finset ℕ) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldFiniteCutoff t s) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperWoldFiniteCutoff_compact t s)

/-- Every finite cutoff has zero ideal cost but misses any admitted critical operator by a fixed gap. -/
theorem paperWoldFiniteCutoff_norm_gap (t : {t : ℝ // 1 / 2 ≤ t})
    (T : PaperWoldRealization t) (s : Finset ℕ) :
    (1 / 24 : ℝ) ≤ ‖T.val - paperWoldFiniteCutoff t s‖ :=
  paperWoldRealization_norm_sub_compact_floor t T
    ⟨paperWoldFiniteCutoff t s, paperWoldFiniteCutoff_compact t s⟩

end
end RHTower
