import GaloisForLFunctions.RHTower.PaperWoldCompositeIdeal

/-! # Complete composite operators throughout the closed half-power domain

Every exponent at most one half has a complete Hardy-dominated realization.
Below the boundary the literal composite matrix is Hilbert–Schmidt.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

theorem paperWoldCompositeEntry_formula (t : ℝ) (n j : ℕ) :
    paperWoldCompositeEntry t n j = if n < j then
      (((2 * (n : ℝ) + 3) ^ (2 * t) * (-xiHeatCassiniWoldNatIncrement (2 * n + 2)) *
        (-xiHeatCassiniWoldNatIncrement (2 * j + 2)) : ℝ) : ℂ) else 0 := by
  unfold paperWoldCompositeEntry paperWoldDirectedKernel
  by_cases h : n < j
  · rw [if_pos h, if_pos (by omega : 2 * n + 2 < 2 * j + 2)]
    push_cast
    rw [show 2 * (n : ℝ) + 2 + 1 = 2 * n + 3 by ring]
    ring
  · rw [if_neg h, if_neg (by omega : ¬ 2 * n + 2 < 2 * j + 2)]

theorem paperWoldCompositeEntry_norm_mono (s t : ℝ) (hst : s ≤ t) (n j : ℕ) :
    ‖paperWoldCompositeEntry s n j‖ ≤ ‖paperWoldCompositeEntry t n j‖ := by
  rw [paperWoldCompositeEntry_norm_eq_re, paperWoldCompositeEntry_norm_eq_re,
    paperWoldCompositeEntry_formula, paperWoldCompositeEntry_formula]
  split_ifs
  · simp only [Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le
          (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith))
        (neg_nonneg.mpr (paperWold_even_composite_increment_neg n).le))
      (neg_nonneg.mpr (paperWold_even_composite_increment_neg j).le)
  · exact le_rfl

def paperWoldCompositeKernel (t : {t : ℝ // t ≤ 1 / 2}) : PaperHardy.Kernel where
  entry := paperWoldCompositeEntry t
  bound n j := (paperWoldCompositeEntry_norm_mono t (1 / 2) t.property n j).trans
    (paperWoldCompositeEntry_critical_bound n j)

/-- Actual complete operator, without a bounded-realization premise. -/
def paperWoldCompositeOperator (t : {t : ℝ // t ≤ 1 / 2}) :
    PaperWoldHistory →L[ℂ] PaperWoldHistory := (paperWoldCompositeKernel t).toOperator

theorem paperWoldCompositeOperator_apply (t : {t : ℝ // t ≤ 1 / 2})
    (f : PaperWoldHistory) (n : ℕ) :
    paperWoldCompositeOperator t f n = ∑' j, paperWoldCompositeEntry t n j * f j := rfl

theorem paperWoldCompositeOperator_single (t : {t : ℝ // t ≤ 1 / 2}) (n j : ℕ) :
    paperWoldCompositeOperator t (lp.single 2 j (1 : ℂ)) n = paperWoldCompositeEntry t n j :=
  (paperWoldCompositeKernel t).toOperator_single n j

theorem paperWoldCompositeOperator_matrix (t : {t : ℝ // t ≤ 1 / 2}) :
    HasLpMatrix (paperWoldCompositeOperator t) (paperWoldCompositeEntry t) :=
  paperWoldCompositeOperator_single t

theorem paperWoldCompositeOperator_norm_le (t : {t : ℝ // t ≤ 1 / 2}) :
    ‖paperWoldCompositeOperator t‖ ≤ 5 := (paperWoldCompositeKernel t).norm_toOperator_le

theorem paperWoldCompositeOperator_critical :
    paperWoldCompositeOperator ⟨1 / 2, le_rfl⟩ = paperWoldCriticalCompositeOperator :=
  HasLpMatrix.ext (paperWoldCompositeOperator_matrix _) paperWoldCriticalCompositeOperator_matrix

theorem paperWoldCompositeEntry_isHS (t : {t : ℝ // t < 1 / 2}) :
    HilbertSchmidt.IsHS (fun q : ℕ × ℕ => paperWoldCompositeEntry t q.1 q.2) := by
  have hinj : Function.Injective (fun q : ℕ × ℕ => (2 * q.1 + 2, 2 * q.2 + 2)) := by
    intro a b hab
    have h1 := congrArg Prod.fst hab
    have h2 := congrArg Prod.snd hab
    apply Prod.ext <;> dsimp at * <;> omega
  exact ((paperWoldDirectedKernel_isHS_iff t).mpr t.property).comp_injective hinj

theorem paperWoldCompositeOperator_compact (t : {t : ℝ // t < 1 / 2}) :
    IsCompactOperator (paperWoldCompositeOperator ⟨t, t.property.le⟩) := by
  have he : paperWoldCompositeOperator ⟨t, t.property.le⟩ =
      HilbertSchmidt.toOperator (paperWoldCompositeEntry_isHS t) :=
    HasLpMatrix.ext (paperWoldCompositeOperator_matrix _)
      (fun n j => HilbertSchmidt.toOperator_single (paperWoldCompositeEntry_isHS t) n j)
  rw [he]
  exact (HilbertSchmidt.isHilbertSchmidt_toOperator (paperWoldCompositeEntry_isHS t)).isCompactOperator

end
end RHTower
