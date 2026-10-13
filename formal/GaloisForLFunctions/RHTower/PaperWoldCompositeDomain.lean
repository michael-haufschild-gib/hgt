import GaloisForLFunctions.RHTower.PaperWoldCompositeGrowth
import GaloisForLFunctions.RHTower.PaperWoldCompositeCutoffs

/-! # Exact bounded and compact domains of the literal composite matrix

Bounded admission includes the half-power endpoint; compact and Hilbert–Schmidt
admission exclude it. Every statement retains the original composite entries.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

def PaperWoldCompositeRealization (t : ℝ) :=
  {T : PaperWoldHistory →L[ℂ] PaperWoldHistory // HasLpMatrix T (paperWoldCompositeEntry t)}

theorem paperWoldCompositeRealization_unique (t : ℝ) (T S : PaperWoldCompositeRealization t) :
    T = S := Subtype.ext (HasLpMatrix.ext T.property S.property)

def paperWoldAdmittedCompositeRealization (t : {t : ℝ // t ≤ 1 / 2}) :
    PaperWoldCompositeRealization t :=
  ⟨paperWoldCompositeOperator t, paperWoldCompositeOperator_matrix t⟩

theorem paperWoldCompositeRealization_not_nonempty (t : {t : ℝ // 1 / 2 < t}) :
    ¬ Nonempty (PaperWoldCompositeRealization t) := by
  rintro ⟨T⟩
  obtain ⟨N, hN, hlarge⟩ := ((eventually_ge_atTop 1).and
    ((paperWoldComposite_power_atTop t).eventually (eventually_gt_atTop ‖T.val‖))).exists
  have hl := paperWoldComposite_rectangle_norm_lower t N hN T.val
    (fun n _ j _ => T.property n j)
  exact (not_lt_of_ge hl) hlarge

/-- Exact unconditional bounded-admission classification over every real exponent. -/
theorem paperWoldComposite_exists_bounded_realization_iff (t : ℝ) :
    Nonempty (PaperWoldCompositeRealization t) ↔ t ≤ 1 / 2 := by
  constructor
  · intro h
    by_contra ht
    exact paperWoldCompositeRealization_not_nonempty ⟨t, lt_of_not_ge ht⟩ h
  · intro ht
    exact ⟨paperWoldAdmittedCompositeRealization ⟨t, ht⟩⟩

theorem paperWoldCompositeRealization_compact_iff (t : ℝ) (T : PaperWoldCompositeRealization t) :
    IsCompactOperator T.val ↔ t < 1 / 2 := by
  constructor
  · intro hT
    by_contra ht
    have hle := (paperWoldComposite_exists_bounded_realization_iff t).mp ⟨T⟩
    have he : t = 1 / 2 := le_antisymm hle (le_of_not_gt ht)
    subst t
    have heT := HasLpMatrix.ext T.property paperWoldCriticalCompositeOperator_matrix
    rw [heT] at hT
    exact paperWoldCriticalCompositeOperator_not_compact hT
  · intro ht
    have he := paperWoldCompositeRealization_unique t T
      (paperWoldAdmittedCompositeRealization ⟨t, ht.le⟩)
    rw [he]
    exact paperWoldCompositeOperator_compact ⟨t, ht⟩

/-- Compact admission has a strictly smaller domain than bounded admission. -/
theorem paperWoldComposite_exists_compact_realization_iff (t : ℝ) :
    (∃ T : PaperWoldCompositeRealization t, IsCompactOperator T.val) ↔ t < 1 / 2 := by
  constructor
  · rintro ⟨T, hT⟩
    exact (paperWoldCompositeRealization_compact_iff t T).mp hT
  · intro ht
    exact ⟨paperWoldAdmittedCompositeRealization ⟨t, ht.le⟩, paperWoldCompositeOperator_compact ⟨t, ht⟩⟩

theorem paperWoldComposite_exists_noncompact_realization_iff (t : ℝ) :
    (∃ T : PaperWoldCompositeRealization t, ¬ IsCompactOperator T.val) ↔ t = 1 / 2 := by
  constructor
  · rintro ⟨T, hT⟩
    have hle := (paperWoldComposite_exists_bounded_realization_iff t).mp ⟨T⟩
    exact le_antisymm hle (le_of_not_gt (fun ht => hT
      ((paperWoldCompositeRealization_compact_iff t T).mpr ht)))
  · rintro rfl
    exact ⟨⟨paperWoldCriticalCompositeOperator, paperWoldCriticalCompositeOperator_matrix⟩,
      paperWoldCriticalCompositeOperator_not_compact⟩

theorem paperWoldCompositeEntry_isHS_iff (t : ℝ) :
    HilbertSchmidt.IsHS (fun q : ℕ × ℕ => paperWoldCompositeEntry t q.1 q.2) ↔ t < 1 / 2 := by
  constructor
  · intro h
    apply (paperWoldComposite_exists_compact_realization_iff t).mp
    exact ⟨⟨HilbertSchmidt.toOperator h, fun n j => HilbertSchmidt.toOperator_single h n j⟩,
      (HilbertSchmidt.isHilbertSchmidt_toOperator h).isCompactOperator⟩
  · intro ht
    exact paperWoldCompositeEntry_isHS ⟨t, ht⟩

theorem paperWoldCompositeRealization_traceCost (t : ℝ) (T : PaperWoldCompositeRealization t) :
    compactOperatorTraceCost PaperWoldHistory T.val = if t < 1 / 2 then 0 else ∞ := by
  split_ifs with ht
  · exact (compactOperatorTraceCost_eq_zero_iff _).mpr
      ((paperWoldCompositeRealization_compact_iff t T).mpr ht)
  · exact (compactOperatorTraceCost_eq_top_iff _).mpr
      (fun h => ht ((paperWoldCompositeRealization_compact_iff t T).mp h))

/-- Ideal cost for the actually constructed complete family, with no realization hypothesis. -/
theorem paperWoldCompositeOperator_traceCost (t : {t : ℝ // t ≤ 1 / 2}) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldCompositeOperator t) =
      if (t : ℝ) < 1 / 2 then 0 else ∞ :=
  paperWoldCompositeRealization_traceCost t (paperWoldAdmittedCompositeRealization t)

/-- The all-exponent finite family agrees exactly with the previously constructed endpoint cutoffs. -/
theorem paperWoldCompositeFiniteCutoff_critical (N : ℕ) :
    paperWoldCompositeFiniteCutoff (1 / 2) (Finset.range N) = paperWoldCriticalCompositeCutoff N := by
  apply HasLpMatrix.ext (K := fun n j =>
    if n < N ∧ j < N then paperWoldCompositeEntry (1 / 2) n j else 0)
  · intro n j
    simp only [lpBasisVec, paperWoldCompositeFiniteCutoff_single, Finset.mem_range]
  · exact paperWoldCriticalCompositeCutoff_single N

end
end RHTower
