import GaloisForLFunctions.RHTower.PaperWoldCompositeObservation

/-! # Exact operator-norm continuity domain of the composite exponent family

Positive damping times have compact factors, which upgrade strong continuity
to operator-norm continuity. The only failure in the admitted exponent domain
is its critical endpoint.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

theorem paperWoldCompositeDamping_continuousAt (r : {r : ℝ≥0 // 0 < r}) :
    ContinuousAt paperWoldCompositeDamping r.val := by
  let s : ℝ≥0 := r.val / 2
  have hs : 0 < s := div_pos r.property (by norm_num)
  have hsr : s < r.val := by
    dsimp [s]
    exact half_lt_self r.property
  have hcont : Continuous (fun u : ℝ≥0 =>
      paperWoldCompositeDamping (u - s) ∘L paperWoldCompositeDamping s) :=
    (paperWoldCompositeDamping_comp_compact_continuous
      ⟨paperWoldCompositeDamping s, paperWoldCompositeDamping_compact ⟨s, hs⟩⟩).comp
        (by fun_prop)
  apply hcont.continuousAt.congr
  filter_upwards [lt_mem_nhds hsr] with u hu
  rw [← paperWoldCompositeDamping_add, tsub_add_cancel_of_le hu.le]

/-- Every strict-half exponent is a point of operator-norm continuity in the full admitted domain. -/
theorem paperWoldCompositeOperator_continuousAt (t : {t : ℝ // t < 1 / 2}) :
    ContinuousAt paperWoldCompositeOperator ⟨t.val, t.property.le⟩ := by
  let u : {t : ℝ // t ≤ 1 / 2} := ⟨t.val, t.property.le⟩
  have ht : 0 < paperWoldCompositeDampingTime u := by
    change (0 : ℝ) < 1 - 2 * (t : ℝ)
    linarith [t.property]
  have h := (paperWoldCompositeDamping_continuousAt ⟨paperWoldCompositeDampingTime u, ht⟩).comp
    (f := paperWoldCompositeDampingTime) (x := u) paperWoldCompositeDampingTime_continuous.continuousAt
  change ContinuousAt (fun v => paperWoldCompositeOperator v) u
  simp_rw [paperWoldCompositeOperator_factor]
  exact h.mul (continuousAt_const (y := paperWoldCriticalCompositeOperator))

/-- Exact unconditional classification: the critical endpoint is the only norm discontinuity. -/
theorem paperWoldCompositeOperator_continuousAt_iff (t : {t : ℝ // t ≤ 1 / 2}) :
    ContinuousAt paperWoldCompositeOperator t ↔ (t : ℝ) < 1 / 2 := by
  constructor
  · intro h
    by_contra ht
    have he : t = ⟨1 / 2, le_rfl⟩ :=
      Subtype.ext (le_antisymm t.property (le_of_not_gt ht))
    rw [he] at h
    exact paperWoldCompositeOperator_not_continuousAt_critical h
  · intro ht
    exact paperWoldCompositeOperator_continuousAt ⟨t, ht⟩

end
end RHTower
