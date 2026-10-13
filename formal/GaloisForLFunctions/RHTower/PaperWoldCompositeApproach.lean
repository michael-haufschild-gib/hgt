import GaloisForLFunctions.RHTower.PaperWoldCompositeParameter

/-! # A literal exponent approach with a compact-ideal jump

The exponents `1/2 - 1/(N+1)` give complete compact arithmetic operators.
They converge on every square-summable history to the original critical
noncompact operator, while their operator-norm gap never falls below `1/24`.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

def paperWoldCompositeApproachExponent (N : ℕ) : {t : ℝ // t < 1 / 2} :=
  ⟨1 / 2 - ((N : ℝ) + 1)⁻¹, by
    have h : 0 < ((N : ℝ) + 1)⁻¹ := by positivity
    linarith⟩

def paperWoldCompositeApproachParameter (N : ℕ) : {t : ℝ // t ≤ 1 / 2} :=
  ⟨paperWoldCompositeApproachExponent N, (paperWoldCompositeApproachExponent N).property.le⟩

def paperWoldCompositeApproach (N : ℕ) : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  paperWoldCompositeOperator (paperWoldCompositeApproachParameter N)

theorem paperWoldCompositeApproach_single (N n j : ℕ) :
    paperWoldCompositeApproach N (lp.single 2 j (1 : ℂ)) n =
      paperWoldCompositeEntry (1 / 2 - ((N : ℝ) + 1)⁻¹) n j :=
  paperWoldCompositeOperator_single (paperWoldCompositeApproachParameter N) n j

theorem paperWoldCompositeApproachParameter_tendsto :
    Tendsto paperWoldCompositeApproachParameter atTop (𝓝 ⟨1 / 2, le_rfl⟩) := by
  apply tendsto_subtype_rng.mpr
  have hi := tendsto_inv_atTop_zero.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub hi
  simpa only [paperWoldCompositeApproachParameter, paperWoldCompositeApproachExponent,
    Function.comp_def, sub_zero] using h

theorem paperWoldCompositeApproach_compact (N : ℕ) :
    IsCompactOperator (paperWoldCompositeApproach N) :=
  paperWoldCompositeOperator_compact (paperWoldCompositeApproachExponent N)

/-- Full-history convergence uses the literal exponent family, with no finite truncation. -/
theorem paperWoldCompositeApproach_strong_tendsto (f : PaperWoldHistory) :
    Tendsto (fun N => paperWoldCompositeApproach N f) atTop
      (𝓝 (paperWoldCriticalCompositeOperator f)) := by
  have h := ((paperWoldCompositeOperator_strong_continuous f).tendsto ⟨1 / 2, le_rfl⟩).comp
    paperWoldCompositeApproachParameter_tendsto
  simpa only [Function.comp_def, paperWoldCompositeApproach, paperWoldCompositeOperator_critical] using h

theorem paperWoldCompositeApproach_norm_gap (N : ℕ) :
    (1 / 24 : ℝ) ≤ ‖paperWoldCriticalCompositeOperator - paperWoldCompositeApproach N‖ :=
  paperWoldCompositeOperator_critical_norm_gap (paperWoldCompositeApproachExponent N)

/-- The exact compact quotient is constant along all differences from the critical limit. -/
theorem paperWoldCompositeApproach_compactIdealDistance (N : ℕ) :
    compactIdealDistance (paperWoldCriticalCompositeOperator - paperWoldCompositeApproach N) =
      compactIdealDistance paperWoldCriticalCompositeOperator :=
  paperWoldCompositeOperator_critical_compactIdealDistance (paperWoldCompositeApproachExponent N)

theorem paperWoldCompositeApproach_traceCost (N : ℕ) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldCompositeApproach N) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperWoldCompositeApproach_compact N)

theorem paperWoldCompositeApproach_not_norm_tendsto :
    ¬ Tendsto paperWoldCompositeApproach atTop (𝓝 paperWoldCriticalCompositeOperator) := by
  intro h
  have hz : Tendsto (fun N => ‖paperWoldCriticalCompositeOperator - paperWoldCompositeApproach N‖)
      atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds (x := paperWoldCriticalCompositeOperator)).sub h).norm
  have hb : (1 / 24 : ℝ) ≤ 0 :=
    ge_of_tendsto hz (Eventually.of_forall paperWoldCompositeApproach_norm_gap)
  norm_num at hb

/-- Strong continuity of the complete family cannot be upgraded to norm continuity at the endpoint. -/
theorem paperWoldCompositeOperator_not_continuousAt_critical :
    ¬ ContinuousAt paperWoldCompositeOperator ⟨1 / 2, le_rfl⟩ := by
  intro h
  have ht := h.tendsto.comp paperWoldCompositeApproachParameter_tendsto
  rw [paperWoldCompositeOperator_critical] at ht
  exact paperWoldCompositeApproach_not_norm_tendsto ht

end
end RHTower
