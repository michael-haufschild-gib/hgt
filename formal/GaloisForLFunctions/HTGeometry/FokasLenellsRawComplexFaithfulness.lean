import GaloisForLFunctions.HTGeometry.FokasLenellsRawComplexCoreGroup

/-!
# Raw multiplier faithfulness and genuine gaps of the entire core

Every core input vanishes on some actual real interval. Every raw derivative
symbol is nonzero off the null singleton at the origin, so all maximal raw
graph outputs and every action on the common core determine their input.
-/

open MeasureTheory Complex Filter Topology Metric Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem gap_cutoff_ae (a : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (rawComplexGraphCutoff a u : ℝ → ℂ) =ᵐ[volume]
      fun z => rawComplexGraphCutoffSymbol a z * u z := by
  unfold rawComplexGraphCutoff
  exact lpBoundedMulCLM_coeFn _ _ _ _

/-- Every actual common-core vector vanishes almost everywhere on a positive real gap. -/
theorem rawComplexEntireCore_exists_zeroGap (u : rawComplexEntireCore) :
    ∃ a : ℝ, ∀ᵐ x : ℝ ∂volume, dist x 0 < Real.exp a → u.val x = 0 := by
  obtain ⟨⟨a,w⟩,hw⟩ := u.property
  change rawComplexGraphCutoff a w = u.val at hw
  refine ⟨a,?_⟩
  have hp := gap_cutoff_ae a w
  rw [hw] at hp
  filter_upwards [hp,(volume : Measure ℝ).ae_ne 0] with x hx hne
  intro hgap
  have habs : |x| < Real.exp a := by simpa only [dist_zero_right,Real.norm_eq_abs] using hgap
  have hnot : x ∉ insert 0 (cutoffPhaseSet a) := by
    rw [mem_insert_iff]
    exact not_or.mpr ⟨hne,not_le.mpr habs⟩
  rw [hx,rawComplexGraphCutoffSymbol,Set.indicator_of_notMem hnot,zero_mul]

/-- Every raw complex derivative symbol is nonzero almost everywhere, at every order and time. -/
theorem rawComplexSymbol_ne_zero_ae (n : ℕ) (τ : ℂ) :
    ∀ᵐ z : ℝ ∂volume, rawComplexSymbol n τ z ≠ 0 := by
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with z hz
  have hf : ((2*z)⁻¹ : ℝ) ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) hz)
  unfold rawComplexSymbol
  exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero
    (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hf)) I_ne_zero)) (Complex.exp_ne_zero _)

/-- All orders of the actual maximal raw graph are faithful in their output coordinate. -/
theorem rawComplexGraphOutput_all_orders_injective (n : ℕ) (τ : ℂ) :
    Function.Injective (rawComplexGraphOutput n τ) := by
  intro p q h
  have hy : p.val.2 = q.val.2 := h
  have hx : p.val.1 = q.val.1 := by
    apply Lp.ext
    filter_upwards [p.property,q.property,rawComplexSymbol_ne_zero_ae n τ] with z hp hq hm
    have he : rawComplexSymbol n τ z * p.val.1 z = rawComplexSymbol n τ z * q.val.1 z := by
      rw [← hp,← hq,hy]
    exact mul_left_cancel₀ hm he
  exact Subtype.ext (Prod.ext hx hy)

/-- Every actual raw core derivative and complex-time action is injective. -/
theorem rawComplexCoreHierarchy_injective (n : ℕ) (τ : ℂ) :
    Function.Injective (rawComplexCoreHierarchy n τ) := by
  intro u v h
  let p : rawComplexGraph n τ :=
    ⟨(u.val,(rawComplexCoreHierarchy n τ u).val),rawComplexCoreHierarchy_mem_graph n τ u⟩
  let q : rawComplexGraph n τ :=
    ⟨(v.val,(rawComplexCoreHierarchy n τ v).val),rawComplexCoreHierarchy_mem_graph n τ v⟩
  have hpq : p = q := rawComplexGraphOutput_all_orders_injective n τ (congrArg Subtype.val h)
  apply Subtype.ext
  exact congrArg (fun p : rawComplexGraph n τ => p.val.1) hpq

end
end GaloisForLFunctions.HTGeometry.FokasLenells
