import GaloisForLFunctions.HTGeometry.FokasLenellsCausalHardyOrientation
import GaloisForLFunctions.RHTower.FokasLenellsCauchyCoreEncoding

/-!
# Sharp causal boundedness gate for the exact Cauchy-encoded complex group

The algebraic group on the actual encoded spectral-gap core is bounded in its
inherited data norm exactly at nonnegative real times. At those times its
literal value is the negative Cauchy compression of the evolved datum, giving
a contraction. A putative bound at another real time would force full Hardy
invariance by core cutoff approximation, contradicting the concrete negative
time Cauchy feature. Existing raw bounds exclude nonreal complex times.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The full signed Cauchy projection satisfies the exact causal compression identity. -/
theorem negativeCauchy_causal_sandwich (t : ℝ≥0) (u : SoninL2) :
    negativeCauchy (evolution t (negativeCauchy u)) = -negativeCauchy (evolution t u) := by
  have hker : u + negativeCauchy u ∈ hardyL2 := by
    apply (negativeCauchy_eq_zero_iff _).1
    rw [map_add,negativeCauchy_square,add_neg_cancel]
  have hh := evolution_nonnegative_mem_hardy t ⟨u+negativeCauchy u,hker⟩
  have hc := (negativeCauchy_eq_zero_iff _).2 hh
  change negativeCauchy (evolution t (u+negativeCauchy u)) = 0 at hc
  rw [map_add,map_add] at hc
  exact eq_neg_of_add_eq_zero_right hc

/-- At nonnegative real time, the encoded group equals a literal bounded Cauchy compression. -/
theorem rawComplexCauchyCoreGroup_nonnegative_value (t : ℝ≥0) (y : rawComplexCauchyCoreRange) :
    (rawComplexCauchyCoreGroup ((t:ℝ):ℂ) y).val = -negativeCauchy (evolution t y.val) := by
  obtain ⟨u,rfl⟩ := rawComplexCauchyCoreEncoding.surjective y
  rw [rawComplexCauchyCoreGroup_transport,rawComplexCauchyCoreHierarchy_zero_ofReal,
    rawComplexCauchyCoreEncoding_apply]
  change negativeCauchy (evolution t u.val) = -negativeCauchy (evolution t (negativeCauchy u.val))
  rw [negativeCauchy_causal_sandwich,neg_neg]

/-- The exact encoded group contracts the original data norm for every nonnegative real time. -/
theorem rawComplexCauchyCoreGroup_nonnegative_bound (t : ℝ≥0) (y : rawComplexCauchyCoreRange) :
    ‖rawComplexCauchyCoreGroup ((t:ℝ):ℂ) y‖ ≤ ‖y‖ := by
  change ‖(rawComplexCauchyCoreGroup ((t:ℝ):ℂ) y).val‖ ≤ ‖y.val‖
  rw [rawComplexCauchyCoreGroup_nonnegative_value,norm_neg]
  exact (negativeCauchy_bound (evolution t y.val)).trans_eq (norm_evolution t y.val)

private theorem encoded_bound_forces_hardy (t B : ℝ)
    (hB : ∀ u : rawComplexEntireCore, ‖negativeCauchy (evolution t u.val)‖ ≤
      B * ‖negativeCauchy u.val‖) :
    ∀ u : UpperHardyL2, evolution t u.val ∈ hardyL2 := by
  intro u
  apply (negativeCauchy_eq_zero_iff _).1
  have hleft : Tendsto (fun a => ‖negativeCauchy (evolution t (rawComplexGraphCutoff a u.val))‖)
      atBot (𝓝 ‖negativeCauchy (evolution t u.val)‖) := by
    exact (negativeCauchy.continuous.continuousAt.tendsto.comp
      ((evolution t).continuous.continuousAt.tendsto.comp (rawComplexGraphCutoff_tendsto u.val))).norm
  have hright : Tendsto (fun a => ‖negativeCauchy (rawComplexGraphCutoff a u.val)‖)
      atBot (𝓝 (0:ℝ)) := by
    have hh := (negativeCauchy.continuous.continuousAt.tendsto.comp
      (rawComplexGraphCutoff_tendsto u.val)).norm
    simpa only [Function.comp_apply,(negativeCauchy_eq_zero_iff _).2 u.property,norm_zero] using hh
  have hh : ‖negativeCauchy (evolution t u.val)‖ ≤ B * 0 :=
    le_of_tendsto_of_tendsto hleft (tendsto_const_nhds.mul hright)
      (Eventually.of_forall (fun a => hB ⟨rawComplexGraphCutoff a u.val,⟨(a,u.val),rfl⟩⟩))
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa only [mul_zero] using hh) (norm_nonneg _)

/-- The complete boundedness gate in encoded L² norm: precisely nonnegative real complex times. -/
theorem rawComplexCauchyCoreGroup_bounded_iff (τ : ℂ) :
    (∃ B : ℝ, ∀ y : rawComplexCauchyCoreRange, ‖rawComplexCauchyCoreGroup τ y‖ ≤ B * ‖y‖) ↔
      τ.im = 0 ∧ 0 ≤ τ.re := by
  constructor
  · rintro ⟨B,hB⟩
    have hB' : ∀ y : rawComplexCauchyCoreRange, ‖rawComplexCauchyCoreGroup τ y‖ ≤ max B 0 * ‖y‖ := by
      intro y
      exact (hB y).trans (mul_le_mul_of_nonneg_right (le_max_left B 0) (norm_nonneg y))
    have hcore : ∀ u : rawComplexEntireCore, ‖rawComplexCauchyCoreHierarchy 0 τ u‖ ≤
        max B 0 * ‖negativeCauchy u.val‖ := by
      intro u
      have h := hB' (rawComplexCauchyCoreEncoding u)
      change ‖(rawComplexCauchyCoreGroup τ (rawComplexCauchyCoreEncoding u)).val‖ ≤
        max B 0 * ‖(rawComplexCauchyCoreEncoding u).val‖ at h
      simpa only [rawComplexCauchyCoreGroup_transport,rawComplexCauchyCoreEncoding_apply] using h
    have hi : τ.im = 0 := ((rawComplexCauchyCoreHierarchy_bounded_iff 0 τ).1
      ⟨max B 0,fun u => (hcore u).trans
        (mul_le_mul_of_nonneg_left (negativeCauchy_bound u.val) (le_max_right B 0))⟩).2
    refine ⟨hi,?_⟩
    have he : τ = (τ.re:ℂ) := by apply Complex.ext <;> simp [hi]
    apply (evolution_hardy_invariance_iff τ.re).1
    apply encoded_bound_forces_hardy τ.re (max B 0)
    intro u
    have h := hcore u
    rw [he,rawComplexCauchyCoreHierarchy_zero_ofReal] at h
    exact h
  · rintro ⟨hi,hr⟩
    have he : τ = (τ.re:ℂ) := by apply Complex.ext <;> simp [hi]
    refine ⟨1,fun y => ?_⟩
    rw [he,one_mul]
    exact rawComplexCauchyCoreGroup_nonnegative_bound ⟨τ.re,hr⟩ y

/-- Exact encoded-data continuity holds at precisely the same causal complex-time gate. -/
theorem rawComplexCauchyCoreGroup_continuous_iff (τ : ℂ) :
    Continuous (rawComplexCauchyCoreGroup τ) ↔ τ.im = 0 ∧ 0 ≤ τ.re := by
  constructor
  · intro hc
    let T : rawComplexCauchyCoreRange →L[ℂ] rawComplexCauchyCoreRange :=
      ⟨(rawComplexCauchyCoreGroup τ).toLinearMap,hc⟩
    exact (rawComplexCauchyCoreGroup_bounded_iff τ).1 ⟨‖T‖,fun y => T.le_opNorm y⟩
  · intro h
    exact ((rawComplexCauchyCoreGroup τ).toLinearMap.mkContinuousOfExistsBound
      ((rawComplexCauchyCoreGroup_bounded_iff τ).2 h)).continuous

/-- Every nonreal time and every negative real time amplifies encoded data beyond every norm bound. -/
theorem rawComplexCauchyCoreGroup_unbounded_growth_iff (τ : ℂ) :
    (∀ B : ℝ, ∃ y : rawComplexCauchyCoreRange, B * ‖y‖ < ‖rawComplexCauchyCoreGroup τ y‖) ↔
      τ.im ≠ 0 ∨ τ.re < 0 := by
  simpa only [not_exists,not_forall,not_le,not_and_or] using
    not_congr (rawComplexCauchyCoreGroup_bounded_iff τ)

/-- The exact algebraic group restricts to actual continuous contractions at all causal times. -/
def rawComplexCauchyCoreCausalEvolution (t : ℝ≥0) : rawComplexCauchyCoreRange →L[ℂ] rawComplexCauchyCoreRange :=
  (rawComplexCauchyCoreGroup ((t:ℝ):ℂ)).toLinearMap.mkContinuous 1 (fun y => by
    change ‖rawComplexCauchyCoreGroup ((t:ℝ):ℂ) y‖ ≤ 1 * ‖y‖
    rw [one_mul]
    exact rawComplexCauchyCoreGroup_nonnegative_bound t y)

end
end RHTower.FokasLenells
