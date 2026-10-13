import GaloisForLFunctions.HTGeometry.LpSolidUniform

/-! # Exact dominated-history observations of diagonal maps

The original history maximizes every diagonal response on its entire solid
hull. Uniform recovery on this hull is equivalent to recovery at that one
history, without a common operator-norm bound on the family.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology
variable {I A : Type*} {l : Filter A}

theorem norm_coordinate_mul_le_of_mem_solidHull
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (w : I → ℂ)
    (hT : ∀ y i, T y i = w i * y i)
    {x y : lp (fun _ : I => ℂ) 2} (hy : y ∈ lpSolidHull x) : ‖T y‖ ≤ ‖T x‖ := by
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro i
  rw [hT, hT, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hy i) (norm_nonneg _)

theorem lpSolidObservation_eq_norm_of_coordinate_mul
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (w : I → ℂ)
    (hT : ∀ y i, T y i = w i * y i) (x : lp (fun _ : I => ℂ) 2) :
    lpSolidObservation T x = ‖T x‖ := by
  apply le_antisymm
  · obtain ⟨m, hm⟩ := lpSolidObservation_attained T x
    rw [← hm]
    exact norm_coordinate_mul_le_of_mem_solidHull T w hT (lpMaskedHistory_mem_solidHull x m)
  · exact norm_apply_le_lpSolidObservation T (fun _ => le_rfl)

theorem lpSolidObservation_diagonal (w : I → ℂ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ i, ‖w i‖ ≤ C) (x : lp (fun _ : I => ℂ) 2) :
    lpSolidObservation (lpDiagonalCLM w hC0 hC) x = ‖lpDiagonalCLM w hC0 hC x‖ :=
  lpSolidObservation_eq_norm_of_coordinate_mul _ w (fun y i => lpDiagonalCLM_apply w hC0 hC y i) x

theorem tendstoUniformlyOn_lpSolidHull_coordinate_mul_iff
    (T : A → lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (w : A → I → ℂ)
    (hT : ∀ a y i, T a y i = w a i * y i) (x : lp (fun _ : I => ℂ) 2) :
    TendstoUniformlyOn (fun a y => T a y) (fun _ => 0) l (lpSolidHull x) ↔
      Tendsto (fun a => T a x) l (𝓝 0) := by
  constructor
  · exact fun h => h.tendsto_at (fun _ => le_rfl)
  · intro h
    have hn : Tendsto (fun a => ‖T a x‖) l (𝓝 0) := by simpa only [norm_zero] using h.norm
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hn.eventually_lt_const hε] with a ha
    intro y hy
    simpa only [dist_zero_left] using
      (norm_coordinate_mul_le_of_mem_solidHull (T a) (w a) (hT a) hy).trans_lt ha

end
end GaloisForLFunctions.HTGeometry
