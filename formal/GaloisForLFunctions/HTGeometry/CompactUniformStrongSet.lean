import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! # Strong convergence uniformly on compact sets

A common operator bound turns pointwise convergence to zero into uniform
convergence on every compact set, for arbitrary source and target spaces.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology

variable {𝕜 X Y A : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {l : Filter A}

theorem tendstoUniformlyOn_zero_of_strong
    (T : A → X →L[𝕜] Y) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a, ‖T a‖ ≤ C)
    (hp : ∀ x, Tendsto (fun a => T a x) l (𝓝 0))
    (K : Set X) (hK : IsCompact K) :
    TendstoUniformlyOn (fun a x => T a x) (fun _ => 0) l K := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε / (2 * (C + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hpay : C * δ ≤ ε / 2 := by
    have he : (C + 1) * δ = ε / 2 := by
      dsimp [δ]
      field_simp [show C + 1 ≠ 0 by linarith]
    nlinarith
  obtain ⟨S, hS, hcover⟩ := (Metric.totallyBounded_iff.mp hK.totallyBounded) δ hδ
  have hfin : ∀ᶠ a in l, ∀ y ∈ hS.toFinset, ‖T a y‖ < ε / 2 := by
    rw [Filter.eventually_all_finset]
    intro y _hy
    have h := (hp y).norm
    rw [norm_zero] at h
    exact h.eventually_lt_const (by linarith)
  filter_upwards [hfin] with a ha
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hyS := hS.mem_toFinset.mpr hy
  have hd : ‖x - y‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hxy
  have hnear : ‖T a (x - y)‖ ≤ C * δ :=
    ((T a).le_opNorm _).trans (mul_le_mul (hb a) hd.le (norm_nonneg _) hC)
  rw [dist_zero_left]
  calc
    ‖T a x‖ = ‖T a (x - y) + T a y‖ := by rw [map_sub, sub_add_cancel]
    _ ≤ ‖T a (x - y)‖ + ‖T a y‖ := norm_add_le _ _
    _ ≤ C * δ + ‖T a y‖ := by linarith
    _ < ε := by linarith [ha y hyS]

theorem tendsto_zero_of_moving_mem_compact
    (T : A → X →L[𝕜] Y) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a, ‖T a‖ ≤ C)
    (hp : ∀ x, Tendsto (fun a => T a x) l (𝓝 0))
    (K : Set X) (hK : IsCompact K) (x : A → X) (hx : ∀ a, x a ∈ K) :
    Tendsto (fun a => T a (x a)) l (𝓝 0) := by
  have hu := Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_zero_of_strong T C hC hb hp K hK)
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hu ε hε] with a ha
  simpa only [dist_zero_left, dist_zero_right] using ha (x a) (hx a)

end
end GaloisForLFunctions.HTGeometry
