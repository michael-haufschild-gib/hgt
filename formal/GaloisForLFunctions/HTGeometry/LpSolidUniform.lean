import GaloisForLFunctions.HTGeometry.LpSolidObservation
import GaloisForLFunctions.HTGeometry.CompactUniformStrongSet

/-! # Uniform decay under all masks of a fixed square-summable history

The masks may change arbitrarily along the filter. The complete worst
masked response still tends to zero under a bounded strong-null family.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology

variable {I Y A : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {l : Filter A}

theorem tendstoUniformlyOn_lpSolidHull
    (T : A → lp (fun _ : I => ℂ) 2 →L[ℂ] Y) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ a, ‖T a‖ ≤ C) (hp : ∀ y, Tendsto (fun a => T a y) l (𝓝 0))
    (x : lp (fun _ : I => ℂ) 2) :
    TendstoUniformlyOn (fun a y => T a y) (fun _ => 0) l (lpSolidHull x) :=
  tendstoUniformlyOn_zero_of_strong T C hC hb hp _ (isCompact_lpSolidHull x)

theorem tendstoUniformly_lpMaskedHistory
    (T : A → lp (fun _ : I => ℂ) 2 →L[ℂ] Y) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ a, ‖T a‖ ≤ C) (hp : ∀ y, Tendsto (fun a => T a y) l (𝓝 0))
    (x : lp (fun _ : I => ℂ) 2) :
    TendstoUniformly (fun a m => T a (lpMaskedHistory x m)) (fun _ => 0) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_lpSolidHull T C hC hb hp x) ε hε]
    with a ha
  intro m
  exact ha _ (lpMaskedHistory_mem_solidHull x m)

theorem tendsto_lpSolidObservation
    (T : A → lp (fun _ : I => ℂ) 2 →L[ℂ] Y) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ a, ‖T a‖ ≤ C) (hp : ∀ y, Tendsto (fun a => T a y) l (𝓝 0))
    (x : lp (fun _ : I => ℂ) 2) : Tendsto (fun a => lpSolidObservation (T a) x) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_lpSolidHull T C hC hb hp x) ε hε]
    with a ha
  obtain ⟨m, hm⟩ := lpSolidObservation_attained (T a) x
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (lpSolidObservation_nonneg _ _), ← hm]
  simpa only [dist_zero_left] using ha _ (lpMaskedHistory_mem_solidHull x m)

theorem tendsto_moving_lpMaskedHistory
    (T : A → lp (fun _ : I => ℂ) 2 →L[ℂ] Y) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ a, ‖T a‖ ≤ C) (hp : ∀ y, Tendsto (fun a => T a y) l (𝓝 0))
    (x : lp (fun _ : I => ℂ) 2) (m : A → LpCoordinateMask I) :
    Tendsto (fun a => T a (lpMaskedHistory x (m a))) l (𝓝 0) :=
  tendsto_zero_of_moving_mem_compact T C hC hb hp _ (isCompact_lpSolidHull x)
    (fun a => lpMaskedHistory x (m a)) (fun a => lpMaskedHistory_mem_solidHull x (m a))

end
end GaloisForLFunctions.HTGeometry
