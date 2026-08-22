import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Weak nullity transfers to the completion of a pre-Hilbert space

On an inner product space `E` that is **not** complete, "weakly null against every element of `E`"
is strictly weaker than "weakly null against every continuous functional": the Riesz
representation of a functional lives in the completion, not in `E`.

This file closes that gap.  If `x n` is a bounded sequence in `E` with `⟪y, x n⟫ → 0` for every
`y : E`, then the image sequence in `UniformSpace.Completion E` is weakly null against **every**
continuous functional, because the completion is a Hilbert space (Riesz applies) and `E` is dense in
it.  This is exactly the hypothesis shape required by the compact-operator criteria, and it is what
lets an incomplete carrier — a Hilbert tensor product before completion, say — be used with them.
-/

namespace HTGeometry

open Filter Topology UniformSpace

section WeakNull

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Weak nullity transfers to the completion.**  Boundedness plus weak nullity against the dense
subspace gives weak nullity against every continuous functional on the completion. -/
theorem completion_weakly_tendsto_zero (x : ℕ → E) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ n, ‖x n‖ ≤ R)
    (hweak : ∀ y : E, Tendsto (fun n => inner ℂ y (x n)) atTop (𝓝 (0 : ℂ)))
    (l : Completion E →L[ℂ] ℂ) :
    Tendsto (fun n => l ((x n : Completion E))) atTop (𝓝 (0 : ℂ)) := by
  obtain ⟨w, hw⟩ := (InnerProductSpace.toDual ℂ (Completion E)).surjective l
  have hlrepr : ∀ z : Completion E, l z = inner ℂ w z := by
    intro z
    rw [← hw]
    rfl
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hRpos : (0 : ℝ) < R + 1 := by linarith
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.mp (Completion.denseRange_coe (α := E)) w
    (ε / (2 * (R + 1))) (by positivity)
  have hyw : ‖w - (y : Completion E)‖ < ε / (2 * (R + 1)) := by
    rw [← dist_eq_norm]
    exact hy
  have hinner := hweak y
  rw [NormedAddGroup.tendsto_nhds_zero] at hinner
  filter_upwards [hinner (ε / 2) (by positivity)] with n hn
  have hcoe : inner ℂ ((y : Completion E)) ((x n : Completion E)) = inner ℂ y (x n) :=
    Completion.inner_coe y (x n)
  have hnormcoe : ‖((x n : Completion E))‖ = ‖x n‖ := Completion.norm_coe (x n)
  have hsplit : l ((x n : Completion E))
      = inner ℂ ((y : Completion E)) ((x n : Completion E))
        + inner ℂ (w - (y : Completion E)) ((x n : Completion E)) := by
    rw [hlrepr, ← inner_add_left]
    congr 1
    abel
  have hrest : ‖inner ℂ (w - (y : Completion E)) ((x n : Completion E))‖
      ≤ ‖w - (y : Completion E)‖ * ‖((x n : Completion E))‖ := norm_inner_le_norm _ _
  have hxn : ‖((x n : Completion E))‖ ≤ R := by rw [hnormcoe]; exact hbound n
  have hxn0 : (0 : ℝ) ≤ ‖((x n : Completion E))‖ := norm_nonneg _
  have hbound2 : ‖inner ℂ (w - (y : Completion E)) ((x n : Completion E))‖ < ε / 2 := by
    calc ‖inner ℂ (w - (y : Completion E)) ((x n : Completion E))‖
        ≤ ‖w - (y : Completion E)‖ * ‖((x n : Completion E))‖ := hrest
      _ ≤ ‖w - (y : Completion E)‖ * R := by
          exact mul_le_mul_of_nonneg_left hxn (norm_nonneg _)
      _ < (ε / (2 * (R + 1))) * (R + 1) := by
          have hlt : ‖w - (y : Completion E)‖ * R
              ≤ ‖w - (y : Completion E)‖ * (R + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
          have hstrict : ‖w - (y : Completion E)‖ * (R + 1)
              < (ε / (2 * (R + 1))) * (R + 1) :=
            mul_lt_mul_of_pos_right hyw hRpos
          linarith
      _ = ε / 2 := by field_simp
  calc ‖l ((x n : Completion E))‖
      = ‖inner ℂ ((y : Completion E)) ((x n : Completion E))
          + inner ℂ (w - (y : Completion E)) ((x n : Completion E))‖ := by rw [hsplit]
    _ ≤ ‖inner ℂ ((y : Completion E)) ((x n : Completion E))‖
          + ‖inner ℂ (w - (y : Completion E)) ((x n : Completion E))‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := by
        rw [hcoe]
        exact add_lt_add hn hbound2
    _ = ε := by ring

end WeakNull

end HTGeometry
