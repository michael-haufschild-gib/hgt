import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Strong convergence from a dense set

A uniformly bounded family of continuous linear maps that converges at every point of a dense set
converges at every point.  This is the standard `ε/3` argument, and it is the step that turns a
norm-convergence statement on a dense range into strong convergence on the whole space — the shape
in which resolvent limits are usually available.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Strong convergence from a dense set.**  If the operators are uniformly bounded by `C`, the
limit candidate is bounded by `C`, and convergence holds on a dense set, then it holds everywhere.
-/
theorem tendsto_of_dense_of_uniform_bound {l : Filter ι} {T : ι → E →L[𝕜] F} {S : E →L[𝕜] F}
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᶠ i in l, ‖T i‖ ≤ C) (hS : ‖S‖ ≤ C)
    {s : Set E} (hs : Dense s)
    (hconv : ∀ v ∈ s, Tendsto (fun i => T i v) l (𝓝 (S v))) (v : E) :
    Tendsto (fun i => T i v) l (𝓝 (S v)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hCpos : 0 < 3 * (C + 1) := by linarith
  obtain ⟨w, hw, hvw⟩ :=
    Metric.mem_closure_iff.mp (hs v) (ε / (3 * (C + 1))) (by positivity)
  have hev := Metric.tendsto_nhds.mp (hconv w hw) (ε / 3) (by linarith)
  filter_upwards [hev, hC] with i hi hCi
  have hdist : ‖v - w‖ < ε / (3 * (C + 1)) := by
    rwa [← dist_eq_norm]
  have h1 : ‖T i v - T i w‖ ≤ C * ‖v - w‖ := by
    rw [← ContinuousLinearMap.map_sub]
    exact ((T i).le_opNorm _).trans (mul_le_mul_of_nonneg_right hCi (norm_nonneg _))
  have h2 : ‖S w - S v‖ ≤ C * ‖v - w‖ := by
    rw [norm_sub_rev, ← ContinuousLinearMap.map_sub]
    exact (S.le_opNorm _).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
  have h3 : ‖T i w - S w‖ < ε / 3 := by
    rwa [← dist_eq_norm]
  have hsmall : C * ‖v - w‖ < ε / 3 := by
    have hle : C * ‖v - w‖ ≤ C * (ε / (3 * (C + 1))) :=
      mul_le_mul_of_nonneg_left hdist.le hC0
    have hfrac : C * (ε / (3 * (C + 1))) < ε / 3 := by
      have hrw : C * (ε / (3 * (C + 1))) = (C / (C + 1)) * (ε / 3) := by
        field_simp
      rw [hrw]
      have hlt1 : C / (C + 1) < 1 := by
        rw [div_lt_one (by linarith)]
        linarith
      nlinarith [hε]
    exact lt_of_le_of_lt hle hfrac
  have hsplit : T i v - S v
      = (T i v - T i w) + ((T i w - S w) + (S w - S v)) := by abel
  have htri : ‖T i v - S v‖ ≤ ‖T i v - T i w‖ + (‖T i w - S w‖ + ‖S w - S v‖) := by
    calc ‖T i v - S v‖
        = ‖(T i v - T i w) + ((T i w - S w) + (S w - S v))‖ := by rw [hsplit]
      _ ≤ ‖T i v - T i w‖ + ‖(T i w - S w) + (S w - S v)‖ := norm_add_le _ _
      _ ≤ ‖T i v - T i w‖ + (‖T i w - S w‖ + ‖S w - S v‖) := by
          have := norm_add_le (T i w - S w) (S w - S v)
          linarith
  rw [dist_eq_norm]
  linarith

end GaloisForLFunctions.HTGeometry
