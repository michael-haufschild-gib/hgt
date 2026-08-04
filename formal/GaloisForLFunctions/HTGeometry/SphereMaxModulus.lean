import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The maximum modulus is attained on the sphere

For an entire function the modulus at any point of a closed disc is dominated by its value at some
point of the bounding circle.  This is the maximum principle together with compactness of the sphere,
in the form a growth argument uses: it converts "large somewhere in the disc" into "large at a point
of a prescribed circle", which is where a minimum-modulus floor lives.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

/-- **The modulus on a closed disc is attained-dominated on its boundary circle.** -/
theorem exists_sphere_norm_ge {F : ℂ → ℂ} (hF : Differentiable ℂ F) {s : ℝ} (hs : 0 < s)
    {w : ℂ} (hw : ‖w‖ ≤ s) : ∃ z : ℂ, ‖z‖ = s ∧ ‖F w‖ ≤ ‖F z‖ := by
  obtain ⟨z₀, hz₀mem, hz₀max⟩ := (isCompact_sphere (0 : ℂ) s).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hs.le) hF.continuous.norm.continuousOn
  have hz₀ : ‖z₀‖ = s := by simpa using hz₀mem
  refine ⟨z₀, hz₀, ?_⟩
  have hfront : frontier (ball (0 : ℂ) s) = sphere (0 : ℂ) s := frontier_ball _ hs.ne'
  have hbound : ∀ z ∈ frontier (ball (0 : ℂ) s), ‖F z‖ ≤ ‖F z₀‖ := by
    intro z hz
    rw [hfront] at hz
    exact hz₀max hz
  have hclos : closure (ball (0 : ℂ) s) = closedBall (0 : ℂ) s := closure_ball _ hs.ne'
  have hmem : w ∈ closure (ball (0 : ℂ) s) := by
    rw [hclos]
    simpa using hw
  exact Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hF.diffContOnCl
    hbound hmem

/-- **Monotonicity of the maximum modulus.**  A value on a smaller circle is dominated by some value
on a larger one. -/
theorem exists_sphere_norm_ge_of_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) {r s : ℝ}
    (hrs : r ≤ s) (hs : 0 < s) {w : ℂ} (hw : ‖w‖ = r) :
    ∃ z : ℂ, ‖z‖ = s ∧ ‖F w‖ ≤ ‖F z‖ :=
  exists_sphere_norm_ge hF hs (by rw [hw]; exact hrs)

/-- **The maximum principle at an arbitrary centre.** -/
theorem exists_sphere_norm_ge_at {F : ℂ → ℂ} (hF : Differentiable ℂ F) {c : ℂ} {s : ℝ}
    (hs : 0 < s) {w : ℂ} (hw : ‖w - c‖ ≤ s) :
    ∃ z : ℂ, ‖z - c‖ = s ∧ ‖F w‖ ≤ ‖F z‖ := by
  have hG : Differentiable ℂ (fun ζ : ℂ => F (c + ζ)) :=
    hF.comp ((differentiable_const c).add differentiable_id)
  obtain ⟨ζ, hζ, hge⟩ := exists_sphere_norm_ge hG hs (w := w - c) hw
  refine ⟨c + ζ, ?_, ?_⟩
  · simpa using hζ
  · have hwc : c + (w - c) = w := by ring
    simpa [hwc] using hge

/-- **A maximiser on the circle dominates the whole closed disc.** -/
theorem exists_sphere_isMaxOn {F : ℂ → ℂ} (hF : Differentiable ℂ F) {s : ℝ} (hs : 0 < s) :
    ∃ z : ℂ, ‖z‖ = s ∧ ∀ w : ℂ, ‖w‖ ≤ s → ‖F w‖ ≤ ‖F z‖ := by
  obtain ⟨z₀, hz₀mem, hz₀max⟩ := (isCompact_sphere (0 : ℂ) s).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hs.le) hF.continuous.norm.continuousOn
  have hz₀ : ‖z₀‖ = s := by simpa using hz₀mem
  refine ⟨z₀, hz₀, ?_⟩
  intro w hw
  have hfront : frontier (ball (0 : ℂ) s) = sphere (0 : ℂ) s := frontier_ball _ hs.ne'
  have hbound : ∀ z ∈ frontier (ball (0 : ℂ) s), ‖F z‖ ≤ ‖F z₀‖ := by
    intro z hz
    rw [hfront] at hz
    exact hz₀max hz
  have hclos : closure (ball (0 : ℂ) s) = closedBall (0 : ℂ) s := closure_ball _ hs.ne'
  have hmem : w ∈ closure (ball (0 : ℂ) s) := by
    rw [hclos]
    simpa using hw
  exact Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hF.diffContOnCl
    hbound hmem

/-- **A maximiser on a circle at an arbitrary centre.** -/
theorem exists_sphere_isMaxOn_at {F : ℂ → ℂ} (hF : Differentiable ℂ F) (c : ℂ) {s : ℝ}
    (hs : 0 < s) :
    ∃ z : ℂ, ‖z - c‖ = s ∧ ∀ w : ℂ, ‖w - c‖ ≤ s → ‖F w‖ ≤ ‖F z‖ := by
  have hG : Differentiable ℂ (fun ζ : ℂ => F (c + ζ)) :=
    hF.comp ((differentiable_const c).add differentiable_id)
  obtain ⟨ζ, hζ, hmax⟩ := exists_sphere_isMaxOn hG hs
  refine ⟨c + ζ, by simpa using hζ, ?_⟩
  intro w hw
  have hwc : c + (w - c) = w := by ring
  have := hmax (w - c) hw
  simpa [hwc] using this

end GaloisForLFunctions.HTGeometry
