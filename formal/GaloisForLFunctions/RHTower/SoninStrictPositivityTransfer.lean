import Mathlib

/-!
# Strict positivity transfer through a lower semicontinuous Sonin-type energy

Connes–Consani bound the archimedean Weil form on smooth test functions with support in
`[2^{−1/2}, 2^{1/2}]` from below by the Sonin trace `Tr(ϑ(g) S ϑ(g)^*) = Σ_j ‖ϑ(g) e_j‖²`, the sum
over an orthonormal basis `(e_j)` of the Sonin space.  This file isolates the abstract mechanism
by which such a bound forces the closed form to have **no null vector**:

* the Sonin-type energy `Σ_j ‖Θ_v e_j‖²` is lower semicontinuous in `v` whenever each
  `v ↦ Θ_v e_j` is continuous (a sum of continuous nonnegative terms);
* it is strictly positive at every `v` for which some `Θ_v e_j ≠ 0`, in particular whenever `Θ_v`
  is injective and the Sonin space is nonzero;
* a lower semicontinuous bound on a core transfers to every vector reachable by a core sequence
  along which the form converges.

Consequently a closed form dominating the Sonin-type energy on a core is strictly positive on its
whole domain, with no null vector.  No Weil-form object is used; the statements are about an
arbitrary family of operators on a normed space.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace RHTower

variable {V K ι : Type*} [TopologicalSpace V] [NormedAddCommGroup K]

/-- The Sonin-type energy `Σ_j ‖Θ_v e_j‖²` of a family of vectors depending on `v`. -/
noncomputable def soninTypeEnergy (Θ : V → ι → K) (v : V) : ℝ≥0∞ :=
  ∑' j, ((‖Θ v j‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)

/-- **Lower semicontinuity.**  A sum of continuous nonnegative terms is lower semicontinuous. -/
theorem lowerSemicontinuous_soninTypeEnergy (Θ : V → ι → K)
    (hc : ∀ j, Continuous fun v => Θ v j) :
    LowerSemicontinuous (soninTypeEnergy Θ) := by
  unfold soninTypeEnergy
  refine lowerSemicontinuous_tsum fun j => ?_
  exact (ENNReal.continuous_coe.comp ((hc j).nnnorm.pow 2)).lowerSemicontinuous

omit [TopologicalSpace V] in
/-- **Strict positivity.**  One nonzero term makes the energy positive. -/
theorem soninTypeEnergy_pos (Θ : V → ι → K) {v : V} {j₀ : ι} (h : Θ v j₀ ≠ 0) :
    0 < soninTypeEnergy Θ v := by
  unfold soninTypeEnergy
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum j₀)
  have : (0 : ℝ≥0) < ‖Θ v j₀‖₊ := nnnorm_pos.mpr h
  exact ENNReal.coe_pos.mpr (pow_pos this 2)

omit [TopologicalSpace V] in
/-- Injective operators on a nonzero Sonin vector give positive energy. -/
theorem soninTypeEnergy_pos_of_injective {𝕜 : Type*} [Semiring 𝕜] [Module 𝕜 K]
    (T : V → K →ₗ[𝕜] K) (e : ι → K) {v : V} (hT : Function.Injective (T v)) {j₀ : ι}
    (he : e j₀ ≠ 0) :
    0 < soninTypeEnergy (fun w j => T w (e j)) v := by
  refine soninTypeEnergy_pos _ (j₀ := j₀) ?_
  intro h0
  exact he (hT (by simpa using h0))

/-- **Lower semicontinuous bounds pass to limits.** -/
theorem le_of_lowerSemicontinuous_of_tendsto {R : V → ℝ≥0∞} (hR : LowerSemicontinuous R)
    {u : ℕ → V} {x : V} (hu : Tendsto u atTop (𝓝 x)) {q : ℕ → ℝ≥0∞} {a : ℝ≥0∞}
    (hq : Tendsto q atTop (𝓝 a)) (hle : ∀ n, R (u n) ≤ q n) : R x ≤ a := by
  have h1 : R x ≤ liminf R (𝓝 x) := lowerSemicontinuous_iff_le_liminf.mp hR x
  have h2 : liminf R (𝓝 x) ≤ liminf (fun n => R (u n)) atTop := by
    have hmap : liminf R (map u atTop) = liminf (fun n => R (u n)) atTop := by
      simp only [Filter.liminf, Filter.map_map]
      rfl
    rw [← hmap]
    exact liminf_le_liminf_of_le hu
  have h3 : liminf (fun n => R (u n)) atTop ≤ liminf q atTop :=
    liminf_le_liminf (Eventually.of_forall hle)
  have h4 : liminf q atTop = a := hq.liminf_eq
  calc R x ≤ liminf R (𝓝 x) := h1
    _ ≤ liminf (fun n => R (u n)) atTop := h2
    _ ≤ liminf q atTop := h3
    _ = a := h4

/-- **No null vector.**  If a form `Q` dominates the Sonin-type energy along a core sequence
converging to `x` with `Q` converging, and some `Θ_x e_j ≠ 0`, then `Q x > 0`. -/
theorem pos_of_dominates_soninTypeEnergy (Θ : V → ι → K)
    (hc : ∀ j, Continuous fun v => Θ v j) {Q : V → ℝ≥0∞} {x : V} {u : ℕ → V}
    (hu : Tendsto u atTop (𝓝 x)) (hQ : Tendsto (fun n => Q (u n)) atTop (𝓝 (Q x)))
    (hle : ∀ n, soninTypeEnergy Θ (u n) ≤ Q (u n)) {j₀ : ι} (hj : Θ x j₀ ≠ 0) :
    0 < Q x :=
  lt_of_lt_of_le (soninTypeEnergy_pos Θ hj)
    (le_of_lowerSemicontinuous_of_tendsto (lowerSemicontinuous_soninTypeEnergy Θ hc) hu hQ hle)

end RHTower
