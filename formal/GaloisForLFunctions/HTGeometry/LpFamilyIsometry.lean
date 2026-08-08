import Mathlib

/-!
# Componentwise isometries of an `lp` direct sum

A family of linear isometries between the summands induces a linear isometry of the `lp` direct
sum: membership and the norm both depend on the summand norms alone, and those are unchanged
componentwise.  mathlib builds `lp` and the single-summand inclusion but not this map.

The statements are given for a finite exponent, which is the case a Fock space needs.
-/

open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} {E F : α → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedAddCommGroup (F i)] {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [∀ i, NormedSpace 𝕜 (E i)] [∀ i, NormedSpace 𝕜 (F i)]

theorem memℓp_of_norm_eq {f : ∀ i, E i} {g : ∀ i, F i} {p : ℝ≥0∞} (hp : 0 < p.toReal)
    (h : ∀ i, ‖g i‖ = ‖f i‖) (hf : Memℓp f p) : Memℓp g p := by
  rw [memℓp_gen_iff hp] at hf ⊢
  refine hf.congr fun i => ?_
  rw [h]

/-- **A family of linear isometries induces one on the `lp` sum.** -/
noncomputable def lpFamilyIsometry {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : ∀ i, E i →ₗᵢ[𝕜] F i) : lp E p →ₗᵢ[𝕜] lp F p := by
  have h1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hptr : 0 < p.toReal :=
    ENNReal.toReal_pos (by intro h; rw [h] at h1; simp at h1) hp
  refine
    { toFun := fun x => ⟨fun i => T i (x i),
        memℓp_of_norm_eq hptr (fun i => (T i).norm_map _) (lp.memℓp x)⟩
      map_add' := ?_
      map_smul' := ?_
      norm_map' := ?_ }
  · intro x y
    refine Subtype.ext (funext fun i => ?_)
    exact (T i).map_add _ _
  · intro c x
    refine Subtype.ext (funext fun i => ?_)
    exact (T i).map_smul _ _
  · intro x
    rw [lp.norm_eq_tsum_rpow hptr, lp.norm_eq_tsum_rpow hptr]
    congr 1
    refine tsum_congr fun i => ?_
    congr 1
    exact (T i).norm_map _

end GaloisForLFunctions.HTGeometry
