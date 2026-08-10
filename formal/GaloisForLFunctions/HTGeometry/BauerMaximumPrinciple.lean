import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Function

/-!
# Bauer's maximum principle

A convex function on a compact convex set attains its maximum at an extreme point.  The mechanism
is that the set where a convex function attains its maximum over `K` is itself an extreme subset of
`K`, so the Krein–Milman lemma produces an extreme point of that subset, and an extreme point of an
extreme subset is an extreme point of `K`.

No convexity of `K` is needed for the argument: only that `K` is compact and that the function is
convex on it.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

omit [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] in
/-- The maximum set of a convex function is an extreme subset. -/
theorem isExtreme_setOf_eq_max {K : Set E} {f : E → ℝ} (hf : ConvexOn ℝ K f) {M : ℝ}
    (hM : ∀ y ∈ K, f y ≤ M) : IsExtreme ℝ K {y | y ∈ K ∧ f y = M} where
  subset := fun _ hy => hy.1
  left_mem_of_mem_openSegment := by
    rintro x hx y hy z ⟨-, hzM⟩ ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨hx, le_antisymm (hM x hx) ?_⟩
    have hconv := hf.2 hx hy ha.le hb.le hab
    have hfy := hM y hy
    have hfx := hM x hx
    rw [hzM] at hconv
    simp only [smul_eq_mul] at hconv
    by_contra hcon
    have hlt : f x < M := not_le.mp hcon
    have h1 : a * f x < a * M := mul_lt_mul_of_pos_left hlt ha
    have h2 : b * f y ≤ b * M := mul_le_mul_of_nonneg_left hfy hb.le
    have h3 : a * M + b * M = M := by rw [← add_mul, hab, one_mul]
    linarith

/-- **Bauer's maximum principle.**  A convex function that is continuous on a nonempty compact set
attains its maximum at an extreme point of that set. -/
theorem exists_extremePoint_forall_le {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    {f : E → ℝ} (hfc : ContinuousOn f K) (hf : ConvexOn ℝ K f) :
    ∃ x ∈ K.extremePoints ℝ, ∀ y ∈ K, f y ≤ f x := by
  obtain ⟨x₀, hx₀K, hx₀max⟩ := hK.exists_isMaxOn hKne hfc
  have hMmax : ∀ y ∈ K, f y ≤ f x₀ := fun y hy => hx₀max hy
  set F : Set E := {y | y ∈ K ∧ f y = f x₀} with hF
  have hFext : IsExtreme ℝ K F := isExtreme_setOf_eq_max hf hMmax
  have hFne : F.Nonempty := ⟨x₀, hx₀K, rfl⟩
  have hFeq : F = K ∩ f ⁻¹' {f x₀} := by
    ext y
    simp [hF, Set.mem_inter_iff, and_comm]
  have hFclosed : IsClosed F := by
    rw [hFeq]
    exact hfc.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton
  have hFcomp : IsCompact F := hK.of_isClosed_subset hFclosed hFext.subset
  obtain ⟨y, hy⟩ := hFcomp.extremePoints_nonempty hFne
  refine ⟨y, hFext.extremePoints_subset_extremePoints hy, fun z hz => ?_⟩
  rw [hy.1.2]
  exact hMmax z hz

end GaloisForLFunctions.HTGeometry
