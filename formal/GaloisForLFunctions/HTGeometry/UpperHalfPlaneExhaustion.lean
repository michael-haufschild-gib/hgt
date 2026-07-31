import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.MetricSpace.ProperSpace
import GaloisForLFunctions.HTGeometry.CompactPatchGenericity

/-!
# A compact exhaustion of the open upper half-plane

The compact-patch genericity argument needs the node region written as a countable union of compact
sets.  The open upper half-plane is exhausted by the patches

```text
K m = {z : 1 / (m + 1) ≤ Im z and ‖z‖ ≤ m + 1},
```

each closed and bounded, hence compact, and each bounded away from the real axis — which is the
second hypothesis every kernel bound needs.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- The `m`-th compact patch of the open upper half-plane. -/
def upperPatch (m : ℕ) : Set ℂ :=
  {z : ℂ | (1 : ℝ) / (m + 1) ≤ z.im ∧ ‖z‖ ≤ (m + 1 : ℝ)}

theorem isClosed_upperPatch (m : ℕ) : IsClosed (upperPatch m) := by
  have h1 : IsClosed {z : ℂ | (1 : ℝ) / (m + 1) ≤ z.im} :=
    isClosed_le continuous_const Complex.continuous_im
  have h2 : IsClosed {z : ℂ | ‖z‖ ≤ (m + 1 : ℝ)} :=
    isClosed_le continuous_norm continuous_const
  exact h1.inter h2

theorem isBounded_upperPatch (m : ℕ) : Bornology.IsBounded (upperPatch m) := by
  apply Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := (m + 1 : ℝ)))
  intro z hz
  simpa [Metric.mem_closedBall, dist_eq_norm] using hz.2

theorem isCompact_upperPatch (m : ℕ) : IsCompact (upperPatch m) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_upperPatch m) (isBounded_upperPatch m)

/-- Every patch stays off the real axis. -/
theorem upperPatch_im_ne_zero (m : ℕ) : ∀ z ∈ upperPatch m, z.im ≠ 0 := by
  intro z hz
  have hpos : (0 : ℝ) < 1 / (m + 1) := by positivity
  exact ne_of_gt (lt_of_lt_of_le hpos hz.1)

/-- Every patch lies in the open upper half-plane. -/
theorem upperPatch_subset (m : ℕ) : upperPatch m ⊆ {z : ℂ | 0 < z.im} := by
  intro z hz
  have hpos : (0 : ℝ) < 1 / (m + 1) := by positivity
  exact lt_of_lt_of_le hpos hz.1

/-- **The patches exhaust the open upper half-plane.** -/
theorem iUnion_upperPatch : (⋃ m, upperPatch m) = {z : ℂ | 0 < z.im} := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hz
    exact upperPatch_subset m hm
  · intro z hz
    have hzim : 0 < z.im := hz
    obtain ⟨m₁, hm₁⟩ := exists_nat_ge (1 / z.im)
    obtain ⟨m₂, hm₂⟩ := exists_nat_ge ‖z‖
    refine Set.mem_iUnion.mpr ⟨max m₁ m₂, ?_, ?_⟩
    · have hge : (1 : ℝ) / z.im ≤ (max m₁ m₂ : ℕ) + 1 := by
        have : (m₁ : ℝ) ≤ (max m₁ m₂ : ℕ) := by
          exact_mod_cast Nat.cast_le.mpr (le_max_left m₁ m₂)
        linarith
      have hpos : (0 : ℝ) < (max m₁ m₂ : ℕ) + 1 := by positivity
      rw [div_le_iff₀ hpos]
      rw [div_le_iff₀ hzim] at hge
      linarith
    · have : (m₂ : ℝ) ≤ (max m₁ m₂ : ℕ) := by
        exact_mod_cast Nat.cast_le.mpr (le_max_right m₁ m₂)
      linarith

/-- Each patch sits inside the interior of the next, so a bound valid on one patch is available on
a neighbourhood of the previous one. -/
theorem upperPatch_subset_interior_succ (m : ℕ) :
    upperPatch m ⊆ interior (upperPatch (m + 1)) := by
  intro z hz
  apply mem_interior_iff_mem_nhds.mpr
  have hopen : IsOpen {w : ℂ | (1 : ℝ) / (m + 2) < w.im ∧ ‖w‖ < (m + 2 : ℝ)} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt continuous_norm continuous_const)
  have hmem : z ∈ {w : ℂ | (1 : ℝ) / (m + 2) < w.im ∧ ‖w‖ < (m + 2 : ℝ)} := by
    constructor
    · have h1 : (1 : ℝ) / (m + 2) < 1 / (m + 1) := by
        apply one_div_lt_one_div_of_lt <;> [positivity; linarith]
      exact lt_of_lt_of_le h1 hz.1
    · have := hz.2
      linarith
  refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
  intro w hw
  obtain ⟨hw1, hw2⟩ := hw
  have hcast : ((m + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 2 := by push_cast; ring
  refine ⟨?_, ?_⟩
  · show (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) ≤ w.im
    rw [hcast]
    exact le_of_lt hw1
  · show ‖w‖ ≤ ((m + 1 : ℕ) : ℝ) + 1
    rw [hcast]
    exact le_of_lt hw2

/-- **Genericity over the whole open upper half-plane.**  If nonvanishing is dense over each
compact patch and jointly continuous along it, then it is dense over the entire open upper
half-plane. -/
theorem dense_setOf_forall_upperHalfPlane_ne_zero
    {X E : Type*} [TopologicalSpace X] [BaireSpace X]
    [TopologicalSpace E] [T1Space E] [Zero E]
    (g : X → ℂ → E)
    (hg : ∀ m, ∀ x : X, ∀ z ∈ upperPatch m,
      ContinuousAt (fun p : X × ℂ => g p.1 p.2) (x, z))
    (hdense : ∀ m, Dense {x : X | ∀ z ∈ upperPatch m, g x z ≠ 0}) :
    Dense {x : X | ∀ z : ℂ, 0 < z.im → g x z ≠ 0} := by
  have hmain := dense_setOf_forall_mem_iUnion_compact_ne_zero
    upperPatch isCompact_upperPatch g hg hdense
  have hset : {x : X | ∀ z ∈ ⋃ m, upperPatch m, g x z ≠ 0} =
      {x : X | ∀ z : ℂ, 0 < z.im → g x z ≠ 0} := by
    ext x
    rw [iUnion_upperPatch]
    simp
  rwa [hset] at hmain

end

end GaloisForLFunctions.HTGeometry
