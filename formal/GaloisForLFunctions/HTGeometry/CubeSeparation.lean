import Mathlib
import GaloisForLFunctions.HTGeometry.BrouwerFixedPoint

/-!
# The Poincaré–Miranda theorem and the separation theorem for the cube

Two consequences of Brouwer's fixed point theorem on the unit cube of `ℝ^m`.

The Poincaré–Miranda theorem says that a continuous vector field whose `i`-th component is
nonpositive on the face `x i = 0` and nonnegative on the opposite face has a zero; it follows from
the fixed point theorem applied to `x ↦ clamp (x - f x)`, because a fixed point of that map has, in
each coordinate, the only sign pattern compatible with the boundary conditions.

The separation theorem says that if for each of the `m` coordinate directions a set `L i` separates
the two opposite faces of the cube, then the `L i` have a common point.  Applying Poincaré–Miranda
to the difference of the distances to the two open sides produces a point that is in neither side,
in every direction at once.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

/-- The unit cube of `ℝ^m`. -/
def unitCube (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

theorem mem_unitCube_iff {m : ℕ} {x : EuclideanSpace ℝ (Fin m)} :
    x ∈ unitCube m ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := Iff.rfl

/-- Coordinatewise clamping to `[0, 1]`. -/
noncomputable def cubeClamp (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm fun i => max 0 (min 1 (x i))

@[simp]
theorem cubeClamp_apply (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    cubeClamp m x i = max 0 (min 1 (x i)) := rfl

theorem continuous_cubeClamp (m : ℕ) : Continuous (cubeClamp m) := by
  refine (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp (continuous_pi fun i => ?_)
  exact continuous_const.max (continuous_const.min (EuclideanSpace.proj i).continuous)

theorem cubeClamp_mem (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) : cubeClamp m x ∈ unitCube m := by
  intro i
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem cubeClamp_eq_self {m : ℕ} {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ unitCube m) :
    cubeClamp m x = x := by
  refine PiLp.ext fun i => ?_
  obtain ⟨h0, h1⟩ := hx i
  rw [cubeClamp_apply, min_eq_right h1, max_eq_right h0]

theorem isBounded_unitCube (m : ℕ) : Bornology.IsBounded (unitCube m) := by
  refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨Real.sqrt m, fun x hx => ?_⟩
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  have hle : ∀ i : Fin m, ‖x i‖ ^ 2 ≤ (1 : ℝ) := by
    intro i
    obtain ⟨h0, h1⟩ := hx i
    have : ‖x i‖ = x i := Real.norm_of_nonneg h0
    rw [this]
    nlinarith
  calc ∑ i : Fin m, ‖x i‖ ^ 2 ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum fun i _ => hle i
    _ = (m : ℝ) := by simp

theorem isClosed_unitCube (m : ℕ) : IsClosed (unitCube m) := by
  have hrw : unitCube m = ⋂ i : Fin m,
      (fun x : EuclideanSpace ℝ (Fin m) => x i) ⁻¹' Set.Icc (0 : ℝ) 1 := by
    ext x
    simp [unitCube, Set.mem_iInter]
  rw [hrw]
  exact isClosed_iInter fun i =>
    isClosed_Icc.preimage (EuclideanSpace.proj (𝕜 := ℝ) i).continuous

theorem isCompact_unitCube (m : ℕ) : IsCompact (unitCube m) :=
  isCompact_of_isClosed_isBounded (isClosed_unitCube m) (isBounded_unitCube m)

theorem zero_mem_unitCube (m : ℕ) : (0 : EuclideanSpace ℝ (Fin m)) ∈ unitCube m := by
  intro i
  simp

/-- The vertex of the cube all of whose coordinates equal `1`. -/
noncomputable def cubeOne (m : ℕ) : EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm fun _ => 1

@[simp]
theorem cubeOne_apply (m : ℕ) (i : Fin m) : cubeOne m i = 1 := rfl

theorem cubeOne_mem_unitCube (m : ℕ) : cubeOne m ∈ unitCube m := by
  intro i
  simp

/-- The three regimes of the clamp. -/
private theorem clamp_trichotomy {t a : ℝ} (h : max 0 (min 1 t) = a) :
    (t ≤ 0 ∧ a = 0) ∨ (0 ≤ t ∧ t ≤ 1 ∧ a = t) ∨ (1 ≤ t ∧ a = 1) := by
  rcases le_total t 0 with ht | ht
  · exact Or.inl ⟨ht, by rw [← h, min_eq_right (by linarith), max_eq_left ht]⟩
  · rcases le_total t 1 with ht1 | ht1
    · exact Or.inr (Or.inl ⟨ht, ht1, by rw [← h, min_eq_right ht1, max_eq_right ht]⟩)
    · exact Or.inr (Or.inr ⟨ht1, by rw [← h, min_eq_left ht1, max_eq_right zero_le_one]⟩)

/-- **The Poincaré–Miranda theorem.**  A continuous map of the cube whose `i`-th component is
nonpositive on the face `x i = 0` and nonnegative on the face `x i = 1` vanishes somewhere. -/
theorem exists_forall_eq_zero_of_boundary_signs {m : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)} (hf : Continuous f)
    (h0 : ∀ x ∈ unitCube m, ∀ i, x i = 0 → f x i ≤ 0)
    (h1 : ∀ x ∈ unitCube m, ∀ i, x i = 1 → 0 ≤ f x i) :
    ∃ x ∈ unitCube m, ∀ i, f x i = 0 := by
  have hT : Continuous fun x => cubeClamp m (x - f x) :=
    (continuous_cubeClamp m).comp (continuous_id.sub hf)
  obtain ⟨x, hx, hfix⟩ :=
    GaloisForLFunctions.exists_fixedPoint_of_retraction (continuous_cubeClamp m)
      (cubeClamp_mem m) (fun y hy => cubeClamp_eq_self hy) (isBounded_unitCube m) hT
      (fun y _ => cubeClamp_mem m _)
  refine ⟨x, hx, fun i => ?_⟩
  have hcoord : max 0 (min 1 (x i - f x i)) = x i := by
    have := congrArg (fun z : EuclideanSpace ℝ (Fin m) => z i) hfix
    simpa using this
  obtain ⟨h0i, h1i⟩ := hx i
  rcases clamp_trichotomy hcoord with ⟨ht, ha⟩ | ⟨ht, ht1, ha⟩ | ⟨ht, ha⟩
  · have := h0 x hx i ha
    linarith
  · linarith
  · have := h1 x hx i ha
    linarith

/-- **The separation theorem for the cube.**  If for every coordinate direction the cube is the
union of two mutually non-adherent sides containing the two opposite faces together with a third
set, then the third sets have a common point. -/
theorem exists_mem_iInter_of_separators {m : ℕ}
    {U W L : Fin m → Set (EuclideanSpace ℝ (Fin m))}
    (hcover : ∀ x ∈ unitCube m, ∀ i, x ∈ U i ∨ x ∈ W i ∨ x ∈ L i)
    (hU : ∀ i, ∀ x ∈ U i, x ∉ closure (W i))
    (hW : ∀ i, ∀ x ∈ W i, x ∉ closure (U i))
    (hUne : ∀ i, (U i).Nonempty) (hWne : ∀ i, (W i).Nonempty)
    (hA : ∀ i, ∀ x ∈ unitCube m, x i = 0 → x ∈ U i)
    (hB : ∀ i, ∀ x ∈ unitCube m, x i = 1 → x ∈ W i) :
    ∃ x ∈ unitCube m, ∀ i, x ∈ L i := by
  set f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) := fun x =>
    (EuclideanSpace.equiv (Fin m) ℝ).symm fun i => infDist x (U i) - infDist x (W i) with hfdef
  have hfapp : ∀ x i, f x i = infDist x (U i) - infDist x (W i) := fun _ _ => rfl
  have hfcont : Continuous f := by
    refine (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp (continuous_pi fun i => ?_)
    exact Metric.continuous_infDist_pt _ |>.sub (Metric.continuous_infDist_pt _)
  have hface0 : ∀ y ∈ unitCube m, ∀ i, y i = 0 → f y i ≤ 0 := by
    intro y hy i hyi
    rw [hfapp, Metric.infDist_zero_of_mem (hA i y hy hyi)]
    have := Metric.infDist_nonneg (x := y) (s := W i)
    linarith
  have hface1 : ∀ y ∈ unitCube m, ∀ i, y i = 1 → 0 ≤ f y i := by
    intro y hy i hyi
    rw [hfapp, Metric.infDist_zero_of_mem (hB i y hy hyi)]
    have := Metric.infDist_nonneg (x := y) (s := U i)
    linarith
  obtain ⟨x, hx, hzero⟩ := exists_forall_eq_zero_of_boundary_signs hfcont hface0 hface1
  refine ⟨x, hx, fun i => ?_⟩
  have hEq : infDist x (U i) = infDist x (W i) := by
    have := hzero i
    rw [hfapp] at this
    linarith
  rcases hcover x hx i with hxu | hxw | hxl
  · exact absurd ((Metric.mem_closure_iff_infDist_zero (hWne i)).mpr
      (by rw [← hEq, Metric.infDist_zero_of_mem hxu])) (hU i x hxu)
  · exact absurd ((Metric.mem_closure_iff_infDist_zero (hUne i)).mpr
      (by rw [hEq, Metric.infDist_zero_of_mem hxw])) (hW i x hxw)
  · exact hxl

end GaloisForLFunctions.HTGeometry
