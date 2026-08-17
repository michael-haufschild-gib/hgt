import GaloisForLFunctions.HTGeometry.PoincareMiranda

/-!
# The separation theorem for the cube

If for each of the `m` coordinate directions a set `L i` separates the two opposite faces of the
unit cube, then the `L i` have a common point.  Applying the Poincaré–Miranda theorem to the
difference of the distances to the two open sides produces a point that lies in neither side, in
every direction at once.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

theorem isClosed_unitCube (m : ℕ) : IsClosed (unitCube m) := by
  have hrw : unitCube m = ⋂ i : Fin m,
      (fun x : EuclideanSpace ℝ (Fin m) => x i) ⁻¹' Set.Icc (0 : ℝ) 1 := by
    ext x
    simp [unitCube, Set.mem_iInter]
  rw [hrw]
  exact isClosed_iInter fun i =>
    isClosed_Icc.preimage (EuclideanSpace.proj (𝕜 := ℝ) i).continuous

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
  obtain ⟨x, hx, hzero⟩ :=
    GaloisForLFunctions.poincare_miranda hfcont.continuousOn hface0 hface1
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
