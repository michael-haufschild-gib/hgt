import Mathlib.Algebra.Colimit.Module

/-!
# Bilinear maps out of a direct limit

A compatible family of bilinear maps between three directed systems induces a bilinear map on the
direct limits: two elements of the limits come from stages of the system, an upper bound of those
stages carries both, and the value there does not depend on the upper bound chosen.  Mathlib lifts
linear maps out of a direct limit but not bilinear ones.

* `directLimitBilinear` : the induced bilinear map on the direct limits.
* `directLimitBilinear_of_of` : its value on elements coming from a common stage.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

section Bilinear

variable {R : Type u} [CommRing R] {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  [DecidableEq ι] {G G' G'' : ι → Type w}
  [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  [∀ i, AddCommGroup (G' i)] [∀ i, Module R (G' i)]
  [∀ i, AddCommGroup (G'' i)] [∀ i, Module R (G'' i)]
  {f : ∀ i j, i ≤ j → G i →ₗ[R] G j} {f' : ∀ i j, i ≤ j → G' i →ₗ[R] G' j}
  {f'' : ∀ i j, i ≤ j → G'' i →ₗ[R] G'' j}
  [DirectedSystem G fun i j h => f i j h] [DirectedSystem G' fun i j h => f' i j h]
  [DirectedSystem G'' fun i j h => f'' i j h]
  (b : ∀ i, G i →ₗ[R] G' i →ₗ[R] G'' i)

/-- A chosen upper bound of two indices. -/
noncomputable def ubOf (i j : ι) : ι := (exists_ge_ge i j).choose

omit [Nonempty ι] [DecidableEq ι] in
theorem le_ubOf_left (i j : ι) : i ≤ ubOf i j := (exists_ge_ge i j).choose_spec.1

omit [Nonempty ι] [DecidableEq ι] in
theorem le_ubOf_right (i j : ι) : j ≤ ubOf i j := (exists_ge_ge i j).choose_spec.2

variable (hb : ∀ (i j : ι) (h : i ≤ j) (x : G i) (y : G' i),
  b j (f i j h x) (f' i j h y) = f'' i j h (b i x y))

include hb

omit [Nonempty ι] [DirectedSystem G'' fun i j h => f'' i j h] in
/-- **The value of the product at a common stage does not depend on the stage.** -/
theorem directLimit_b_stage_eq {i j : ι} (k k' : ι) (hik : i ≤ k) (hjk : j ≤ k) (hik' : i ≤ k')
    (hjk' : j ≤ k') (x : G i) (y : G' j) :
    Module.DirectLimit.of R ι G'' f'' k (b k (f i k hik x) (f' j k hjk y)) =
      Module.DirectLimit.of R ι G'' f'' k' (b k' (f i k' hik' x) (f' j k' hjk' y)) := by
  obtain ⟨m, hkm, hk'm⟩ := exists_ge_ge k k'
  have hmove : ∀ (l : ι) (hil : i ≤ l) (hjl : j ≤ l) (hlm : l ≤ m),
      Module.DirectLimit.of R ι G'' f'' l (b l (f i l hil x) (f' j l hjl y)) =
        Module.DirectLimit.of R ι G'' f'' m
          (b m (f i m (hil.trans hlm) x) (f' j m (hjl.trans hlm) y)) := by
    intro l hil hjl hlm
    rw [← Module.DirectLimit.of_f (f := f'') (hij := hlm)
      (x := b l (f i l hil x) (f' j l hjl y))]
    congr 1
    rw [← hb l m hlm (f i l hil x) (f' j l hjl y)]
    rw [DirectedSystem.map_map (f := fun i j h => f i j h) hil hlm x,
      DirectedSystem.map_map (f := fun i j h => f' i j h) hjl hlm y]
  rw [hmove k hik hjk hkm, hmove k' hik' hjk' hk'm]

/-- The map on the second limit determined by an element of a stage of the first. -/
noncomputable def rightLift (i : ι) (x : G i) :
    Module.DirectLimit G' f' →ₗ[R] Module.DirectLimit G'' f'' :=
  Module.DirectLimit.lift R ι G' f'
    (fun j => (Module.DirectLimit.of R ι G'' f'' (ubOf i j)).comp
      ((b (ubOf i j) (f i (ubOf i j) (le_ubOf_left i j) x)).comp
        (f' j (ubOf i j) (le_ubOf_right i j))))
    (fun j j' hjj' y => by
      show Module.DirectLimit.of R ι G'' f'' (ubOf i j')
          (b (ubOf i j') (f i (ubOf i j') (le_ubOf_left i j') x)
            (f' j' (ubOf i j') (le_ubOf_right i j') (f' j j' hjj' y))) =
        Module.DirectLimit.of R ι G'' f'' (ubOf i j)
          (b (ubOf i j) (f i (ubOf i j) (le_ubOf_left i j) x)
            (f' j (ubOf i j) (le_ubOf_right i j) y))
      rw [DirectedSystem.map_map (f := fun i j h => f' i j h) hjj' (le_ubOf_right i j') y]
      exact directLimit_b_stage_eq b hb _ _ (le_ubOf_left i j')
        (hjj'.trans (le_ubOf_right i j')) (le_ubOf_left i j) (le_ubOf_right i j) x y)

omit [Nonempty ι] [DirectedSystem G'' fun i j h => f'' i j h] in
@[simp]
theorem rightLift_of (i j : ι) (x : G i) (y : G' j) :
    rightLift b hb i x (Module.DirectLimit.of R ι G' f' j y) =
      Module.DirectLimit.of R ι G'' f'' (ubOf i j)
        (b (ubOf i j) (f i (ubOf i j) (le_ubOf_left i j) x)
          (f' j (ubOf i j) (le_ubOf_right i j) y)) :=
  Module.DirectLimit.lift_of _ _ _

omit [Nonempty ι] [DirectedSystem G'' fun i j h => f'' i j h] in
/-- The value of `rightLift` at any common stage. -/
theorem rightLift_of_stage {i j : ι} (k : ι) (hik : i ≤ k) (hjk : j ≤ k) (x : G i) (y : G' j) :
    rightLift b hb i x (Module.DirectLimit.of R ι G' f' j y) =
      Module.DirectLimit.of R ι G'' f'' k (b k (f i k hik x) (f' j k hjk y)) := by
  rw [rightLift_of]
  exact directLimit_b_stage_eq b hb _ _ (le_ubOf_left i j) (le_ubOf_right i j) hik hjk x y

/-- `rightLift` is linear in the element of the first system. -/
noncomputable def leftFamily (i : ι) :
    G i →ₗ[R] (Module.DirectLimit G' f' →ₗ[R] Module.DirectLimit G'' f'') where
  toFun x := rightLift b hb i x
  map_add' x x' := by
    refine Module.DirectLimit.hom_ext fun j => LinearMap.ext fun y => ?_
    show rightLift b hb i (x + x') (Module.DirectLimit.of R ι G' f' j y) =
      rightLift b hb i x (Module.DirectLimit.of R ι G' f' j y) +
        rightLift b hb i x' (Module.DirectLimit.of R ι G' f' j y)
    rw [rightLift_of, rightLift_of, rightLift_of, map_add, map_add, LinearMap.add_apply,
      map_add]
  map_smul' c x := by
    refine Module.DirectLimit.hom_ext fun j => LinearMap.ext fun y => ?_
    show rightLift b hb i (c • x) (Module.DirectLimit.of R ι G' f' j y) =
      c • rightLift b hb i x (Module.DirectLimit.of R ι G' f' j y)
    rw [rightLift_of, rightLift_of, map_smul, map_smul, LinearMap.smul_apply, map_smul]

/-- **The bilinear map induced on the direct limits.** -/
noncomputable def directLimitBilinear :
    Module.DirectLimit G f →ₗ[R] (Module.DirectLimit G' f' →ₗ[R] Module.DirectLimit G'' f'') :=
  Module.DirectLimit.lift R ι G f (leftFamily b hb)
    (fun i i' hii' x => by
      refine Module.DirectLimit.hom_ext fun j => LinearMap.ext fun y => ?_
      show rightLift b hb i' (f i i' hii' x) (Module.DirectLimit.of R ι G' f' j y) =
        rightLift b hb i x (Module.DirectLimit.of R ι G' f' j y)
      obtain ⟨m, hi'm, hjm⟩ := exists_ge_ge i' j
      rw [rightLift_of_stage b hb m hi'm hjm, rightLift_of_stage b hb m (hii'.trans hi'm) hjm]
      rw [DirectedSystem.map_map (f := fun i j h => f i j h) hii' hi'm x])

omit [Nonempty ι] [DirectedSystem G'' fun i j h => f'' i j h] in
/-- **The value of the induced bilinear map on elements coming from a common stage.** -/
theorem directLimitBilinear_of_of {i j : ι} (k : ι) (hik : i ≤ k) (hjk : j ≤ k) (x : G i)
    (y : G' j) :
    directLimitBilinear b hb (Module.DirectLimit.of R ι G f i x) (Module.DirectLimit.of R ι G' f' j y) =
      Module.DirectLimit.of R ι G'' f'' k (b k (f i k hik x) (f' j k hjk y)) := by
  show (Module.DirectLimit.lift R ι G f (leftFamily b hb) _ (Module.DirectLimit.of R ι G f i x))
    (Module.DirectLimit.of R ι G' f' j y) = _
  rw [Module.DirectLimit.lift_of]
  exact rightLift_of_stage b hb k hik hjk x y

omit [Nonempty ι] [DirectedSystem G'' fun i j h => f'' i j h] in
/-- The value of the induced bilinear map on elements of the same stage. -/
theorem directLimitBilinear_of_of_same (i : ι) (x : G i) (y : G' i) :
    directLimitBilinear b hb (Module.DirectLimit.of R ι G f i x) (Module.DirectLimit.of R ι G' f' i y) =
      Module.DirectLimit.of R ι G'' f'' i (b i x y) := by
  rw [directLimitBilinear_of_of b hb i le_rfl le_rfl x y]
  rw [DirectedSystem.map_self (f := fun i j h => f i j h) x,
    DirectedSystem.map_self (f := fun i j h => f' i j h) y]

end Bilinear

end GaloisForLFunctions.HTGeometry
