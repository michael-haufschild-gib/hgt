import GaloisForLFunctions.HTGeometry.CDGAModule
import Mathlib.Algebra.Colimit.Module

/-!
# The colimit of a directed system of differential graded modules

A directed system of differential graded modules over a fixed commutative differential graded
algebra has, in each degree, a direct limit of the modules of that degree.  The differentials and
the actions assemble into a differential graded module structure on the limit: each axiom is an
identity between elements of the limit, and every element of the limit comes from a stage.

* `CDGAModuleDirectedSystem` : the functoriality hypotheses of a directed system of modules.
* `colimModuleDeg` : the direct limit in a degree.
* `colimModuleD`, `colimModuleAct` : the differential and the action on the limit.
* `colimModule` : the colimit module.
* `colimModuleHom` : the morphism of colimits induced by a compatible family of morphisms.
* `colimModuleOf` : the canonical morphism from a stage.
-/

universe u v v' w

namespace GaloisForLFunctions.HTGeometry

section Colimit

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {ι : Type v'} [Preorder ι] [DecidableEq ι]
  {M : ι → ℕ → Type w} [∀ i n, AddCommGroup (M i n)] [∀ i n, Module R (M i n)]
  {P : ∀ i, CDGAModuleStructure A (M i)}

/-- **The functoriality hypotheses of a directed system of differential graded modules**: the
morphism attached to a relation with itself is the identity, and the morphisms compose. -/
structure CDGAModuleDirectedSystem (P : ∀ i, CDGAModuleStructure A (M i))
    (φ : ∀ i j, i ≤ j → CDGAModuleHom (P i) (P j)) : Prop where
  /-- The morphism of a reflexive relation is the identity. -/
  map_self : ∀ (i : ι) (h : i ≤ i) (n : ℕ) (m : M i n), (φ i i h).toFun n m = m
  /-- The morphisms compose. -/
  map_map : ∀ (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) (n : ℕ) (m : M i n),
    (φ j k hjk).toFun n ((φ i j hij).toFun n m) = (φ i k (hij.trans hjk)).toFun n m

variable (φ : ∀ i j, i ≤ j → CDGAModuleHom (P i) (P j))

/-- The transition maps of the directed system in a given degree. -/
def moduleDegTransition (n : ℕ) (i j : ι) (h : i ≤ j) : M i n →ₗ[R] M j n := (φ i j h).mapₗ n

/-- **The direct limit of a directed system of modules in a given degree.** -/
abbrev colimModuleDeg (n : ℕ) :=
  Module.DirectLimit (fun i => M i n) (moduleDegTransition φ n)

omit [DecidableEq ι] in
theorem moduleDirectedSystem_deg (hsys : CDGAModuleDirectedSystem P φ) (n : ℕ) :
    DirectedSystem (fun i => M i n) (fun i j h => moduleDegTransition φ n i j h) where
  map_self := by
    intro i m
    exact hsys.map_self i le_rfl n m
  map_map := by
    intro k j i hij hjk m
    exact hsys.map_map i j k hij hjk n m

variable [∀ n : ℕ, DirectedSystem (fun i => M i n) fun i j h => moduleDegTransition φ n i j h]

/-- **The differential on the direct limit.** -/
noncomputable def colimModuleD (n : ℕ) :
    colimModuleDeg φ n →ₗ[R] colimModuleDeg φ (n + 1) :=
  Module.DirectLimit.map (fun i => (P i).dₗ n) (fun i j h => by
    refine LinearMap.ext fun m => ?_
    show (P j).d n ((φ i j h).toFun n m) = (φ i j h).toFun (n + 1) ((P i).d n m)
    rw [(φ i j h).map_d n m])

omit [∀ n : ℕ, DirectedSystem (fun i => M i n) fun i j h => moduleDegTransition φ n i j h] in
@[simp] theorem colimModuleD_of (n : ℕ) (i : ι) (m : M i n) :
    colimModuleD φ n
        (Module.DirectLimit.of R ι (fun i => M i n) (moduleDegTransition φ n) i m)
      = Module.DirectLimit.of R ι (fun i => M i (n + 1)) (moduleDegTransition φ (n + 1)) i
        ((P i).d n m) :=
  Module.DirectLimit.map_apply_of _ _ _

/-- **The action of the algebra on the direct limit.** -/
noncomputable def colimModuleAct {b c n : ℕ} (h : b + c = n) (x : X b) :
    colimModuleDeg φ c →ₗ[R] colimModuleDeg φ n :=
  Module.DirectLimit.map (fun i => (P i).actₗ h x) (fun i j hij => by
    refine LinearMap.ext fun m => ?_
    show (P j).act h x ((φ i j hij).toFun c m) = (φ i j hij).toFun n ((P i).act h x m)
    rw [(φ i j hij).map_act h x m])

omit [∀ n : ℕ, DirectedSystem (fun i => M i n) fun i j h => moduleDegTransition φ n i j h] in
@[simp] theorem colimModuleAct_of {b c n : ℕ} (h : b + c = n) (x : X b) (i : ι) (m : M i c) :
    colimModuleAct φ h x
        (Module.DirectLimit.of R ι (fun i => M i c) (moduleDegTransition φ c) i m)
      = Module.DirectLimit.of R ι (fun i => M i n) (moduleDegTransition φ n) i
        ((P i).act h x m) :=
  Module.DirectLimit.map_apply_of _ _ _

variable [IsDirectedOrder ι] [Nonempty ι]

/-- **The colimit of a directed system of differential graded modules.** -/
noncomputable def colimModule : CDGAModuleStructure A (colimModuleDeg φ) where
  act h x z := colimModuleAct φ h x z
  d n z := colimModuleD φ n z
  act_add_left h x x' z := by
    obtain ⟨i, u, rfl⟩ := Module.DirectLimit.exists_of z
    show colimModuleAct φ h (x + x') _ = colimModuleAct φ h x _ + colimModuleAct φ h x' _
    rw [colimModuleAct_of, colimModuleAct_of, colimModuleAct_of, (P i).act_add_left, map_add]
  act_add_right h x z z' := map_add (colimModuleAct φ h x) z z'
  act_smul_left h c x z := by
    obtain ⟨i, u, rfl⟩ := Module.DirectLimit.exists_of z
    show colimModuleAct φ h (c • x) _ = c • colimModuleAct φ h x _
    rw [colimModuleAct_of, colimModuleAct_of, (P i).act_smul_left, map_smul]
  act_smul_right h c x z := map_smul (colimModuleAct φ h x) c z
  act_assoc h₁ h₂ h₃ h₄ x y z := by
    obtain ⟨i, u, rfl⟩ := Module.DirectLimit.exists_of z
    show colimModuleAct φ h₂ (A.mul h₁ x y) _
      = colimModuleAct φ h₄ x (colimModuleAct φ h₃ y _)
    rw [colimModuleAct_of, colimModuleAct_of, colimModuleAct_of, (P i).act_assoc]
  d_add n z z' := map_add (colimModuleD φ n) z z'
  d_smul n c z := map_smul (colimModuleD φ n) c z
  d_d n z := by
    obtain ⟨i, u, rfl⟩ := Module.DirectLimit.exists_of z
    show colimModuleD φ (n + 1) (colimModuleD φ n _) = 0
    rw [colimModuleD_of, colimModuleD_of, (P i).d_d, map_zero]
  d_act h x z := by
    obtain ⟨i, u, rfl⟩ := Module.DirectLimit.exists_of z
    show colimModuleD φ _ (colimModuleAct φ h x _)
      = colimModuleAct φ _ (A.d _ x) _
        + ((-1 : R)) ^ _ • colimModuleAct φ _ x (colimModuleD φ _ _)
    rw [colimModuleAct_of, colimModuleD_of, (P i).d_act, map_add, map_smul,
      colimModuleAct_of, colimModuleD_of, colimModuleAct_of]

/-- **The canonical morphism from a stage into the colimit.** -/
noncomputable def colimModuleOf (i : ι) : CDGAModuleHom (P i) (colimModule φ) where
  toFun n m := Module.DirectLimit.of R ι (fun i => M i n) (moduleDegTransition φ n) i m
  map_add n m m' :=
    map_add (Module.DirectLimit.of R ι (fun i => M i n) (moduleDegTransition φ n) i) m m'
  map_smul n c m :=
    map_smul (Module.DirectLimit.of R ι (fun i => M i n) (moduleDegTransition φ n) i) c m
  map_act h x m := (colimModuleAct_of φ h x i m).symm
  map_d n m := (colimModuleD_of φ n i m).symm

omit [∀ n : ℕ, DirectedSystem (fun i => M i n) fun i j h => moduleDegTransition φ n i j h] in
theorem colimModuleOf_eq (i : ι) (n : ℕ) (m : M i n) :
    (colimModuleOf φ i).toFun n m
      = Module.DirectLimit.of R ι (fun i => M i n) (moduleDegTransition φ n) i m := rfl

omit [∀ n : ℕ, DirectedSystem (fun i => M i n) fun i j h => moduleDegTransition φ n i j h] in
@[simp] theorem colimModuleD_colimOf (n : ℕ) (i : ι) (m : M i n) :
    colimModuleD φ n ((colimModuleOf φ i).toFun n m)
      = (colimModuleOf φ i).toFun (n + 1) ((P i).d n m) := colimModuleD_of φ n i m

omit [∀ n : ℕ, DirectedSystem (fun i => M i n) fun i j h => moduleDegTransition φ n i j h] in
@[simp] theorem colimModuleAct_colimOf {b c n : ℕ} (h : b + c = n) (x : X b) (i : ι) (m : M i c) :
    colimModuleAct φ h x ((colimModuleOf φ i).toFun c m)
      = (colimModuleOf φ i).toFun n ((P i).act h x m) := colimModuleAct_of φ h x i m

omit [∀ n : ℕ, DirectedSystem (fun i => M i n) fun i j h => moduleDegTransition φ n i j h] in
/-- Every element of the colimit comes from a stage. -/
theorem colimModuleOf_exists (n : ℕ) (z : colimModuleDeg φ n) :
    ∃ (i : ι) (m : M i n), (colimModuleOf φ i).toFun n m = z :=
  Module.DirectLimit.exists_of z

omit [∀ n : ℕ, DirectedSystem (fun i => M i n) fun i j h => moduleDegTransition φ n i j h] in
/-- The canonical maps from the stages are compatible with the transitions. -/
theorem colimModuleOf_trans {i j : ι} (hij : i ≤ j) (n : ℕ) (m : M i n) :
    (colimModuleOf φ j).toFun n ((φ i j hij).toFun n m) = (colimModuleOf φ i).toFun n m :=
  Module.DirectLimit.of_f

/-- An element that vanishes in the colimit already vanishes at a later stage. -/
theorem colimModuleOf_eq_zero {i : ι} {n : ℕ} {m : M i n}
    (h : (colimModuleOf φ i).toFun n m = 0) :
    ∃ (j : ι) (hij : i ≤ j), (φ i j hij).toFun n m = 0 :=
  Module.DirectLimit.of.zero_exact h

end Colimit

section ColimitHom

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {ι : Type v'} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι]
  {M : ι → ℕ → Type w} [∀ i n, AddCommGroup (M i n)] [∀ i n, Module R (M i n)]
  {P : ∀ i, CDGAModuleStructure A (M i)} (φ : ∀ i j, i ≤ j → CDGAModuleHom (P i) (P j))
  [∀ n : ℕ, DirectedSystem (fun i => M i n) fun i j h => moduleDegTransition φ n i j h]
  {N : ι → ℕ → Type w} [∀ i n, AddCommGroup (N i n)] [∀ i n, Module R (N i n)]
  {Q : ∀ i, CDGAModuleStructure A (N i)} (ψ : ∀ i j, i ≤ j → CDGAModuleHom (Q i) (Q j))
  [∀ n : ℕ, DirectedSystem (fun i => N i n) fun i j h => moduleDegTransition ψ n i j h]
  (Θ : ∀ i, CDGAModuleHom (P i) (Q i))
  (hΘ : ∀ (i j : ι) (hij : i ≤ j) (n : ℕ) (m : M i n),
    (Θ j).toFun n ((φ i j hij).toFun n m) = (ψ i j hij).toFun n ((Θ i).toFun n m))

include hΘ

/-- The induced map of direct limits in a degree. -/
noncomputable def colimModuleHomFun (n : ℕ) : colimModuleDeg φ n →ₗ[R] colimModuleDeg ψ n :=
  Module.DirectLimit.map (fun i => (Θ i).mapₗ n) (fun i j hij =>
    LinearMap.ext fun m => hΘ i j hij n m)

omit [IsDirectedOrder ι] [Nonempty ι]
  [∀ n : ℕ, DirectedSystem (fun i => M i n) fun i j h => moduleDegTransition φ n i j h]
  [∀ n : ℕ, DirectedSystem (fun i => N i n) fun i j h => moduleDegTransition ψ n i j h] in
@[simp] theorem colimModuleHomFun_of (n : ℕ) (i : ι) (m : M i n) :
    colimModuleHomFun φ ψ Θ hΘ n
        (Module.DirectLimit.of R ι (fun i => M i n) (moduleDegTransition φ n) i m)
      = Module.DirectLimit.of R ι (fun i => N i n) (moduleDegTransition ψ n) i
        ((Θ i).toFun n m) :=
  Module.DirectLimit.map_apply_of _ _ _

/-- **The morphism of colimit modules induced by a compatible family of morphisms.** -/
noncomputable def colimModuleHom : CDGAModuleHom (colimModule φ) (colimModule ψ) where
  toFun n z := colimModuleHomFun φ ψ Θ hΘ n z
  map_add n z z' := map_add _ z z'
  map_smul n c z := map_smul _ c z
  map_act h x z := by
    obtain ⟨i, u, rfl⟩ := Module.DirectLimit.exists_of z
    show colimModuleHomFun φ ψ Θ hΘ _ (colimModuleAct φ h x _)
      = colimModuleAct ψ h x (colimModuleHomFun φ ψ Θ hΘ _ _)
    rw [colimModuleAct_of, colimModuleHomFun_of, colimModuleHomFun_of, colimModuleAct_of,
      (Θ i).map_act h x u]
  map_d n z := by
    obtain ⟨i, u, rfl⟩ := Module.DirectLimit.exists_of z
    show colimModuleHomFun φ ψ Θ hΘ _ (colimModuleD φ n _)
      = colimModuleD ψ n (colimModuleHomFun φ ψ Θ hΘ _ _)
    rw [colimModuleD_of, colimModuleHomFun_of, colimModuleHomFun_of, colimModuleD_of,
      (Θ i).map_d n u]

end ColimitHom

end GaloisForLFunctions.HTGeometry
