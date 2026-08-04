import GaloisForLFunctions.HTGeometry.CDGA
import Mathlib.Algebra.Colimit.Module

/-!
# The colimit of a directed system of commutative differential graded algebras

A directed system of commutative differential graded algebras has, in each degree, a direct limit of
the modules of that degree, and the differentials assemble into a differential on the limit which
still squares to zero.  This is the underlying differential graded module of the colimit algebra.

* `CDGADirectedSystem` : the functoriality hypotheses of a directed system of morphisms.
* `colimDeg` : the direct limit in a degree.
* `colimD`, `colimD_comp` : the differential on the limit, and that it squares to zero.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

open CDGAStructure

section Colimit

variable {R : Type u} [CommRing R] {ι : Type v} [Preorder ι] [DecidableEq ι]
  {X : ι → ℕ → Type w} [∀ i n, AddCommGroup (X i n)] [∀ i n, Module R (X i n)]
  {A : ∀ i, CDGAStructure R (X i)}

/-- **The functoriality hypotheses of a directed system of algebras**: the morphism attached to a
relation with itself is the identity, and the morphisms compose. -/
structure CDGADirectedSystem (A : ∀ i, CDGAStructure R (X i))
    (φ : ∀ i j, i ≤ j → CDGAHom (A i) (A j)) : Prop where
  /-- The morphism of a reflexive relation is the identity. -/
  map_self : ∀ (i : ι) (h : i ≤ i) (n : ℕ) (x : X i n), (φ i i h).toFun n x = x
  /-- The morphisms compose. -/
  map_map : ∀ (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) (n : ℕ) (x : X i n),
    (φ j k hjk).toFun n ((φ i j hij).toFun n x) = (φ i k (hij.trans hjk)).toFun n x

variable (φ : ∀ i j, i ≤ j → CDGAHom (A i) (A j))

/-- The transition maps of the directed system in a given degree. -/
def degTransition (n : ℕ) (i j : ι) (h : i ≤ j) : X i n →ₗ[R] X j n := (φ i j h).mapₗ n

/-- **The direct limit of a directed system of algebras in a given degree.** -/
abbrev colimDeg (n : ℕ) := Module.DirectLimit (fun i => X i n) (degTransition φ n)

omit [DecidableEq ι] in
theorem directedSystem_deg (hsys : CDGADirectedSystem A φ) (n : ℕ) :
    DirectedSystem (fun i => X i n) (fun i j h => degTransition φ n i j h) where
  map_self := by
    intro i x
    exact hsys.map_self i le_rfl n x
  map_map := by
    intro k j i hij hjk x
    exact hsys.map_map i j k hij hjk n x

/-- **The differential on the direct limit.** -/
noncomputable def colimD (n : ℕ) : colimDeg φ n →ₗ[R] colimDeg φ (n + 1) :=
  Module.DirectLimit.map (fun i => (A i).dₗ n) (fun i j h => by
    refine LinearMap.ext fun x => ?_
    show (A j).d n ((φ i j h).toFun n x) = (φ i j h).toFun (n + 1) ((A i).d n x)
    rw [(φ i j h).map_d n x])

@[simp]
theorem colimD_of (n : ℕ) (i : ι) (x : X i n) :
    colimD φ n (Module.DirectLimit.of R ι (fun i => X i n) (degTransition φ n) i x) =
      Module.DirectLimit.of R ι (fun i => X i (n + 1)) (degTransition φ (n + 1)) i
        ((A i).d n x) :=
  Module.DirectLimit.map_apply_of _ _ _

variable [IsDirectedOrder ι] [Nonempty ι]

/-- **The differential on the direct limit squares to zero**, so the limit of a directed system of
algebras is a differential graded module. -/
theorem colimD_comp (_hsys : CDGADirectedSystem A φ) (n : ℕ) :
    (colimD φ (n + 1)).comp (colimD φ n) = 0 := by
  haveI := directedSystem_deg φ _hsys n
  refine LinearMap.ext fun ξ => ?_
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of ξ
  show colimD φ (n + 1) (colimD φ n
    (Module.DirectLimit.of R ι (fun i => X i n) (degTransition φ n) i x)) = 0
  rw [colimD_of, colimD_of, (A i).d_d n x]
  exact map_zero _

end Colimit

end GaloisForLFunctions.HTGeometry
