import Mathlib.Algebra.Colimit.Module
import Mathlib.LinearAlgebra.Pi

/-!
# A finite product of direct limits is the direct limit of the products

Over a directed index a finite family of stages has a common upper bound, which is exactly what is
needed to turn a finite tuple of elements coming from different stages into a tuple coming from one
stage.  So a finite product commutes with a filtered colimit of modules.

* `GaloisForLFunctions.HTGeometry.piTransition` : the transition maps of the product system.
* `GaloisForLFunctions.HTGeometry.directLimitPi` : the comparison, an isomorphism.
-/

universe u v w r

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {ι : Type v} [Preorder ι] [DecidableEq ι]
  {ρ : Type r} [Fintype ρ]
  {G : ρ → ι → Type w} [∀ p i, AddCommGroup (G p i)] [∀ p i, Module R (G p i)]
  (f : ∀ (p : ρ) (i j : ι), i ≤ j → G p i →ₗ[R] G p j)

/-- The transition maps of the product of a finite family of directed systems. -/
def piTransition (i j : ι) (h : i ≤ j) : (∀ p, G p i) →ₗ[R] (∀ p, G p j) :=
  LinearMap.pi fun p => (f p i j h).comp (LinearMap.proj p)

omit [DecidableEq ι] [Fintype ρ] in
@[simp] theorem piTransition_apply (i j : ι) (h : i ≤ j) (x : ∀ p, G p i) (p : ρ) :
    piTransition f i j h x p = f p i j h (x p) := rfl

instance piDirectedSystem [∀ p, DirectedSystem (G p) fun i j h => f p i j h] :
    DirectedSystem (fun i => ∀ p, G p i) fun i j h => piTransition f i j h where
  map_self := by
    intro i x
    funext p
    exact DirectedSystem.map_self (f := fun i j h => (f p i j h : G p i → G p j)) (x p)
  map_map := by
    intro k j i hij hjk x
    funext p
    exact DirectedSystem.map_map (f := fun i j h => (f p i j h : G p i → G p j)) hij hjk (x p)

variable [IsDirectedOrder ι] [Nonempty ι]

/-- The comparison from the direct limit of the products to the product of the direct limits. -/
noncomputable def directLimitPiMap :
    Module.DirectLimit (fun i => ∀ p, G p i) (piTransition f) →ₗ[R]
      (∀ p, Module.DirectLimit (G p) (f p)) :=
  Module.DirectLimit.lift R ι _ _
    (fun i => LinearMap.pi fun p =>
      (Module.DirectLimit.of R ι (G p) (f p) i).comp (LinearMap.proj p))
    (fun i j hij x => by
      funext p
      show Module.DirectLimit.of R ι (G p) (f p) j (f p i j hij (x p))
        = Module.DirectLimit.of R ι (G p) (f p) i (x p)
      exact Module.DirectLimit.of_f)

omit [Fintype ρ] [IsDirectedOrder ι] [Nonempty ι] in
@[simp] theorem directLimitPiMap_of (i : ι) (x : ∀ p, G p i) (p : ρ) :
    directLimitPiMap f
        (Module.DirectLimit.of R ι (fun i => ∀ p, G p i) (piTransition f) i x) p
      = Module.DirectLimit.of R ι (G p) (f p) i (x p) := by
  simp only [directLimitPiMap, Module.DirectLimit.lift_of]
  rfl

variable [∀ p, DirectedSystem (G p) fun i j h => f p i j h]

theorem directLimitPiMap_injective : Function.Injective (directLimitPiMap f) := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
  have hcomp : ∀ p, Module.DirectLimit.of R ι (G p) (f p) i (x p) = 0 := by
    intro p
    rw [← directLimitPiMap_of f i x p, hz]
    rfl
  choose j hij hj using fun p => Module.DirectLimit.of.zero_exact (hcomp p)
  obtain ⟨m, hm⟩ := Finset.exists_le (insert i (Finset.image j Finset.univ))
  have him : i ≤ m := hm i (Finset.mem_insert_self _ _)
  have hjm : ∀ p, j p ≤ m := fun p =>
    hm _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem j (Finset.mem_univ p)))
  have hzero : piTransition f i m him x = 0 := by
    funext p
    show f p i m him (x p) = 0
    rw [← DirectedSystem.map_map (f := fun i j h => (f p i j h : G p i → G p j))
      (hij p) (hjm p) (x p)]
    show f p (j p) m (hjm p) (f p i (j p) (hij p) (x p)) = 0
    rw [hj p]
    exact (f p (j p) m (hjm p)).map_zero
  have hof : Module.DirectLimit.of R ι (fun i => ∀ p, G p i) (piTransition f) m
      (piTransition f i m him x)
    = Module.DirectLimit.of R ι (fun i => ∀ p, G p i) (piTransition f) i x :=
    Module.DirectLimit.of_f
  rw [← hof, hzero]
  exact map_zero _

omit [∀ p, DirectedSystem (G p) fun i j h => f p i j h] in
theorem directLimitPiMap_surjective : Function.Surjective (directLimitPiMap f) := by
  classical
  intro ξ
  choose i x hx using fun p => Module.DirectLimit.exists_of (ξ p)
  obtain ⟨m, hm⟩ := Finset.exists_le (Finset.image i Finset.univ)
  have him : ∀ p, i p ≤ m := fun p =>
    hm _ (Finset.mem_image_of_mem i (Finset.mem_univ p))
  refine ⟨Module.DirectLimit.of R ι (fun i => ∀ p, G p i) (piTransition f) m
    (fun p => f p (i p) m (him p) (x p)), ?_⟩
  funext p
  rw [directLimitPiMap_of]
  show Module.DirectLimit.of R ι (G p) (f p) m (f p (i p) m (him p) (x p)) = ξ p
  rw [Module.DirectLimit.of_f]
  exact hx p

/-- **A finite product commutes with a filtered colimit of modules.** -/
noncomputable def directLimitPi :
    Module.DirectLimit (fun i => ∀ p, G p i) (piTransition f) ≃ₗ[R]
      (∀ p, Module.DirectLimit (G p) (f p)) :=
  LinearEquiv.ofBijective (directLimitPiMap f)
    ⟨directLimitPiMap_injective f, directLimitPiMap_surjective f⟩

end GaloisForLFunctions.HTGeometry
