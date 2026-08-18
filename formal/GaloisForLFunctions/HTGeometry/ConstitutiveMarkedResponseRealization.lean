import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Tactic

/-!
# Marked response realization and doctrine memory

A law is tested by a complete family of linear probes on a source history space.  If two
surjective state presentations have the same complete response and their probes separate states,
then the presentations have the same synthesis kernel and are related by one unique marked linear
equivalence.  This is the finite-linear presentation-invariance gate for response mechanics.

Restricting the legal doctrine leaves a reachable subspace `R` and an unobservable subspace `N`.
Rank-nullity gives an exact conservation law: lost memory is the sum of unreachable and
unobservable dimensions.  Parallel response fusion is represented by tensor product, so its
minimal doctrine memory is bounded by the product of the factor memories.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

section MarkedReconstruction

variable {K S V W I : Type*} [Field K]
  [AddCommGroup S] [Module K S]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- A probe family is complete when its common kernel is zero. -/
def LinearProbeFamilySeparates (p : I → V →ₗ[K] K) : Prop :=
  ∀ x, (∀ i, p i x = 0) → x = 0

/-- Equal complete responses force equal synthesis kernels. -/
theorem kernel_eq_of_complete_linear_response
    (f : S →ₗ[K] V) (g : S →ₗ[K] W)
    (p : I → V →ₗ[K] K) (q : I → W →ₗ[K] K)
    (hp : LinearProbeFamilySeparates p) (hq : LinearProbeFamilySeparates q)
    (hresponse : ∀ i, (p i).comp f = (q i).comp g) :
    f.ker = g.ker := by
  ext x
  constructor
  · intro hx
    apply LinearMap.mem_ker.mpr
    apply hq
    intro i
    have hpoint := congrArg (fun h : S →ₗ[K] K => h x) (hresponse i)
    change p i (f x) = q i (g x) at hpoint
    rw [LinearMap.mem_ker.mp hx] at hpoint
    simpa using hpoint.symm
  · intro hx
    apply LinearMap.mem_ker.mpr
    apply hp
    intro i
    have hpoint := congrArg (fun h : S →ₗ[K] K => h x) (hresponse i)
    change p i (f x) = q i (g x) at hpoint
    rw [LinearMap.mem_ker.mp hx] at hpoint
    simpa using hpoint

/-- The canonical marked equivalence reconstructed from one complete response. -/
noncomputable def markedLinearResponseEquiv
    (f : S →ₗ[K] V) (g : S →ₗ[K] W)
    (p : I → V →ₗ[K] K) (q : I → W →ₗ[K] K)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hp : LinearProbeFamilySeparates p) (hq : LinearProbeFamilySeparates q)
    (hresponse : ∀ i, (p i).comp f = (q i).comp g) :
    V ≃ₗ[K] W :=
  ((f.quotKerEquivOfSurjective hf).symm.trans
    (Submodule.quotEquivOfEq _ _
      (kernel_eq_of_complete_linear_response f g p q hp hq hresponse))).trans
    (g.quotKerEquivOfSurjective hg)

/-- The reconstructed equivalence intertwines the two synthesis maps. -/
theorem markedLinearResponseEquiv_apply
    (f : S →ₗ[K] V) (g : S →ₗ[K] W)
    (p : I → V →ₗ[K] K) (q : I → W →ₗ[K] K)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hp : LinearProbeFamilySeparates p) (hq : LinearProbeFamilySeparates q)
    (hresponse : ∀ i, (p i).comp f = (q i).comp g) (x : S) :
    markedLinearResponseEquiv f g p q hf hg hp hq hresponse (f x) = g x := by
  show (g.quotKerEquivOfSurjective hg)
    ((Submodule.quotEquivOfEq _ _
      (kernel_eq_of_complete_linear_response f g p q hp hq hresponse))
      ((f.quotKerEquivOfSurjective hf).symm (f x))) = g x
  have h1 : (f.quotKerEquivOfSurjective hf).symm (f x) =
      Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [h1]
  rfl

/-- The reconstructed equivalence preserves every marked probe. -/
theorem markedLinearResponseEquiv_preserves_probes
    (f : S →ₗ[K] V) (g : S →ₗ[K] W)
    (p : I → V →ₗ[K] K) (q : I → W →ₗ[K] K)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hp : LinearProbeFamilySeparates p) (hq : LinearProbeFamilySeparates q)
    (hresponse : ∀ i, (p i).comp f = (q i).comp g)
    (i : I) (v : V) :
    q i (markedLinearResponseEquiv f g p q hf hg hp hq hresponse v) = p i v := by
  obtain ⟨x, rfl⟩ := hf v
  rw [markedLinearResponseEquiv_apply]
  have hpoint := congrArg (fun h : S →ₗ[K] K => h x) (hresponse i)
  change p i (f x) = q i (g x) at hpoint
  exact hpoint.symm

/-- No second marked equivalence can intertwine the same complete response presentation. -/
theorem markedLinearResponseEquiv_unique
    (f : S →ₗ[K] V) (g : S →ₗ[K] W)
    (p : I → V →ₗ[K] K) (q : I → W →ₗ[K] K)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hp : LinearProbeFamilySeparates p) (hq : LinearProbeFamilySeparates q)
    (hresponse : ∀ i, (p i).comp f = (q i).comp g)
    (e : V ≃ₗ[K] W) (he : ∀ x, e (f x) = g x) :
    e = markedLinearResponseEquiv f g p q hf hg hp hq hresponse := by
  ext v
  obtain ⟨x, rfl⟩ := hf v
  rw [he, markedLinearResponseEquiv_apply]

/-- **Unique marked reconstruction.** Complete response data determine the minimal presentation. -/
theorem existsUnique_markedLinearResponseEquiv
    (f : S →ₗ[K] V) (g : S →ₗ[K] W)
    (p : I → V →ₗ[K] K) (q : I → W →ₗ[K] K)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hp : LinearProbeFamilySeparates p) (hq : LinearProbeFamilySeparates q)
    (hresponse : ∀ i, (p i).comp f = (q i).comp g) :
    ∃! e : V ≃ₗ[K] W, ∀ x, e (f x) = g x := by
  refine ⟨markedLinearResponseEquiv f g p q hf hg hp hq hresponse,
    markedLinearResponseEquiv_apply f g p q hf hg hp hq hresponse, ?_⟩
  intro e he
  exact markedLinearResponseEquiv_unique f g p q hf hg hp hq hresponse e he

end MarkedReconstruction

section DoctrineMemory

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- **Doctrine-memory conservation.**

For reachable memory `R` and its unobservable part `N`, total state memory minus restricted
minimal memory is exactly unreachable memory plus unobservable memory.
-/
theorem doctrineMemoryConservation (R : Submodule K V) (N : Submodule K R) :
    Module.finrank K V - Module.finrank K (R ⧸ N) =
      (Module.finrank K V - Module.finrank K R) + Module.finrank K N := by
  have hR := Submodule.finrank_le R
  have hQ := Submodule.finrank_quotient_add_finrank N
  omega

end DoctrineMemory

section TensorFusion

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Scalar response of a parallel tensor realization. -/
def tensorLinearResponse (p : V →ₗ[K] K) (q : W →ₗ[K] K) :
    TensorProduct K V W →ₗ[K] K :=
  (TensorProduct.lid K K).toLinearMap.comp (TensorProduct.map p q)

/-- Parallel tensor formation multiplies the two factor responses. -/
theorem tensorLinearResponse_tmul
    (p : V →ₗ[K] K) (q : W →ₗ[K] K) (v : V) (w : W) :
    tensorLinearResponse p q (v ⊗ₜ[K] w) = p v * q w := by
  simp [tensorLinearResponse]

/-- A restricted tensor presentation cannot have more minimal memory than the product carrier. -/
theorem tensorDoctrineMemory_le
    [FiniteDimensional K V] [FiniteDimensional K W]
    (R : Submodule K (TensorProduct K V W)) (N : Submodule K R) :
    Module.finrank K (R ⧸ N) ≤ Module.finrank K V * Module.finrank K W := by
  have hQ := Submodule.finrank_quotient_add_finrank N
  have hQR : Module.finrank K (R ⧸ N) ≤ Module.finrank K R := by omega
  calc
    Module.finrank K (R ⧸ N) ≤ Module.finrank K R := hQR
    _ ≤ Module.finrank K (TensorProduct K V W) := Submodule.finrank_le R
    _ = Module.finrank K V * Module.finrank K W := Module.finrank_tensorProduct

end TensorFusion

end GaloisForLFunctions.HTGeometry
