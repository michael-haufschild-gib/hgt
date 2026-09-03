import Mathlib.RingTheory.Length

/-!
# Length additivity for nested submodules over arbitrary rings

For nested submodules `P ≤ Q ≤ M`, this leaf constructs the exact quotient sequence
`Q/P → M/P → M/Q` without assuming commutative scalars.  Module length is therefore additive
across every such interval.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [Ring R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The smaller submodule `P` viewed inside `Q`. -/
def nestedSubmoduleInside (P Q : Submodule R M) : Submodule R Q :=
  Submodule.comap Q.subtype P

/-- The intermediate layer `Q/P` included in the finer quotient `M/P`. -/
def nestedSubmoduleLayerInclusion (P Q : Submodule R M) :
    (Q ⧸ nestedSubmoduleInside P Q) →ₗ[R] M ⧸ P :=
  Submodule.mapQ (nestedSubmoduleInside P Q) P Q.subtype (by
    intro x hx
    exact hx)

/-- The intermediate-layer inclusion is injective. -/
theorem nestedSubmoduleLayerInclusion_injective (P Q : Submodule R M) :
    Function.Injective (nestedSubmoduleLayerInclusion P Q) := by
  intro q q'
  refine Submodule.Quotient.induction_on (nestedSubmoduleInside P Q) q ?_
  intro x
  refine Submodule.Quotient.induction_on (nestedSubmoduleInside P Q) q' ?_
  intro y hxy
  rw [Submodule.Quotient.eq]
  change (x : M) - (y : M) ∈ P
  change Submodule.Quotient.mk (p := P) (x : M) =
    Submodule.Quotient.mk (p := P) (y : M) at hxy
  exact (Submodule.Quotient.eq P).1 hxy

/-- Canonical transition from the finer quotient `M/P` to the coarser quotient `M/Q`. -/
def nestedSubmoduleQuotientTransition (P Q : Submodule R M) (h : P ≤ Q) :
    (M ⧸ P) →ₗ[R] M ⧸ Q :=
  Submodule.mapQ P Q LinearMap.id (by simpa using h)

/-- The canonical nested-quotient transition is surjective. -/
theorem nestedSubmoduleQuotientTransition_surjective
    (P Q : Submodule R M) (h : P ≤ Q) :
    Function.Surjective (nestedSubmoduleQuotientTransition P Q h) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective Q y
  exact ⟨Submodule.Quotient.mk z, rfl⟩

/-- The intermediate layer is exactly the kernel of the nested-quotient transition. -/
theorem nestedSubmoduleQuotient_exact
    (P Q : Submodule R M) (h : P ≤ Q) :
    Function.Exact (nestedSubmoduleLayerInclusion P Q)
      (nestedSubmoduleQuotientTransition P Q h) := by
  rw [LinearMap.exact_iff]
  rw [nestedSubmoduleQuotientTransition, Submodule.ker_mapQ]
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    let x : Q := ⟨z, hz⟩
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [nestedSubmoduleLayerInclusion, Submodule.mapQ_apply]
    rfl
  · rintro ⟨q', hq'⟩
    revert hq'
    refine Submodule.Quotient.induction_on (nestedSubmoduleInside P Q) q' ?_
    intro x hq'
    refine ⟨x, x.property, ?_⟩
    rw [nestedSubmoduleLayerInclusion, Submodule.mapQ_apply] at hq'
    exact hq'

/-- Module length is additive across a nested submodule interval over any scalar ring. -/
theorem nestedSubmoduleQuotient_length_add
    (P Q : Submodule R M) (h : P ≤ Q) :
    Module.length R (M ⧸ P) =
      Module.length R (Q ⧸ nestedSubmoduleInside P Q) +
        Module.length R (M ⧸ Q) := by
  exact Module.length_eq_add_of_exact
    (nestedSubmoduleLayerInclusion P Q)
    (nestedSubmoduleQuotientTransition P Q h)
    (nestedSubmoduleLayerInclusion_injective P Q)
    (nestedSubmoduleQuotientTransition_surjective P Q h)
    (nestedSubmoduleQuotient_exact P Q h)

/-- A linear equivalence onto the intermediate submodule identifies its quotient layer. -/
def nestedSubmoduleLayerQuotientEquiv
    {A : Type*} [AddCommGroup A] [Module R A]
    (S : Submodule R A) (P Q : Submodule R M)
    (e : A ≃ₗ[R] Q)
    (hmap : Submodule.map e.toLinearMap S = nestedSubmoduleInside P Q) :
    (A ⧸ S) ≃ₗ[R] (Q ⧸ nestedSubmoduleInside P Q) :=
  Submodule.Quotient.equiv _ _ e hmap

/-- Transporting an intermediate layer through a linear equivalence preserves module length. -/
theorem nestedSubmoduleLayerQuotient_length_eq
    {A : Type*} [AddCommGroup A] [Module R A]
    (S : Submodule R A) (P Q : Submodule R M)
    (e : A ≃ₗ[R] Q)
    (hmap : Submodule.map e.toLinearMap S = nestedSubmoduleInside P Q) :
    Module.length R (Q ⧸ nestedSubmoduleInside P Q) =
      Module.length R (A ⧸ S) :=
  (nestedSubmoduleLayerQuotientEquiv S P Q e hmap).length_eq.symm

end

end GaloisForLFunctions.HTGeometry
