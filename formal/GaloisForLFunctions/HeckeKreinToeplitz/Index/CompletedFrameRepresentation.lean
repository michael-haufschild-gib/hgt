import GaloisForLFunctions.HeckeKreinToeplitz.Index.NegativeFrameHilbertSpace
import GaloisForLFunctions.HeckeKreinToeplitz.Index.CompletedColumnRepresentation
import GaloisForLFunctions.HeckeKreinToeplitz.Index.CompletingFiniteNegativeIsometries

/-!
# The complete finite-index column representation

Translations on kernel columns extend to the completion of the positive
orthogonal complement. Their group law and form preservation pass through
the dense embedding. No bound on the original kernel is required.
-/

noncomputable section
set_option autoImplicit false
open UniformSpace Complex

namespace GaloisForLFunctions.HeckeKreinToeplitz.NegativeFrame

variable {G : Type*} [Group G] {k : G → ℂ}

private theorem column_action_mul (a b : G) (v : kernelColumnSpan k) :
    kernelColumnRepresentation k (a * b) v =
      kernelColumnRepresentation k a (kernelColumnRepresentation k b v) :=
  congrArg (fun f : Module.End ℂ (kernelColumnSpan k) => f v)
    (map_mul (kernelColumnRepresentation k) a b)

variable {m : ℕ} (hk : IsHermKernel k) (e : Fin m → kernelColumnSpan k)
    (he : IsNegativeColumnFrame e)
    (hp : ∀ v : kernelColumnSpan k, (∀ i, kernelColumnPairing k (e i) v = 0) →
      0 ≤ (kernelColumnPairing k v v).re)

/-- The positive Hilbert space obtained by completing the orthogonal complement. -/
abbrev Hilbert := Completion (Space hk e he hp)

/-- Dense realization of columns in a complete space with a finite negative factor. -/
def embedding : kernelColumnSpan k →ₗ[ℂ] (Hilbert hk e he hp × EuclideanSpace ℂ (Fin m)) :=
  FiniteNegative.completionEmbedding.comp (splitting hk e he hp).toLinearMap

theorem embedding_dense : DenseRange (embedding hk e he hp) := by
  apply (FiniteNegative.completionEmbedding_dense (H := Space hk e he hp)).mono
  rintro y ⟨v, rfl⟩
  refine ⟨(splitting hk e he hp).symm v, ?_⟩
  simp only [embedding, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply]

theorem embedding_pairing (v w : kernelColumnSpan k) :
    FiniteNegative.pairing (embedding hk e he hp v) (embedding hk e he hp w) =
      kernelColumnPairing k v w := by
  rw [embedding, LinearMap.comp_apply, LinearMap.comp_apply,
    FiniteNegative.completionEmbedding_pairing]
  exact pairing_splitting hk e he hp v w

/-- Negative coordinates retain the finite column pairings. -/
theorem embedding_snd (v : kernelColumnSpan k) (i : Fin m) :
    (embedding hk e he hp v).2 i = -kernelColumnPairing k (e i) v := rfl

theorem embedding_injective : Function.Injective (embedding hk e he hp) := by
  intro v w hvw
  apply sub_eq_zero.mp
  apply kernelColumnPairing_nondegenerate hk
  intro z
  rw [map_sub, ← embedding_pairing hk e he hp z v, ← embedding_pairing hk e he hp z w,
    hvw, sub_self]

/-- Translation expressed in positive and negative coordinates. -/
def algebraicAction (a : G) :
    (Space hk e he hp × EuclideanSpace ℂ (Fin m)) ≃ₗ[ℂ] (Space hk e he hp × EuclideanSpace ℂ (Fin m)) :=
  ((splitting hk e he hp).symm.trans (NegativeColumn.columnAction a)).trans (splitting hk e he hp)

theorem algebraicAction_pairing (a : G) (v w : Space hk e he hp × EuclideanSpace ℂ (Fin m)) :
    FiniteNegative.pairing (algebraicAction hk e he hp a v) (algebraicAction hk e he hp a w) =
      FiniteNegative.pairing v w := by
  change FiniteNegative.pairing
    (splitting hk e he hp (kernelColumnRepresentation k a ((splitting hk e he hp).symm v)))
    (splitting hk e he hp (kernelColumnRepresentation k a ((splitting hk e he hp).symm w))) = _
  rw [pairing_splitting, kernelColumnPairing_invariant hk, pairing_splitting_symm]

/-- Bounded invertible translation on the completed column space. -/
def action (a : G) : (Hilbert hk e he hp × EuclideanSpace ℂ (Fin m)) ≃L[ℂ] (Hilbert hk e he hp × EuclideanSpace ℂ (Fin m)) :=
  FiniteNegative.completedIsometry (algebraicAction hk e he hp a)
    (algebraicAction_pairing hk e he hp a)

theorem action_embedding (a : G) (v : kernelColumnSpan k) :
    action hk e he hp a (embedding hk e he hp v) =
      embedding hk e he hp (kernelColumnRepresentation k a v) := by
  unfold action embedding
  rw [LinearMap.comp_apply, FiniteNegative.completedIsometry_embedding, LinearMap.comp_apply]
  congr 1
  change splitting hk e he hp (kernelColumnRepresentation k a
    ((splitting hk e he hp).symm (splitting hk e he hp v))) =
      splitting hk e he hp (kernelColumnRepresentation k a v)
  rw [LinearEquiv.symm_apply_apply]

theorem action_pairing (a : G) (v w : Hilbert hk e he hp × EuclideanSpace ℂ (Fin m)) :
    FiniteNegative.pairing (action hk e he hp a v) (action hk e he hp a w) =
      FiniteNegative.pairing v w :=
  FiniteNegative.completedIsometry_pairing _ _ v w

theorem action_one (v : Hilbert hk e he hp × EuclideanSpace ℂ (Fin m)) : action hk e he hp 1 v = v := by
  refine (embedding_dense hk e he hp).induction_on v
    (isClosed_eq (action hk e he hp 1).continuous continuous_id) ?_
  intro x
  rw [action_embedding, map_one]
  rfl

theorem action_mul (a b : G) (v : Hilbert hk e he hp × EuclideanSpace ℂ (Fin m)) :
    action hk e he hp (a * b) v = action hk e he hp a (action hk e he hp b v) := by
  refine (embedding_dense hk e he hp).induction_on v
    (isClosed_eq (action hk e he hp (a * b)).continuous
      ((action hk e he hp a).continuous.comp (action hk e he hp b).continuous)) ?_
  intro x
  rw [action_embedding, action_embedding, action_embedding, column_action_mul]

theorem action_point (a g : G) :
    action hk e he hp a (embedding hk e he hp (kernelColumnPoint k g)) =
      embedding hk e he hp (kernelColumnPoint k (a * g)) := by
  rw [action_embedding, kernelColumnRepresentation_point]

#print axioms action_pairing
#print axioms action_mul
#print axioms embedding_injective

end GaloisForLFunctions.HeckeKreinToeplitz.NegativeFrame
