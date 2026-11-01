import GaloisForLFunctions.HeckeKreinToeplitz.Index.NegativeColumnHilbertSpace
import GaloisForLFunctions.HeckeKreinToeplitz.Index.CompletingIndexOneIsometries

/-!
# The complete index-one column representation

Translations on kernel columns extend to the completion of the positive
orthogonal complement. Their group law and form preservation pass through
the dense embedding. No bound on the original kernel is required.
-/

noncomputable section
set_option autoImplicit false
open UniformSpace Complex

namespace GaloisForLFunctions.HeckeKreinToeplitz.NegativeColumn

variable {G : Type*} [Group G] {k : G → ℂ}

private theorem column_action_mul (a b : G) (v : kernelColumnSpan k) :
    kernelColumnRepresentation k (a * b) v =
      kernelColumnRepresentation k a (kernelColumnRepresentation k b v) :=
  congrArg (fun f : Module.End ℂ (kernelColumnSpan k) => f v)
    (map_mul (kernelColumnRepresentation k) a b)

/-- The invertible algebraic translation on columns. -/
def columnAction (a : G) : kernelColumnSpan k ≃ₗ[ℂ] kernelColumnSpan k where
  toLinearMap := kernelColumnRepresentation k a
  invFun := kernelColumnRepresentation k a⁻¹
  left_inv v := by
    change kernelColumnRepresentation k a⁻¹ (kernelColumnRepresentation k a v) = v
    rw [← column_action_mul, inv_mul_cancel, map_one]
    rfl
  right_inv v := by
    change kernelColumnRepresentation k a (kernelColumnRepresentation k a⁻¹ v) = v
    rw [← column_action_mul, mul_inv_cancel, map_one]
    rfl

variable (hk : IsHermKernel k) (hi : negIndex k ≤ 1)
    (e : kernelColumnSpan k) (he : kernelColumnPairing k e e = -1)

/-- The positive Hilbert space obtained by completing the orthogonal complement. -/
abbrev Hilbert := Completion (Space hk hi e he)

/-- Dense realization of columns in a complete space with one negative direction. -/
def embedding : kernelColumnSpan k →ₗ[ℂ] (Hilbert hk hi e he × ℂ) :=
  IndexOne.completionEmbedding.comp (splitting hk hi e he).toLinearMap

theorem embedding_dense : DenseRange (embedding hk hi e he) := by
  apply (IndexOne.completionEmbedding_dense (H := Space hk hi e he)).mono
  rintro y ⟨v, rfl⟩
  refine ⟨(splitting hk hi e he).symm v, ?_⟩
  simp only [embedding, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply]

theorem embedding_pairing (v w : kernelColumnSpan k) :
    IndexOne.pairing (embedding hk hi e he v) (embedding hk hi e he w) =
      kernelColumnPairing k v w := by
  rw [embedding, LinearMap.comp_apply, LinearMap.comp_apply,
    IndexOne.completionEmbedding_pairing]
  exact pairing_splitting hk hi e he v w

/-- Translation expressed in positive and negative coordinates. -/
def algebraicAction (a : G) :
    (Space hk hi e he × ℂ) ≃ₗ[ℂ] (Space hk hi e he × ℂ) :=
  ((splitting hk hi e he).symm.trans (columnAction a)).trans (splitting hk hi e he)

theorem algebraicAction_pairing (a : G) (v w : Space hk hi e he × ℂ) :
    IndexOne.pairing (algebraicAction hk hi e he a v) (algebraicAction hk hi e he a w) =
      IndexOne.pairing v w := by
  change IndexOne.pairing
    (splitting hk hi e he (kernelColumnRepresentation k a ((splitting hk hi e he).symm v)))
    (splitting hk hi e he (kernelColumnRepresentation k a ((splitting hk hi e he).symm w))) = _
  rw [pairing_splitting, kernelColumnPairing_invariant hk, pairing_splitting_symm]

/-- Bounded invertible translation on the completed column space. -/
def action (a : G) : (Hilbert hk hi e he × ℂ) ≃L[ℂ] (Hilbert hk hi e he × ℂ) :=
  IndexOne.completedIsometry (algebraicAction hk hi e he a)
    (algebraicAction_pairing hk hi e he a)

theorem action_embedding (a : G) (v : kernelColumnSpan k) :
    action hk hi e he a (embedding hk hi e he v) =
      embedding hk hi e he (kernelColumnRepresentation k a v) := by
  unfold action embedding
  rw [LinearMap.comp_apply, IndexOne.completedIsometry_embedding, LinearMap.comp_apply]
  congr 1
  change splitting hk hi e he (kernelColumnRepresentation k a
    ((splitting hk hi e he).symm (splitting hk hi e he v))) =
      splitting hk hi e he (kernelColumnRepresentation k a v)
  rw [LinearEquiv.symm_apply_apply]

theorem action_pairing (a : G) (v w : Hilbert hk hi e he × ℂ) :
    IndexOne.pairing (action hk hi e he a v) (action hk hi e he a w) =
      IndexOne.pairing v w :=
  IndexOne.completedIsometry_pairing _ _ v w

theorem action_one (v : Hilbert hk hi e he × ℂ) : action hk hi e he 1 v = v := by
  refine (embedding_dense hk hi e he).induction_on v
    (isClosed_eq (action hk hi e he 1).continuous continuous_id) ?_
  intro x
  rw [action_embedding, map_one]
  rfl

theorem action_mul (a b : G) (v : Hilbert hk hi e he × ℂ) :
    action hk hi e he (a * b) v = action hk hi e he a (action hk hi e he b v) := by
  refine (embedding_dense hk hi e he).induction_on v
    (isClosed_eq (action hk hi e he (a * b)).continuous
      ((action hk hi e he a).continuous.comp (action hk hi e he b).continuous)) ?_
  intro x
  rw [action_embedding, action_embedding, action_embedding, column_action_mul]

theorem action_point (a g : G) :
    action hk hi e he a (embedding hk hi e he (kernelColumnPoint k g)) =
      embedding hk hi e he (kernelColumnPoint k (a * g)) := by
  rw [action_embedding, kernelColumnRepresentation_point]

end GaloisForLFunctions.HeckeKreinToeplitz.NegativeColumn
