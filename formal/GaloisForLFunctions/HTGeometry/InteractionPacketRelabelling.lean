import GaloisForLFunctions.HTGeometry.FinsetPosetMobiusBridge
import GaloisForLFunctions.HTGeometry.DisconnectedLocalAffineFactorization

/-!
# Relabelling disjoint interaction packets

A disjoint union of two finite label packets is canonically equivalent to the
subtype of their union.  Coupling vectors, restricted packets, affine matrix
families, and Boolean Möbius responses transport exactly across this
equivalence.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Canonical equivalence from two disjoint label packets to their union. -/
def splitInteractionLabelEquiv
    {E : Type*} [DecidableEq E]
    (left right : Finset E) (hlabel : Disjoint left right) :
    Sum {e : E // e ∈ left} {e : E // e ∈ right} ≃
      {e : E // e ∈ left ∪ right} where
  toFun
    | Sum.inl e => ⟨e.1, Finset.mem_union_left right e.2⟩
    | Sum.inr e => ⟨e.1, Finset.mem_union_right left e.2⟩
  invFun e := if he : e.1 ∈ left then Sum.inl ⟨e.1, he⟩ else
    Sum.inr ⟨e.1, (Finset.mem_union.mp e.2).resolve_left he⟩
  left_inv e := by
    cases e with
    | inl e =>
        simp
    | inr e =>
        have hnot : e.1 ∉ left := by
          intro he
          exact Finset.disjoint_left.mp hlabel he e.2
        simp [hnot]
  right_inv e := by
    by_cases he : e.1 ∈ left
    · simp [he]
    · simp [he]

@[simp]
theorem splitInteractionLabelEquiv_apply_inl
    {E : Type*} [DecidableEq E]
    (left right : Finset E) (hlabel : Disjoint left right)
    (e : {e : E // e ∈ left}) :
    (splitInteractionLabelEquiv left right hlabel (Sum.inl e)).1 =
      e.1 := rfl

@[simp]
theorem splitInteractionLabelEquiv_apply_inr
    {E : Type*} [DecidableEq E]
    (left right : Finset E) (hlabel : Disjoint left right)
    (e : {e : E // e ∈ right}) :
    (splitInteractionLabelEquiv left right hlabel (Sum.inr e)).1 =
      e.1 := rfl

/-- Transport a coupling vector along a label equivalence. -/
def relabelCoupling {P Q : Type*} (e : P ≃ Q)
    (z : P → ℂ) : Q → ℂ :=
  fun q => z (e.symm q)

@[simp]
theorem relabelCoupling_apply
    {P Q : Type*} (e : P ≃ Q) (z : P → ℂ) (q : Q) :
    relabelCoupling e z q = z (e.symm q) := rfl

@[simp]
theorem relabelCoupling_zero
    {P Q : Type*} (e : P ≃ Q) :
    relabelCoupling e (0 : P → ℂ) = 0 := by
  rfl

@[simp]
theorem relabelCoupling_symm_relabelCoupling
    {P Q : Type*} (e : P ≃ Q) (z : P → ℂ) :
    relabelCoupling e.symm (relabelCoupling e z) = z := by
  funext p
  simp [relabelCoupling]

@[simp]
theorem relabelCoupling_restrictInteractionPacket
    {P Q : Type*} [Fintype P] [Fintype Q]
    [DecidableEq P] [DecidableEq Q]
    (e : P ≃ Q) (packet : Finset P) (z : P → ℂ) :
    relabelCoupling e (restrictInteractionPacket packet z) =
      restrictInteractionPacket (e.finsetCongr packet)
        (relabelCoupling e z) := by
  funext q
  simp [relabelCoupling, restrictInteractionPacket]

/-- Coupling transport is analytic. -/
theorem relabelCoupling_analyticAt
    {P Q : Type*} [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q]
    (e : P ≃ Q) :
    AnalyticAt ℂ (relabelCoupling e : (P → ℂ) → Q → ℂ) 0 := by
  apply AnalyticAt.pi
  intro q
  exact (ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : P => ℂ) (e.symm q)).analyticAt 0

/-- Coupling transport preserves the zero-coupling germ. -/
theorem relabelCoupling_tendsto_zero
    {P Q : Type*} [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q]
    (e : P ≃ Q) :
    Tendsto (relabelCoupling e : (P → ℂ) → Q → ℂ)
      (𝓝 0) (𝓝 0) := by
  have hc := (relabelCoupling_analyticAt e).continuousAt
  simpa using hc

namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-- Relabelling a split packet as the subtype of its union leaves the global
affine matrix family unchanged. -/
theorem affineMatrixFamily_relabel_splitPacket
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (left right : Finset E) (hlabel : Disjoint left right)
    (z : Sum {e : E // e ∈ left} {e : E // e ∈ right} → ℂ) :
    affineMatrixFamily
      (Matrix.diagonal (onsiteProductEnergy onsite))
      (fun e : {e : E // e ∈ left ∪ right} =>
        L.globalInteraction e.1)
      (relabelCoupling (splitInteractionLabelEquiv left right hlabel) z) =
    affineMatrixFamily
      (Matrix.diagonal (onsiteProductEnergy onsite))
      (L.splitPacketGlobalInteraction left right) z := by
  unfold affineMatrixFamily
  congr 1
  symm
  apply Fintype.sum_equiv
    (splitInteractionLabelEquiv left right hlabel)
  intro p
  cases p <;>
    simp [relabelCoupling, splitPacketGlobalInteraction]

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
