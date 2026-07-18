import GaloisForLFunctions.HTGeometry.BaireGenericAvoidance
import GaloisForLFunctions.HTGeometry.AffineCollisionMatroid
import GaloisForLFunctions.HTGeometry.MultivariateHermiteCRT
import GaloisForLFunctions.HTGeometry.MultivariateEntireCompactOpen
import GaloisForLFunctions.HTGeometry.PolynomialEvaluationLemma

/-!
# Generic affine jet packets have the collision matroid

This module packages the exact Baire-category assembly used by the affine jet-packet theorem.
The analytic input consists of the countable determinant defect loci, their closed/empty-interior
certificates (obtained from finite Hermite interpolation), and the algebraic conversion from
determinant avoidance to collision rank and the operator-rank law.  The countable residual
selection and the finite polynomial sampling lemma are proved internally.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology

noncomputable section

/-- Exact analytic interface for a countable affine jet-packet family.  A natural number encodes a
finite decorated differential-monomial packet, so no uncountable coefficient enumeration occurs. -/
structure AffineJetPacketCollisionInput
    (X Λ Frame : Type*) [TopologicalSpace X] [DecidableEq Frame]
    (frame : Λ → Frame) where
  defect : ℕ → Set X
  orbitRank : X → Finset Λ → ℕ
  operatorRankLaw : X → Prop
  defect_closed : ∀ n, IsClosed (defect n)
  defect_interior_empty : ∀ n, interior (defect n) = ∅
  collisionRank_of_avoids : ∀ f,
    (∀ n, f ∉ defect n) → ∀ E, orbitRank f E = (E.image frame).card
  operatorRank_of_avoids : ∀ f, (∀ n, f ∉ defect n) → operatorRankLaw f

/-- The residual source set: every finite decorated-monomial determinant is nonzero. -/
def affineJetPacketResidualSet
    {X Λ Frame : Type*} [TopologicalSpace X] [DecidableEq Frame]
    {frame : Λ → Frame} (input : AffineJetPacketCollisionInput X Λ Frame frame) : Set X :=
  {f | ∀ n, f ∉ input.defect n}

/-- **Affine jet-packet collision completeness.**  In a Baire source space, the sources avoiding
all countably many finite determinant defects form a dense residual set.  Every source in that set
has orbit rank equal to the number of distinct affine frames and satisfies the complete
constant-coefficient operator-rank law. -/
theorem affineJetPacketCollision_denseResidual_exactMatroid
    {X Λ Frame : Type*} [TopologicalSpace X] [BaireSpace X] [DecidableEq Frame]
    {frame : Λ → Frame} (input : AffineJetPacketCollisionInput X Λ Frame frame) :
    Dense (affineJetPacketResidualSet input) ∧
      affineJetPacketResidualSet input ∈ residual X ∧
      ∀ f ∈ affineJetPacketResidualSet input,
        (∀ E, input.orbitRank f E = (E.image frame).card) ∧ input.operatorRankLaw f := by
  have hnowhere : ∀ n, IsNowhereDense (input.defect n) := fun n =>
    GaloisForLFunctions.isNowhereDense_of_isClosed_of_interior_eq_empty
      (input.defect_closed n) (input.defect_interior_empty n)
  have hdense : Dense (affineJetPacketResidualSet input) := by
    simpa [affineJetPacketResidualSet] using
      GaloisForLFunctions.dense_setOf_forall_notMem_of_isNowhereDense input.defect hnowhere
  have hresidual : affineJetPacketResidualSet input ∈ residual X := by
    have hset : affineJetPacketResidualSet input = ⋂ n, (input.defect n)ᶜ := by
      ext f
      simp [affineJetPacketResidualSet]
    rw [hset]
    exact countable_iInter_mem.mpr fun n => (hnowhere n).isMeagre
  refine ⟨hdense, hresidual, ?_⟩
  intro f hf
  exact ⟨input.collisionRank_of_avoids f hf, input.operatorRank_of_avoids f hf⟩

/-- On every source in the residual set, the packet orbit rank is the extended rank of the actual
collision matroid pulled back along the affine-frame map. -/
theorem affineJetPacketCollision_orbitRank_eq_collisionMatroid_eRk
    {X Λ Frame : Type*} [TopologicalSpace X] [DecidableEq Frame]
    {frame : Λ → Frame} (input : AffineJetPacketCollisionInput X Λ Frame frame)
    {f : X} (hf : f ∈ affineJetPacketResidualSet input) (E : Finset Λ) :
    (input.orbitRank f E : ℕ∞) =
      (affineCollisionMatroid frame).eRk (↑E : Set Λ) := by
  rw [input.collisionRank_of_avoids f hf, affineCollisionMatroid_eRk_finset]

/-- The finite determinant witness used in every defect-density proof: linearly independent
decorated monomials admit a square evaluation packet with nonzero determinant. -/
theorem affineDecoratedMonomials_exist_packet_det_ne_zero
    {K σ : Type*} [Field K] [Infinite K] {n : ℕ}
    (p : Fin n → MvPolynomial σ K) (hp : LinearIndependent K p) :
    ∃ x : Fin n → (σ → K),
      (Matrix.of fun i j => MvPolynomial.eval (x j) (p i)).det ≠ 0 :=
  AffineJet.exists_eval_matrix_det_ne_zero n p hp

end

end GaloisForLFunctions.HTGeometry
