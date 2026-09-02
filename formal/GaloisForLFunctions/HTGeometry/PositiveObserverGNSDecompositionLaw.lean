import GaloisForLFunctions.HTGeometry.KSGNSWeightedProjection
import GaloisForLFunctions.HTGeometry.MomentFiberPickSchurPhase
import GaloisForLFunctions.HTGeometry.PositiveObserverCovarianceLaw

/-!
# Completed GNS splitting for a conditional expectation

This file supplies the completed Hilbert-space half of the positive-observer theorem.  A
conditional expectation that descends to a bounded self-adjoint idempotent on its GNS completion
splits that completion into its closed observed range and closed hidden kernel.  The algebraic
observed and centered cores are dense in the respective summands, every GNS vector has a unique
orthogonal decomposition, and the centered component is exactly the GNS image of `a - E(a)`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Bounded self-adjoint idempotent obtained by extending a conditional expectation to a completed
GNS Hilbert space. -/
structure CompletedConditionalProjection (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  projector : H →L[ℂ] H
  idempotent : ∀ x, projector (projector x) = projector x
  selfAdjoint : ∀ x y, ⟪projector x, y⟫_ℂ = ⟪x, projector y⟫_ℂ

namespace CompletedConditionalProjection

variable (P : CompletedConditionalProjection H)

/-- Completed observed summand. -/
def observerSubspace : Submodule ℂ H :=
  LinearMap.range P.projector.toLinearMap

/-- Completed hidden summand. -/
def hiddenSubspace : Submodule ℂ H :=
  LinearMap.ker P.projector.toLinearMap

/-- Complementary hidden projection `I - P`. -/
def complement : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - P.projector

theorem observerSubspace_eq_ker_complement :
    P.observerSubspace = LinearMap.ker P.complement.toLinearMap := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change P.projector y - P.projector (P.projector y) = 0
    rw [P.idempotent, sub_self]
  · intro hx
    change x - P.projector x = 0 at hx
    exact ⟨x, (sub_eq_zero.mp hx).symm⟩

/-- Observed summand is closed. -/
theorem observerSubspace_isClosed : IsClosed (P.observerSubspace : Set H) := by
  rw [P.observerSubspace_eq_ker_complement]
  exact P.complement.isClosed_ker

/-- Hidden summand is closed. -/
theorem hiddenSubspace_isClosed : IsClosed (P.hiddenSubspace : Set H) :=
  P.projector.isClosed_ker

theorem projector_fixes_observer {x : H} (hx : x ∈ P.observerSubspace) :
    P.projector x = x := by
  rcases hx with ⟨y, rfl⟩
  exact P.idempotent y

/-- Every observed vector is orthogonal to every hidden vector. -/
theorem observer_orthogonal_hidden {x y : H}
    (hx : x ∈ P.observerSubspace) (hy : y ∈ P.hiddenSubspace) :
    ⟪x, y⟫_ℂ = 0 := by
  rw [← P.projector_fixes_observer hx, P.selfAdjoint]
  rw [show P.projector y = 0 from hy]
  simp

/-- Canonical orthogonal decomposition of every completed GNS vector. -/
theorem decomposition (x : H) :
    x = P.projector x + (x - P.projector x) ∧
      P.projector x ∈ P.observerSubspace ∧
      x - P.projector x ∈ P.hiddenSubspace ∧
      ⟪P.projector x, x - P.projector x⟫_ℂ = 0 := by
  have hh : x - P.projector x ∈ P.hiddenSubspace := by
    change P.projector (x - P.projector x) = 0
    rw [map_sub, P.idempotent, sub_self]
  exact ⟨by abel, ⟨x, rfl⟩, hh, P.observer_orthogonal_hidden ⟨x, rfl⟩ hh⟩

/-- The observed-plus-hidden expression is unique, so the two closed summands form an internal
orthogonal direct sum. -/
theorem existsUnique_observer_add_hidden (x : H) :
    ∃! p : P.observerSubspace × P.hiddenSubspace,
      x = (p.1 : H) + (p.2 : H) := by
  let p : P.observerSubspace × P.hiddenSubspace :=
    (⟨P.projector x, ⟨x, rfl⟩⟩,
      ⟨x - P.projector x, by
        change P.projector (x - P.projector x) = 0
        rw [map_sub, P.idempotent, sub_self]⟩)
  refine ⟨p, (P.decomposition x).1, ?_⟩
  intro q hq
  apply Prod.ext
  · apply Subtype.ext
    have hp := congrArg P.projector hq
    change P.projector x = P.projector ((q.1 : H) + (q.2 : H)) at hp
    rw [map_add, P.projector_fixes_observer q.1.property,
      show P.projector (q.2 : H) = 0 from q.2.property, add_zero] at hp
    exact hp.symm
  · apply Subtype.ext
    have hfirst : (q.1 : H) = P.projector x := by
      have hp := congrArg P.projector hq
      change P.projector x = P.projector ((q.1 : H) + (q.2 : H)) at hp
      rw [map_add, P.projector_fixes_observer q.1.property,
        show P.projector (q.2 : H) = 0 from q.2.property, add_zero] at hp
      exact hp.symm
    have hsum := hq
    rw [hfirst] at hsum
    exact add_left_cancel (hsum.symm.trans (P.decomposition x).1)

end CompletedConditionalProjection

variable {A : Type*} [CStarAlgebra A]

/-- Dense GNS core, its descended conditional expectation, and exact intertwining with the
completed orthogonal projection. -/
structure ConditionalExpectationGNSCompletion
    (E : ConditionalExpectationCore (A := A)) where
  projection : CompletedConditionalProjection H
  gns : A →ₗ[ℂ] H
  gns_dense : DenseRange gns
  projector_gns : ∀ a, projection.projector (gns a) = gns (E.map a)

namespace ConditionalExpectationGNSCompletion

variable {E : ConditionalExpectationCore (A := A)}
variable (G : ConditionalExpectationGNSCompletion E (H := H))

/-- Algebraic observed GNS core. -/
def observerCoreMap : A →ₗ[ℂ] H :=
  G.projection.projector.toLinearMap.comp G.gns

/-- Algebraic centered GNS core. -/
def hiddenCoreMap : A →ₗ[ℂ] H :=
  G.projection.complement.toLinearMap.comp G.gns

theorem hiddenCoreMap_apply (a : A) :
    G.hiddenCoreMap a = G.gns (E.hiddenComponent a) := by
  simp [hiddenCoreMap, CompletedConditionalProjection.complement,
    ConditionalExpectationCore.hiddenComponent, G.projector_gns]

/-- Centered algebraic vectors are dense in the entire closed hidden summand. -/
theorem topologicalClosure_hiddenCore_eq_hiddenSubspace :
    (LinearMap.range G.hiddenCoreMap).topologicalClosure =
      G.projection.hiddenSubspace := by
  exact topologicalClosure_range_projectionComplement_comp_eq_ker
    G.projection.projector G.projection.idempotent G.gns G.gns_dense

/-- Observed algebraic vectors are dense in the entire closed observed summand. -/
theorem topologicalClosure_observerCore_eq_observerSubspace :
    (LinearMap.range G.observerCoreMap).topologicalClosure =
      G.projection.observerSubspace := by
  let Q := G.projection.complement
  have hQ : ∀ x, Q (Q x) = Q x := by
    intro x
    change (x - G.projection.projector x) -
        G.projection.projector (x - G.projection.projector x) =
      x - G.projection.projector x
    rw [map_sub, G.projection.idempotent, sub_self, sub_zero]
  have h := topologicalClosure_range_projectionComplement_comp_eq_ker
    Q hQ G.gns G.gns_dense
  rw [show continuousProjectionComplement Q = G.projection.projector by
    ext x
    simp [Q, continuousProjectionComplement,
      CompletedConditionalProjection.complement]] at h
  rw [show LinearMap.ker Q.toLinearMap = G.projection.observerSubspace by
    exact G.projection.observerSubspace_eq_ker_complement.symm] at h
  exact h

/-- Literal GNS decomposition `a = E(a) + (a-E(a))`, with closed-summand membership and
orthogonality after completion. -/
theorem gns_orthogonal_decomposition (a : A) :
    G.gns a = G.gns (E.map a) + G.gns (E.hiddenComponent a) ∧
      G.gns (E.map a) ∈ G.projection.observerSubspace ∧
      G.gns (E.hiddenComponent a) ∈ G.projection.hiddenSubspace ∧
      ⟪G.gns (E.map a), G.gns (E.hiddenComponent a)⟫_ℂ = 0 := by
  have h := G.projection.decomposition (G.gns a)
  simpa [G.projector_gns, ← G.hiddenCoreMap_apply a,
    hiddenCoreMap, CompletedConditionalProjection.complement] using h

end ConditionalExpectationGNSCompletion

end

end GaloisForLFunctions.HTGeometry
