import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.HTGeometry.ABHN.FinsuppReciprocitySupportCardinality
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.PolarizedIncidenceStokes

/-!
# Hasse exactness for connected oriented incidence

On a finite connected multigraph, edge flows, vertex charges, and total charge form an exact
local--global sequence.  Total charge is the complete obstruction to realizing a vertex profile as
an oriented boundary, and local profiles modulo global edge flows form one copy of `ℂ`.
-/

namespace HTGeometry.ConstraintRelativity

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.ABHN

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (s t : E → V)

/-- Total vertex charge is onto whenever the vertex set is nonempty. -/
theorem piAugmentation_surjective [Nonempty V] :
    Function.Surjective (piAugmentation (V := V)) := by
  intro z
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  refine ⟨Pi.single v₀ z, ?_⟩
  rw [augmentation_apply]
  simp

/-- Edge boundaries and total charge form an exact pair on a connected multigraph. -/
theorem orientedBoundary_piAugmentation_exact [Nonempty V]
    (hconn : ∀ u v : V, Relation.ReflTransGen (edgeRel s t) u v) :
    Function.Exact (orientedBoundary s t) (piAugmentation (V := V)) :=
  LinearMap.exact_iff.mpr (range_orientedBoundary_eq_ker_augmentation s t hconn).symm

/-- **Connected incidence Hasse quotient.**  Vertex charges modulo globally induced edge
boundaries are classified by their total charge. -/
noncomputable def orientedIncidenceHasseQuotientEquiv [Nonempty V]
    (hconn : ∀ u v : V, Relation.ReflTransGen (edgeRel s t) u v) :
    ((V → ℂ) ⧸ LinearMap.range (orientedBoundary s t)) ≃ₗ[ℂ] ℂ :=
  linearHasseQuotientEquiv (orientedBoundary s t) (piAugmentation (V := V))
    (orientedBoundary_piAugmentation_exact s t hconn) piAugmentation_surjective

@[simp]
theorem orientedIncidenceHasseQuotientEquiv_mk [Nonempty V]
    (hconn : ∀ u v : V, Relation.ReflTransGen (edgeRel s t) u v) (w : V → ℂ) :
    orientedIncidenceHasseQuotientEquiv s t hconn (Submodule.Quotient.mk w) =
      piAugmentation w :=
  linearHasseQuotientEquiv_mk (orientedBoundary s t) (piAugmentation (V := V))
    (orientedBoundary_piAugmentation_exact s t hconn) piAugmentation_surjective w

/-- A connected vertex-charge profile is a global edge boundary exactly when its total charge
vanishes. -/
theorem exists_orientedBoundary_eq_iff_sum_eq_zero [Nonempty V]
    (hconn : ∀ u v : V, Relation.ReflTransGen (edgeRel s t) u v) (w : V → ℂ) :
    (∃ q, orientedBoundary s t q = w) ↔ ∑ v, w v = 0 := by
  rw [← augmentation_apply]
  change w ∈ LinearMap.range (orientedBoundary s t) ↔
    w ∈ LinearMap.ker (piAugmentation (V := V))
  rw [range_orientedBoundary_eq_ker_augmentation s t hconn]

/-- Two vertex profiles differ by a global edge flow exactly when they have equal total charge. -/
theorem orientedIncidence_congr_hasse_iff [Nonempty V]
    (hconn : ∀ u v : V, Relation.ReflTransGen (edgeRel s t) u v) (w₁ w₂ : V → ℂ) :
    w₁ - w₂ ∈ LinearMap.range (orientedBoundary s t) ↔
      piAugmentation w₁ = piAugmentation w₂ :=
  linearHasse_congr_iff (orientedBoundary s t) (piAugmentation (V := V))
    (orientedBoundary_piAugmentation_exact s t hconn) w₁ w₂

/-- A finite vertex profile associated to an oriented boundary. -/
noncomputable def orientedBoundaryChargeProfile (q : E → ℂ) : V →₀ ℂ :=
  Finsupp.equivFunOnFinite.symm (orientedBoundary s t q)

omit [DecidableEq E] in
@[simp]
theorem orientedBoundaryChargeProfile_apply (q : E → ℂ) (v : V) :
    orientedBoundaryChargeProfile s t q v = orientedBoundary s t q v := rfl

omit [DecidableEq E] in
/-- Oriented boundary charge obeys the finite reciprocity sum. -/
theorem orientedBoundaryChargeProfile_sum_eq_zero (q : E → ℂ) :
    (orientedBoundaryChargeProfile s t q).sum (fun _ z => z) = 0 := by
  rw [Finsupp.sum_fintype _ _ (by intro; rfl)]
  exact sum_orientedBoundary s t q

omit [DecidableEq E] in
/-- Every nonzero boundary charge has a distinct nonzero companion vertex. -/
theorem orientedBoundaryChargeProfile_exists_other_nonzero_vertex
    (q : E → ℂ) {v : V} (hv : orientedBoundary s t q v ≠ 0) :
    ∃ w : V, w ≠ v ∧ orientedBoundary s t q w ≠ 0 := by
  apply finsupp_exists_other_nonzero_place_of_sum_eq_zero
    (orientedBoundaryChargeProfile s t q)
    (orientedBoundaryChargeProfile_sum_eq_zero s t q)
  simpa using hv

omit [DecidableEq E] in
/-- A nonzero oriented boundary charges at least two vertices. -/
theorem orientedBoundaryChargeProfile_two_le_support_card
    (q : E → ℂ) (hne : orientedBoundaryChargeProfile s t q ≠ 0) :
    2 ≤ (orientedBoundaryChargeProfile s t q).support.card :=
  finsupp_two_le_support_card_of_sum_eq_zero (orientedBoundaryChargeProfile s t q)
    (orientedBoundaryChargeProfile_sum_eq_zero s t q) hne

end HTGeometry.ConstraintRelativity
