import GaloisForLFunctions.HTGeometry.DifferentialConstantLinearFamilyMatroid

/-!
# Incidence matroids after pointed label collisions

When vertex values depend only on a label, repeated labels must first be collapsed before an
incidence law is exact. The distinguished loop label supplies the deleted zero column. This file
constructs that quotient incidence matroid and proves that pairwise differences of independent
nonloop label values represent it exactly.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Matrix Set
open scoped Differential

noncomputable section

universe u

/-- The finite set of occupied nonloop labels of a finite vertex family. -/
def pointedCollisionIncidenceSupport
    {V Frame : Type u} [Fintype V] [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) : Finset Frame :=
  (Finset.univ.image frame).erase loopFrame

/-- Incidence matrix after vertices with equal labels have been collapsed and the loop-label
column has been deleted. -/
def pointedCollisionIncidenceMatrix
    {C V E Frame : Type u} [Field C] [Fintype V] [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) :
    Matrix E (pointedCollisionIncidenceSupport frame loopFrame) C :=
  fun e q ↦
    (if frame (head e) = (q : Frame) then 1 else 0) -
      (if frame (tail e) = (q : Frame) then 1 else 0)

/-- The ordinary incidence matroid of the finite occupied-label quotient. -/
def pointedCollisionIncidenceMatroid
    {C V E Frame : Type u} [Field C] [Fintype V] [Fintype E]
    [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) : Matroid E :=
  linearFamilyMatroid
    (pointedCollisionIncidenceMatrix (C := C) frame loopFrame tail head)

@[simp]
theorem pointedCollisionIncidenceMatroid_ground
    {C V E Frame : Type u} [Field C] [Fintype V] [Fintype E]
    [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) :
    (pointedCollisionIncidenceMatroid
      (C := C) frame loopFrame tail head).E = Set.univ := by
  simp [pointedCollisionIncidenceMatroid]

/-- Independence in the collision-quotient incidence matroid is ordinary row independence. -/
theorem pointedCollisionIncidenceMatroid_indep_iff
    {C V E Frame : Type u} [Field C] [Fintype V] [Fintype E]
    [DecidableEq Frame] [DecidableEq E]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) (I : Set E) :
    (pointedCollisionIncidenceMatroid
        (C := C) frame loopFrame tail head).Indep I ↔
      LinearIndependent C
        (fun e : I ↦ pointedCollisionIncidenceMatrix
          (C := C) frame loopFrame tail head e) := by
  exact linearFamilyMatroid_indep_iff _ I

/-- Exact finite-packet rank in the collision-quotient incidence matroid. -/
theorem pointedCollisionIncidenceMatroid_eRk_finset
    {C V E Frame : Type u} [Field C] [Fintype V] [Fintype E]
    [DecidableEq Frame] [DecidableEq E]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) (I : Finset E) :
    (pointedCollisionIncidenceMatroid
        (C := C) frame loopFrame tail head).eRk (↑I : Set E) =
      (Module.finrank C
        (Submodule.span C
          (pointedCollisionIncidenceMatrix
            (C := C) frame loopFrame tail head '' (↑I : Set E))) : ℕ∞) := by
  exact linearFamilyMatroid_eRk_finset _ I

/-- Collision-quotient incidence linear forms are the literal endpoint-label differences. -/
theorem matrixLinearForms_pointedCollisionIncidenceMatrix
    {C K V E Frame : Type u} [Field C] [Field K] [Algebra C K]
    [Fintype V] [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V)
    (x : Frame → K) (hx : x loopFrame = 0) :
    matrixLinearForms
        (pointedCollisionIncidenceMatrix (C := C) frame loopFrame tail head)
        (fun q : pointedCollisionIncidenceSupport frame loopFrame ↦ x q) =
      fun e ↦ x (frame (head e)) - x (frame (tail e)) := by
  funext e
  have hsum (v0 : V) :
      ∑ q : pointedCollisionIncidenceSupport frame loopFrame,
        algebraMap C K (if frame v0 = (q : Frame) then 1 else 0) * x q =
          x (frame v0) := by
    by_cases hv0 : frame v0 = loopFrame
    · rw [hv0, hx]
      apply Finset.sum_eq_zero
      intro q _
      have hq : (q : Frame) ≠ loopFrame :=
        (Finset.mem_erase.mp q.property).1
      simp [hq.symm]
    · let q' : pointedCollisionIncidenceSupport frame loopFrame :=
        ⟨frame v0, by simp [pointedCollisionIncidenceSupport, hv0]⟩
      calc
        (∑ q : pointedCollisionIncidenceSupport frame loopFrame,
            algebraMap C K (if frame v0 = (q : Frame) then 1 else 0) * x q) =
            algebraMap C K (if frame v0 = (q' : Frame) then 1 else 0) * x q' := by
          apply Fintype.sum_eq_single q'
          intro q hq
          have hne : frame v0 ≠ (q : Frame) := by
            intro h
            exact hq (Subtype.ext h.symm)
          simp [hne]
        _ = x (frame v0) := by simp [q']
  simp only [matrixLinearForms, pointedCollisionIncidenceMatrix, map_sub,
    sub_mul, Finset.sum_sub_distrib]
  rw [hsum, hsum]

/-- Every collision-quotient incidence coefficient is a differential constant. -/
theorem pointedCollisionIncidenceMatrix_coefficients_constant
    {C K V E Frame : Type u} [Field C] [Field K] [Algebra C K]
    [Differential K] [Fintype V] [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) :
    ∀ e q,
      (algebraMap C K
        (pointedCollisionIncidenceMatrix
          (C := C) frame loopFrame tail head e q))′ = 0 := by
  intro e q
  simp only [pointedCollisionIncidenceMatrix]
  split_ifs <;> simp

/-- **Pointed-collision incidence law.** Pairwise differences of a labelled family whose occupied
nonloop label values are differentially independent represent exactly the incidence matroid of
the occupied-label quotient. Repeated labels and vertices carrying the loop label require no
extra hypotheses. -/
theorem differentialFamilyMatroid_gradedPairwiseDifferences_eq_pointedCollisionIncidenceMatroid
    {C K V E Frame : Type u} [Field C] [Field K] [Algebra C K]
    [Differential C] [Differential K] [DifferentialAlgebra C K] [CharZero K]
    [Fintype V] [Fintype E] [DecidableEq Frame] [DecidableEq E]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V)
    (x : Frame → K) (hx0 : x loopFrame = 0)
    (hx : DifferentialIndependent C
      (fun q : pointedCollisionIncidenceSupport frame loopFrame ↦ x q)) :
    differentialFamilyMatroid (F := C)
        (fun e ↦ x (frame (head e)) - x (frame (tail e))) =
      pointedCollisionIncidenceMatroid
        (C := C) frame loopFrame tail head := by
  rw [← matrixLinearForms_pointedCollisionIncidenceMatrix
    (C := C) frame loopFrame tail head x hx0]
  exact differentialFamilyMatroid_matrixLinearForms_eq_linearFamilyMatroid
    (pointedCollisionIncidenceMatrix (C := C) frame loopFrame tail head)
    (pointedCollisionIncidenceMatrix_coefficients_constant
      frame loopFrame tail head)
    (fun q : pointedCollisionIncidenceSupport frame loopFrame ↦ x q) hx

end

end GaloisForLFunctions.HTGeometry
