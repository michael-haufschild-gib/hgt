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

/-- Vertices of the occupied-label quotient: one vertex for each occupied nonloop label and a
distinguished collapsed vertex for the loop label. -/
abbrev pointedCollisionIncidenceVertex
    {V Frame : Type u} [Fintype V] [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) : Type u :=
  Option (pointedCollisionIncidenceSupport frame loopFrame)

/-- Map an original vertex to its occupied-label quotient vertex. -/
def pointedCollisionIncidenceVertexOf
    {V Frame : Type u} [Fintype V] [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (v : V) :
    pointedCollisionIncidenceVertex frame loopFrame :=
  if h : frame v = loopFrame then none
  else some ⟨frame v, by simp [pointedCollisionIncidenceSupport, h]⟩

@[simp]
theorem pointedCollisionIncidenceVertexOf_eq_none_iff
    {V Frame : Type u} [Fintype V] [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (v : V) :
    pointedCollisionIncidenceVertexOf frame loopFrame v = none ↔
      frame v = loopFrame := by
  simp [pointedCollisionIncidenceVertexOf]

@[simp]
theorem pointedCollisionIncidenceVertexOf_eq_some_iff
    {V Frame : Type u} [Fintype V] [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (v : V)
    (q : pointedCollisionIncidenceSupport frame loopFrame) :
    pointedCollisionIncidenceVertexOf frame loopFrame v = some q ↔
      frame v = (q : Frame) := by
  simp only [pointedCollisionIncidenceVertexOf]
  split_ifs with h
  · have hq : (q : Frame) ≠ loopFrame := (Finset.mem_erase.mp q.property).1
    constructor
    · intro hs
      cases hs
    · intro hv
      exact (hq (hv.symm.trans h)).elim
  · constructor
    · intro hs
      exact congrArg Subtype.val (Option.some.inj hs)
    · intro hv
      apply congrArg some
      exact Subtype.ext hv

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

/-- A coefficient family is a collision-quotient circulation when its incidence coefficient
vanishes at every occupied nonloop label. -/
def IsPointedCollisionIncidenceCirculation
    {C V E J Frame : Type u} [Field C] [Fintype V] [Fintype J]
    [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V)
    (edge : J → E) (weight : J → C) : Prop :=
  ∀ q : pointedCollisionIncidenceSupport frame loopFrame,
    ∑ j, weight j * pointedCollisionIncidenceMatrix
      (C := C) frame loopFrame tail head (edge j) q = 0

/-- The circulation equations are Kirchhoff conservation at every occupied nonloop label. -/
theorem isPointedCollisionIncidenceCirculation_iff_nonloop_conservation
    {C V E J Frame : Type u} [Field C] [Fintype V] [Fintype J]
    [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V)
    (edge : J → E) (weight : J → C) :
    IsPointedCollisionIncidenceCirculation frame loopFrame tail head edge weight ↔
      ∀ q : pointedCollisionIncidenceSupport frame loopFrame,
        (∑ j, if frame (head (edge j)) = (q : Frame) then weight j else 0) =
          ∑ j, if frame (tail (edge j)) = (q : Frame) then weight j else 0 := by
  constructor
  · intro h q
    simpa [IsPointedCollisionIncidenceCirculation,
      pointedCollisionIncidenceMatrix, mul_sub, Finset.sum_sub_distrib,
      sub_eq_zero] using h q
  · intro h q
    simpa [pointedCollisionIncidenceMatrix, mul_sub, Finset.sum_sub_distrib,
      sub_eq_zero] using h q

/-- **Collapsed-loop equation discharge.** Conservation at occupied nonloop labels forces the
equation at the collapsed loop-label vertex, since total incidence is zero. Hence a circulation
is equivalent to full Kirchhoff conservation on the occupied-label quotient. -/
theorem isPointedCollisionIncidenceCirculation_iff_vertex_conservation
    {C V E J Frame : Type u} [Field C] [Fintype V] [Fintype J]
    [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V)
    (edge : J → E) (weight : J → C) :
    IsPointedCollisionIncidenceCirculation frame loopFrame tail head edge weight ↔
      ∀ q : pointedCollisionIncidenceVertex frame loopFrame,
        (∑ j, if pointedCollisionIncidenceVertexOf frame loopFrame
              (head (edge j)) = q then weight j else 0) =
          ∑ j, if pointedCollisionIncidenceVertexOf frame loopFrame
              (tail (edge j)) = q then weight j else 0 := by
  rw [isPointedCollisionIncidenceCirculation_iff_nonloop_conservation]
  constructor
  · intro h q
    cases q with
    | none =>
        let incoming : pointedCollisionIncidenceVertex frame loopFrame → C := fun w ↦
          ∑ j, if pointedCollisionIncidenceVertexOf frame loopFrame
            (head (edge j)) = w then weight j else 0
        let outgoing : pointedCollisionIncidenceVertex frame loopFrame → C := fun w ↦
          ∑ j, if pointedCollisionIncidenceVertexOf frame loopFrame
            (tail (edge j)) = w then weight j else 0
        have htotal : ∑ w, (incoming w - outgoing w) = 0 := by
          simp [incoming, outgoing, Finset.sum_sub_distrib, Finset.sum_comm]
        have hsingle : ∑ w, (incoming w - outgoing w) =
            incoming none - outgoing none := by
          apply Fintype.sum_eq_single none
          intro w hw
          cases w with
          | none => exact (hw rfl).elim
          | some q =>
              apply sub_eq_zero.mpr
              simpa [incoming, outgoing] using h q
        rw [hsingle] at htotal
        exact sub_eq_zero.mp htotal
    | some q =>
        simpa using h q
  · intro h q
    simpa using h (some q)

/-- A finite collision-quotient incidence packet is independent exactly when it has no nonzero
coefficient circulation. -/
theorem pointedCollisionIncidenceMatroid_indep_iff_no_nonzero_circulation
    {C V E Frame : Type u} [Field C] [Fintype V] [Fintype E]
    [DecidableEq Frame] [DecidableEq E]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) (I : Finset E) :
    (pointedCollisionIncidenceMatroid
        (C := C) frame loopFrame tail head).Indep (↑I : Set E) ↔
      ∀ weight : ↑(↑I : Set E) → C,
        IsPointedCollisionIncidenceCirculation frame loopFrame tail head
            (fun e : ↑(↑I : Set E) ↦ (e : E)) weight →
          ∀ e, weight e = 0 := by
  rw [pointedCollisionIncidenceMatroid_indep_iff]
  rw [Fintype.linearIndependent_iff]
  simp only [IsPointedCollisionIncidenceCirculation, funext_iff, Pi.zero_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- **Full quotient Kirchhoff Prop interface.** Independence is equivalent to triviality of every
coefficient flow conserved at every occupied-label quotient vertex. -/
theorem pointedCollisionIncidenceMatroid_indep_iff_vertex_conservation
    {C V E Frame : Type u} [Field C] [Fintype V] [Fintype E]
    [DecidableEq Frame] [DecidableEq E]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) (I : Finset E) :
    (pointedCollisionIncidenceMatroid
        (C := C) frame loopFrame tail head).Indep (↑I : Set E) ↔
      ∀ weight : ↑(↑I : Set E) → C,
        (∀ q : pointedCollisionIncidenceVertex frame loopFrame,
          (∑ e : ↑(↑I : Set E),
              if pointedCollisionIncidenceVertexOf frame loopFrame
                (head (e : E)) = q then weight e else 0) =
            ∑ e : ↑(↑I : Set E),
              if pointedCollisionIncidenceVertexOf frame loopFrame
                (tail (e : E)) = q then weight e else 0) →
          ∀ e, weight e = 0 := by
  rw [pointedCollisionIncidenceMatroid_indep_iff_no_nonzero_circulation]
  simp_rw [isPointedCollisionIncidenceCirculation_iff_vertex_conservation]

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
