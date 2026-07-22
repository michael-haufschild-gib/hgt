import GaloisForLFunctions.HTGeometry.DifferentialOperatorMatroid
import GaloisForLFunctions.HTGeometry.FiniteShadowCapacity

/-!
# Exact matroids of differential-constant linear observations

A finite matrix whose actual embedded coefficients are differential constants sends a
differentially independent source family to a represented differential matroid equal to the
ordinary row matroid of the matrix. This upgrades the existing whole-family rank criterion to
every dependent subpacket and its exact rank.

The rooted incidence specialization says that pairwise differences of a free vertex family have
exactly the incidence (graphic) matroid: all nonlinear differential dependence is already visible
in the ordinary constant-coefficient incidence rows.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Matrix Set
open scoped Differential

noncomputable section

universe u

/-- **Differential-constant linear matroid law.** On a differentially independent finite source
family, a finite matrix of differential-constant entries represents exactly its ordinary row
matroid. -/
theorem differentialFamilyMatroid_matrixLinearForms_eq_linearFamilyMatroid
    {C K m n : Type u} [Field C] [Field K] [Algebra C K]
    [Differential C] [Differential K] [DifferentialAlgebra C K] [CharZero K]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n C)
    (hMconst : ∀ i j, (algebraMap C K (M i j))′ = 0)
    (x : n → K) (hx : DifferentialIndependent C x) :
    differentialFamilyMatroid (F := C) (matrixLinearForms M x) =
      linearFamilyMatroid M := by
  apply Matroid.ext_indep
  · simp [differentialFamilyMatroid]
  · intro I _
    letI : Fintype I := Fintype.ofFinite I
    rw [differentialFamilyMatroid_indep_iff,
      linearFamilyMatroid_indep_iff]
    simpa only [] using
      (differentialIndependent_matrixLinearForms_iff_rowIndependent
        (fun i : I ↦ M i) (fun i j ↦ hMconst i j) x hx)

/-- Constant-coefficient incidence rows, with the root coordinate deleted. Deleting the root
column makes the vertex source family free while retaining every edge difference when the root
value is zero. -/
def rootedIncidenceMatrix
    {C V E : Type u} [Field C] [DecidableEq V]
    (root : V) (tail head : E → V) :
    Matrix E ↑({v | v ≠ root} : Set V) C :=
  fun e v ↦
    (if head e = (v : V) then 1 else 0) -
      (if tail e = (v : V) then 1 else 0)

/-- The ordinary rooted incidence matroid of an oriented edge family. -/
def rootedIncidenceMatroid
    {C V E : Type u} [Field C] [Fintype V] [DecidableEq V]
    (root : V) (tail head : E → V) : Matroid E :=
  linearFamilyMatroid (rootedIncidenceMatrix (C := C) root tail head)

@[simp]
theorem rootedIncidenceMatroid_ground
    {C V E : Type u} [Field C] [Fintype V] [DecidableEq V]
    (root : V) (tail head : E → V) :
    (rootedIncidenceMatroid (C := C) root tail head).E = Set.univ := by
  simp [rootedIncidenceMatroid]

/-- Independence in the rooted incidence matroid is exactly linear independence of the incidence
rows. -/
theorem rootedIncidenceMatroid_indep_iff
    {C V E : Type u} [Field C] [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (tail head : E → V) (I : Set E) :
    (rootedIncidenceMatroid (C := C) root tail head).Indep I ↔
      LinearIndependent C
        (fun e : I ↦ rootedIncidenceMatrix (C := C) root tail head e) := by
  exact linearFamilyMatroid_indep_iff _ I

/-- Exact incidence rank of every finite edge packet. -/
theorem rootedIncidenceMatroid_eRk_finset
    {C V E : Type u} [Field C] [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (tail head : E → V) (I : Finset E) :
    (rootedIncidenceMatroid (C := C) root tail head).eRk (↑I : Set E) =
      (Module.finrank C
        (Submodule.span C
          (rootedIncidenceMatrix (C := C) root tail head '' (↑I : Set E))) : ℕ∞) := by
  exact linearFamilyMatroid_eRk_finset _ I

/-- A coefficient family on an oriented edge family is a rooted incidence circulation when its
net incidence coefficient vanishes at every non-root vertex. The missing root equation follows
from the fact that every incidence row has total coefficient zero. -/
def IsRootedIncidenceCirculation
    {C V E J : Type u} [Field C] [Fintype J] [DecidableEq V]
    (root : V) (tail head : E → V) (edge : J → E) (weight : J → C) : Prop :=
  ∀ v : ↑({v | v ≠ root} : Set V),
    ∑ j, weight j * rootedIncidenceMatrix (C := C) root tail head (edge j) v = 0

/-- A rooted incidence circulation is exactly Kirchhoff conservation: total incoming weight
equals total outgoing weight at every non-root vertex. -/
theorem isRootedIncidenceCirculation_iff_nonroot_vertex_conservation
    {C V E J : Type u} [Field C] [Fintype J] [DecidableEq V]
    (root : V) (tail head : E → V) (edge : J → E) (weight : J → C) :
    IsRootedIncidenceCirculation root tail head edge weight ↔
      ∀ v : ↑({v | v ≠ root} : Set V),
        (∑ j, if head (edge j) = (v : V) then weight j else 0) =
          ∑ j, if tail (edge j) = (v : V) then weight j else 0 := by
  constructor
  · intro h v
    simpa [IsRootedIncidenceCirculation, rootedIncidenceMatrix,
      mul_sub, Finset.sum_sub_distrib, sub_eq_zero] using h v
  · intro h v
    simpa [rootedIncidenceMatrix, mul_sub, Finset.sum_sub_distrib,
      sub_eq_zero] using h v

/-- **Root-equation discharge.** The omitted root equation in a rooted incidence circulation is
forced by conservation at all other vertices, because every oriented edge contributes once with
each sign. Thus the rooted linear interface is equivalent to full Kirchhoff conservation. -/
theorem isRootedIncidenceCirculation_iff_vertex_conservation
    {C V E J : Type u} [Field C] [Fintype V] [Fintype J] [DecidableEq V]
    (root : V) (tail head : E → V) (edge : J → E) (weight : J → C) :
    IsRootedIncidenceCirculation root tail head edge weight ↔
      ∀ v : V,
        (∑ j, if head (edge j) = v then weight j else 0) =
          ∑ j, if tail (edge j) = v then weight j else 0 := by
  rw [isRootedIncidenceCirculation_iff_nonroot_vertex_conservation]
  constructor
  · intro h v
    by_cases hv : v = root
    · subst v
      let incoming : V → C := fun w ↦
        ∑ j, if head (edge j) = w then weight j else 0
      let outgoing : V → C := fun w ↦
        ∑ j, if tail (edge j) = w then weight j else 0
      have htotal : ∑ w, (incoming w - outgoing w) = 0 := by
        simp [incoming, outgoing, Finset.sum_sub_distrib, Finset.sum_comm]
      have hsingle : ∑ w, (incoming w - outgoing w) =
          incoming root - outgoing root := by
        apply Fintype.sum_eq_single root
        intro w hw
        exact sub_eq_zero.mpr (h ⟨w, hw⟩)
      rw [hsingle] at htotal
      exact sub_eq_zero.mp htotal
    · exact h ⟨v, hv⟩
  · intro h v
    exact h v

/-- **No-circulation independence law.** A finite edge packet is independent in the rooted
incidence matroid exactly when the zero circulation is its only conserved coefficient flow. This
handles loops, parallel oriented edges, and arbitrary directed multigraph packets uniformly. -/
theorem rootedIncidenceMatroid_indep_iff_no_nonzero_circulation
    {C V E : Type u} [Field C] [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (tail head : E → V) (I : Finset E) :
    (rootedIncidenceMatroid (C := C) root tail head).Indep (↑I : Set E) ↔
      ∀ weight : ↑(↑I : Set E) → C,
        IsRootedIncidenceCirculation root tail head
            (fun e : ↑(↑I : Set E) ↦ (e : E)) weight →
          ∀ e, weight e = 0 := by
  rw [rootedIncidenceMatroid_indep_iff]
  rw [Fintype.linearIndependent_iff]
  simp only [IsRootedIncidenceCirculation, funext_iff, Pi.zero_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Explicit non-root Kirchhoff Prop interface for independence in every finite rooted incidence
packet. -/
theorem rootedIncidenceMatroid_indep_iff_nonroot_vertex_conservation
    {C V E : Type u} [Field C] [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (tail head : E → V) (I : Finset E) :
    (rootedIncidenceMatroid (C := C) root tail head).Indep (↑I : Set E) ↔
      ∀ weight : ↑(↑I : Set E) → C,
        (∀ v : ↑({v | v ≠ root} : Set V),
          (∑ e : ↑(↑I : Set E),
              if head (e : E) = (v : V) then weight e else 0) =
            ∑ e : ↑(↑I : Set E),
              if tail (e : E) = (v : V) then weight e else 0) →
          ∀ e, weight e = 0 := by
  rw [rootedIncidenceMatroid_indep_iff_no_nonzero_circulation]
  simp_rw [isRootedIncidenceCirculation_iff_nonroot_vertex_conservation]

/-- **Full Kirchhoff Prop interface.** A finite rooted incidence packet is independent exactly
when every coefficient flow conserved at every vertex is zero. The root equation is a conclusion,
not an extra hypothesis. -/
theorem rootedIncidenceMatroid_indep_iff_vertex_conservation
    {C V E : Type u} [Field C] [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (root : V) (tail head : E → V) (I : Finset E) :
    (rootedIncidenceMatroid (C := C) root tail head).Indep (↑I : Set E) ↔
      ∀ weight : ↑(↑I : Set E) → C,
        (∀ v : V,
          (∑ e : ↑(↑I : Set E),
              if head (e : E) = v then weight e else 0) =
            ∑ e : ↑(↑I : Set E),
              if tail (e : E) = v then weight e else 0) →
          ∀ e, weight e = 0 := by
  rw [rootedIncidenceMatroid_indep_iff_no_nonzero_circulation]
  simp_rw [isRootedIncidenceCirculation_iff_vertex_conservation]

/-- **Pairwise common-mode decomposition.** An arbitrary family generates exactly the same
differential field as one anchor value together with all ordered pairwise differences. Thus the
pairwise reporter loses at most the single common-translation mode, with no finiteness or
independence hypothesis. -/
theorem differentialAdjoin_range_eq_root_insert_pairwiseDifferences
    {F K V : Type u} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K]
    (root : V) (x : V → K) :
    differentialAdjoin F (Set.range x) =
      differentialAdjoin F
        (insert (x root) (Set.range fun p : V × V ↦ x p.1 - x p.2)) := by
  apply le_antisymm
  · apply differentialAdjoin_le F
    · rintro _ ⟨v, rfl⟩
      have hdiff := subset_differentialAdjoin F
        (insert (x root) (Set.range fun p : V × V ↦ x p.1 - x p.2))
        (Set.mem_insert_of_mem _ (Set.mem_range_self (v, root)))
      have hroot := subset_differentialAdjoin F
        (insert (x root) (Set.range fun p : V × V ↦ x p.1 - x p.2))
        (Set.mem_insert (x root) _)
      have := IntermediateField.add_mem _ hdiff hroot
      simpa using this
    · exact derivationClosed_differentialAdjoin F _
  · apply differentialAdjoin_le F
    · rintro y (rfl | ⟨⟨v, w⟩, rfl⟩)
      · exact subset_differentialAdjoin F (Set.range x) (Set.mem_range_self root)
      · exact IntermediateField.sub_mem _
          (subset_differentialAdjoin F (Set.range x) (Set.mem_range_self v))
          (subset_differentialAdjoin F (Set.range x) (Set.mem_range_self w))
    · exact derivationClosed_differentialAdjoin F _

/-- **Exact common-mode obstruction.** The complete pairwise-difference reporter generates the
full family field if and only if it recovers one anchor value. This identifies the only possible
generated-field loss, rather than imposing a zero-anchor hypothesis. -/
theorem differentialAdjoin_range_pairwiseDifferences_eq_iff_root_mem
    {F K V : Type u} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K]
    (root : V) (x : V → K) :
    differentialAdjoin F (Set.range fun p : V × V ↦ x p.1 - x p.2) =
        differentialAdjoin F (Set.range x) ↔
      x root ∈ differentialAdjoin F
        (Set.range fun p : V × V ↦ x p.1 - x p.2) := by
  constructor
  · intro h
    rw [h]
    exact subset_differentialAdjoin F (Set.range x) (Set.mem_range_self root)
  · intro hroot
    calc
      differentialAdjoin F (Set.range fun p : V × V ↦ x p.1 - x p.2) =
          differentialAdjoin F
            (insert (x root) (Set.range fun p : V × V ↦ x p.1 - x p.2)) := by
        apply le_antisymm
        · apply differentialAdjoin_le F
          · intro y hy
            exact subset_differentialAdjoin F _ (Set.mem_insert_of_mem _ hy)
          · exact derivationClosed_differentialAdjoin F _
        · apply differentialAdjoin_le F
          · intro y hy
            rcases hy with rfl | hy
            · exact hroot
            · exact subset_differentialAdjoin F _ hy
          · exact derivationClosed_differentialAdjoin F _
      _ = differentialAdjoin F (Set.range x) :=
        (differentialAdjoin_range_eq_root_insert_pairwiseDifferences root x).symm

/-- **Zero-anchor pairwise generated-field law.** A zero anchor kills the common-translation
obstruction, so all ordered pairwise differences generate exactly the original family field. -/
theorem differentialAdjoin_range_pairwiseDifferences_eq_of_root_zero
    {F K V : Type u} [Field F] [Field K] [Algebra F K]
    [Differential F] [Differential K] [DifferentialAlgebra F K]
    (root : V) (x : V → K) (hx0 : x root = 0) :
    differentialAdjoin F (Set.range fun p : V × V => x p.1 - x p.2) =
      differentialAdjoin F (Set.range x) := by
  rw [differentialAdjoin_range_pairwiseDifferences_eq_iff_root_mem]
  rw [hx0]
  exact IntermediateField.zero_mem _

/-- Rooted incidence linear forms are the literal endpoint differences whenever the root value is
zero. -/
theorem matrixLinearForms_rootedIncidenceMatrix
    {C K V E : Type u} [Field C] [Field K] [Algebra C K]
    [Fintype V] [DecidableEq V]
    (root : V) (tail head : E → V) (x : V → K) (hx : x root = 0) :
    matrixLinearForms (rootedIncidenceMatrix (C := C) root tail head)
        (fun v : ↑({v | v ≠ root} : Set V) ↦ x v) =
      fun e ↦ x (head e) - x (tail e) := by
  funext e
  have hsum (v0 : V) :
      ∑ v : ↑({v | v ≠ root} : Set V),
        algebraMap C K (if v0 = (v : V) then 1 else 0) * x v = x v0 := by
    by_cases hv0 : v0 = root
    · subst v0
      rw [hx]
      apply Finset.sum_eq_zero
      intro v _
      have hv : root ≠ (v : V) := Ne.symm v.property
      simp [hv]
    · let v' : ↑({v | v ≠ root} : Set V) := ⟨v0, hv0⟩
      calc
        (∑ v : ↑({v | v ≠ root} : Set V),
            algebraMap C K (if v0 = (v : V) then 1 else 0) * x v) =
            algebraMap C K (if v0 = (v' : V) then 1 else 0) * x v' := by
          apply Fintype.sum_eq_single v'
          intro v hv
          have hne : v0 ≠ (v : V) := by
            intro h
            exact hv (Subtype.ext h.symm)
          simp [hne]
        _ = x v0 := by simp [v']
  simp only [matrixLinearForms, rootedIncidenceMatrix, map_sub,
    sub_mul, Finset.sum_sub_distrib]
  rw [hsum, hsum]

/-- Every rooted incidence coefficient is a differential constant, even when unrelated elements
of the coefficient field have nonzero derivative. -/
theorem rootedIncidenceMatrix_coefficients_constant
    {C K V E : Type u} [Field C] [Field K] [Algebra C K]
    [Differential K] [Fintype V] [DecidableEq V]
    (root : V) (tail head : E → V) :
    ∀ e v,
      (algebraMap C K
        (rootedIncidenceMatrix (C := C) root tail head e v))′ = 0 := by
  intro e v
  simp only [rootedIncidenceMatrix]
  split_ifs <;> simp

/-- **Rooted pairwise-difference matroid law.** If all non-root vertex values are differentially
independent and the root value is zero, then the complete nonlinear differential matroid of every
finite oriented edge family is exactly its rooted incidence matroid. -/
theorem differentialFamilyMatroid_pairwiseDifferences_eq_rootedIncidenceMatroid
    {C K V E : Type u} [Field C] [Field K] [Algebra C K]
    [Differential C] [Differential K] [DifferentialAlgebra C K] [CharZero K]
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (root : V) (tail head : E → V) (x : V → K) (hx0 : x root = 0)
    (hx : DifferentialIndependent C
      (fun v : ↑({v | v ≠ root} : Set V) ↦ x v)) :
    differentialFamilyMatroid (F := C)
        (fun e ↦ x (head e) - x (tail e)) =
      rootedIncidenceMatroid (C := C) root tail head := by
  rw [← matrixLinearForms_rootedIncidenceMatrix
    (C := C) root tail head x hx0]
  exact differentialFamilyMatroid_matrixLinearForms_eq_linearFamilyMatroid
    (rootedIncidenceMatrix (C := C) root tail head)
    (rootedIncidenceMatrix_coefficients_constant root tail head)
    (fun v : ↑({v | v ≠ root} : Set V) ↦ x v) hx

end

end GaloisForLFunctions.HTGeometry
