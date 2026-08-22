import GaloisForLFunctions.HTGeometry.HaferkampFlattenedCoordinateDerivative
import GaloisForLFunctions.HTGeometry.HaferkampTwoQubitPauliTransport

/-!
# Pauli coordinates for the two-qubit special-unitary group

This module reindexes the existing finite-qubit Pauli basis from function
configurations to the Boolean-pair convention used by local `SU(4)` gates.
It thereby supplies a certified complex-linearly independent family of all
fifteen nonidentity two-qubit Pauli directions, ready for the local Haar-chart
bridge in the Haferkamp--Faist--Kothakonda--Eisert--Yunger Halpern proof.
-/

open Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Boolean-pair computational basis is equivalent to the two-coordinate
Boolean-function basis used by `finitePauliMatrix`. -/
def boolPairConfigurationEquiv : (Bool × Bool) ≃ (Bool → Bool) where
  toFun x b := if b then x.2 else x.1
  invFun f := (f false, f true)
  left_inv := by
    rintro ⟨x, y⟩
    simp
  right_inv := by
    intro f
    funext b
    fin_cases b <;> simp

/-- The finite-qubit Pauli label associated to a pair of local Boolean labels. -/
def boolTwoQubitPauliLabel (p q : Option (Fin 3)) : Bool → Option (Fin 3) :=
  fun b => if b then q else p

/-- Literal tensor-product and finite-register presentations of a two-qubit
Pauli matrix agree under the basis reindexing. -/
theorem boolTwoQubitPauli_eq_reindex_finitePauliMatrix
    (p q : Option (Fin 3)) :
    boolTwoQubitPauli p q =
      Matrix.reindex boolPairConfigurationEquiv.symm boolPairConfigurationEquiv.symm
        (finitePauliMatrix (boolTwoQubitPauliLabel p q)) := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp [boolTwoQubitPauli, Matrix.kronecker, finitePauliMatrix,
    boolPairConfigurationEquiv, boolTwoQubitPauliLabel, boolPauliOptionEntry]
  exact mul_comm _ _

/-- The two-coordinate label encoding is injective. -/
theorem boolTwoQubitPauliLabel_injective :
    Function.Injective (fun pq : Option (Fin 3) × Option (Fin 3) =>
      boolTwoQubitPauliLabel pq.1 pq.2) := by
  intro x y hxy
  apply Prod.ext
  · have h := congrFun hxy false
    simpa [boolTwoQubitPauliLabel] using h
  · have h := congrFun hxy true
    simpa [boolTwoQubitPauliLabel] using h

/-- All sixteen literal Boolean-pair Pauli matrices are complex-linearly
independent. -/
theorem linearIndependent_boolTwoQubitPauli :
    LinearIndependent ℂ (fun pq : Option (Fin 3) × Option (Fin 3) =>
      boolTwoQubitPauli pq.1 pq.2) := by
  let reindexMap :
      Matrix (Bool → Bool) (Bool → Bool) ℂ →ₗ[ℂ]
        Matrix (Bool × Bool) (Bool × Bool) ℂ :=
    (Matrix.reindexLinearEquiv ℂ ℂ
      boolPairConfigurationEquiv.symm boolPairConfigurationEquiv.symm).toLinearMap
  have hbase := (finitePauliMatrix_linearIndependent (σ := Bool)).comp
    (fun pq : Option (Fin 3) × Option (Fin 3) => boolTwoQubitPauliLabel pq.1 pq.2)
    boolTwoQubitPauliLabel_injective
  have hinj : reindexMap.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr
      (Matrix.reindexLinearEquiv ℂ ℂ
        boolPairConfigurationEquiv.symm boolPairConfigurationEquiv.symm).injective
  have hmap := hbase.map' reindexMap hinj
  have hfamily :
      (fun pq : Option (Fin 3) × Option (Fin 3) =>
        reindexMap (finitePauliMatrix (boolTwoQubitPauliLabel pq.1 pq.2))) =
      (fun pq : Option (Fin 3) × Option (Fin 3) => boolTwoQubitPauli pq.1 pq.2) := by
    funext pq
    exact (boolTwoQubitPauli_eq_reindex_finitePauliMatrix pq.1 pq.2).symm
  rw [← hfamily]
  change LinearIndependent ℂ
    (reindexMap ∘ finitePauliMatrix ∘
      fun pq : Option (Fin 3) × Option (Fin 3) => boolTwoQubitPauliLabel pq.1 pq.2)
  exact hmap

/-- The fifteen nonidentity Boolean-pair Pauli matrices are
complex-linearly independent. -/
theorem linearIndependent_boolNonidentityTwoQubitPauli :
    LinearIndependent ℂ (fun pq : boolNonidentityTwoQubitPauliLabel =>
      boolTwoQubitPauli pq.1.1 pq.1.2) := by
  have h := linearIndependent_boolTwoQubitPauli.comp
    (fun pq : boolNonidentityTwoQubitPauliLabel => pq.1)
    (fun x y hxy => Subtype.ext hxy)
  change LinearIndependent ℂ
    ((fun pq : Option (Fin 3) × Option (Fin 3) => boolTwoQubitPauli pq.1 pq.2) ∘
      fun pq : boolNonidentityTwoQubitPauliLabel => pq.1)
  exact h

/-- The adjoint of a finite special unitary is again finite special unitary. -/
def specialUnitaryAdjoint
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
  ⟨Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ), by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
      have hU : (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
          Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 1 := by
        rw [← Matrix.star_eq_conjTranspose]
        exact Matrix.mem_unitaryGroup_iff.mp
          (Matrix.mem_specialUnitaryGroup_iff.mp U.2).1
      exact mul_eq_one_comm.mp hU
    · rw [Matrix.det_conjTranspose,
        (Matrix.mem_specialUnitaryGroup_iff.mp U.2).2, star_one]⟩

/-- An adjoint followed by its special unitary cancels exactly. -/
@[simp] theorem specialUnitaryAdjoint_mul
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    specialUnitaryAdjoint U * U = 1 := by
  apply Subtype.ext
  change Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
      (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 1
  have hU : (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
      Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp
      (Matrix.mem_specialUnitaryGroup_iff.mp U.2).1
  exact mul_eq_one_comm.mp hU

/-- Chosen determinant-one Clifford transporting a nonidentity local Pauli
to the terminal `I ⊗ Z` direction. -/
noncomputable def boolNonidentityTwoQubitPauliTransport
    (pq : boolNonidentityTwoQubitPauliLabel) :
    Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
  Classical.choose (boolNonidentityTwoQubitPauli_exists_specialUnitaryTransport pq)

/-- Nonzero scalar of the chosen local Pauli transport. -/
noncomputable def boolNonidentityTwoQubitPauliTransportScalar
    (pq : boolNonidentityTwoQubitPauliLabel) : ℂ :=
  Classical.choose (Classical.choose_spec
    (boolNonidentityTwoQubitPauli_exists_specialUnitaryTransport pq))

/-- Exact specification of the chosen local Pauli transport. -/
theorem boolNonidentityTwoQubitPauliTransport_spec
    (pq : boolNonidentityTwoQubitPauliLabel) :
    boolNonidentityTwoQubitPauliTransportScalar pq ≠ 0 ∧
      (boolNonidentityTwoQubitPauliTransport pq :
        Matrix (Bool × Bool) (Bool × Bool) ℂ) *
          boolTwoQubitPauli pq.1.1 pq.1.2 *
          Matrix.conjTranspose (boolNonidentityTwoQubitPauliTransport pq :
            Matrix (Bool × Bool) (Bool × Bool) ℂ) =
        boolNonidentityTwoQubitPauliTransportScalar pq •
          boolTwoQubitPauli none (some 2) :=
  Classical.choose_spec (Classical.choose_spec
    (boolNonidentityTwoQubitPauli_exists_specialUnitaryTransport pq))

/-- A one-parameter special-unitary path in the local Pauli direction
indexed by `pq`. -/
def boolNonidentityTwoQubitPauliPath
    (pq : boolNonidentityTwoQubitPauliLabel) (t : ℝ) :
    Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
  specialUnitaryAdjoint (boolNonidentityTwoQubitPauliTransport pq) *
    terminalPauliPhase t * boolNonidentityTwoQubitPauliTransport pq

@[simp] theorem boolNonidentityTwoQubitPauliPath_zero
    (pq : boolNonidentityTwoQubitPauliLabel) :
    boolNonidentityTwoQubitPauliPath pq 0 = 1 := by
  simp [boolNonidentityTwoQubitPauliPath]

/-- Ambient matrix tangent of the Pauli-coordinate path. -/
def boolNonidentityTwoQubitPauliTangent
    (pq : boolNonidentityTwoQubitPauliLabel) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Complex.I •
    (Matrix.conjTranspose (boolNonidentityTwoQubitPauliTransport pq :
        Matrix (Bool × Bool) (Bool × Bool) ℂ) *
      (boolTwoQubitPauli none (some 2) *
        (boolNonidentityTwoQubitPauliTransport pq :
          Matrix (Bool × Bool) (Bool × Bool) ℂ)))

/-- Entrywise derivative of the Pauli-coordinate path at identity. -/
theorem entrywiseHasDerivAt_boolNonidentityTwoQubitPauliPath
    (pq : boolNonidentityTwoQubitPauliLabel) :
    EntrywiseMatrixHasDerivAt (fun t : ℝ =>
      (boolNonidentityTwoQubitPauliPath pq t :
        Matrix (Bool × Bool) (Bool × Bool) ℂ))
      (boolNonidentityTwoQubitPauliTangent pq) 0 := by
  let U := boolNonidentityTwoQubitPauliTransport pq
  have hphase := entrywiseHasDerivAt_terminalPauliPhaseMatrix
  have hderiv := (hphase.mul_right_const (U :
      Matrix (Bool × Bool) (Bool × Bool) ℂ)).mul_left_const
        (Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ))
  simpa [boolNonidentityTwoQubitPauliPath,
    boolNonidentityTwoQubitPauliTangent, specialUnitaryAdjoint, U,
    terminalPauliPhase, Matrix.mul_assoc] using hderiv

/-- Ordinary real Fréchet derivative of each Pauli-coordinate path. -/
theorem hasFDerivAt_boolNonidentityTwoQubitPauliPath
    (pq : boolNonidentityTwoQubitPauliLabel) :
    HasFDerivAt (fun t : ℝ =>
      (boolNonidentityTwoQubitPauliPath pq t :
        Matrix (Bool × Bool) (Bool × Bool) ℂ))
      (ContinuousLinearMap.toSpanSingleton ℝ
        (boolNonidentityTwoQubitPauliTangent pq)) 0 :=
  (entrywiseHasDerivAt_boolNonidentityTwoQubitPauliPath pq).hasFDerivAt

/-- Each Pauli-coordinate tangent is the corresponding literal Pauli
direction, multiplied by an explicitly nonzero complex scalar. -/
theorem boolNonidentityTwoQubitPauliTangent_eq
    (pq : boolNonidentityTwoQubitPauliLabel) :
    boolNonidentityTwoQubitPauliTangent pq =
      (Complex.I * (boolNonidentityTwoQubitPauliTransportScalar pq)⁻¹) •
        boolTwoQubitPauli pq.1.1 pq.1.2 := by
  let U := boolNonidentityTwoQubitPauliTransport pq
  let c := boolNonidentityTwoQubitPauliTransportScalar pq
  have htransport := boolNonidentityTwoQubitPauliTransport_spec pq
  have hc : c ≠ 0 := by simpa [c] using htransport.1
  have hconj : (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
      boolTwoQubitPauli pq.1.1 pq.1.2 *
      Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
        c • boolTwoQubitPauli none (some 2) := by
    simpa [U, c] using htransport.2
  have hU : (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
      Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp
      (Matrix.mem_specialUnitaryGroup_iff.mp U.2).1
  have hUadj : Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
      (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 1 :=
    mul_eq_one_comm.mp hU
  have hscaled : c •
      (Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli none (some 2) *
        (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) =
      boolTwoQubitPauli pq.1.1 pq.1.2 := by
    calc
      c • (Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
          boolTwoQubitPauli none (some 2) *
          (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) =
          Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
            (c • boolTwoQubitPauli none (some 2)) *
            (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
              rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
          ((U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
            boolTwoQubitPauli pq.1.1 pq.1.2 *
            Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) *
          (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by rw [← hconj]
      _ = (Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
          (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) *
          boolTwoQubitPauli pq.1.1 pq.1.2 *
          (Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
            (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) := by
              noncomm_ring
      _ = boolTwoQubitPauli pq.1.1 pq.1.2 := by rw [hUadj]; simp
  have hinverse :
      Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        boolTwoQubitPauli none (some 2) *
        (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      c⁻¹ • boolTwoQubitPauli pq.1.1 pq.1.2 := by
    calc
      Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
          boolTwoQubitPauli none (some 2) *
          (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) =
          (c⁻¹ * c) •
            (Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
              boolTwoQubitPauli none (some 2) *
              (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) := by
                rw [inv_mul_cancel₀ hc, one_smul]
      _ = c⁻¹ • (c •
          (Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
            boolTwoQubitPauli none (some 2) *
            (U : Matrix (Bool × Bool) (Bool × Bool) ℂ))) := by
              rw [smul_smul]
      _ = c⁻¹ • boolTwoQubitPauli pq.1.1 pq.1.2 := by rw [hscaled]
  change Complex.I •
      (Matrix.conjTranspose (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        (boolTwoQubitPauli none (some 2) *
          (U : Matrix (Bool × Bool) (Bool × Bool) ℂ))) = _
  rw [← Matrix.mul_assoc, hinverse, smul_smul]

/-- The fifteen Pauli-coordinate path tangents are complex-linearly
independent. -/
theorem linearIndependent_boolNonidentityTwoQubitPauliTangent :
    LinearIndependent ℂ boolNonidentityTwoQubitPauliTangent := by
  let u : boolNonidentityTwoQubitPauliLabel → ℂˣ := fun pq =>
    Units.mk0 (Complex.I * (boolNonidentityTwoQubitPauliTransportScalar pq)⁻¹)
      (mul_ne_zero Complex.I_ne_zero
        (inv_ne_zero (boolNonidentityTwoQubitPauliTransport_spec pq).1))
  rw [show boolNonidentityTwoQubitPauliTangent =
      u • (fun pq : boolNonidentityTwoQubitPauliLabel =>
        boolTwoQubitPauli pq.1.1 pq.1.2) by
    funext pq
    rw [boolNonidentityTwoQubitPauliTangent_eq]
    change (Complex.I * (boolNonidentityTwoQubitPauliTransportScalar pq)⁻¹) •
        boolTwoQubitPauli pq.1.1 pq.1.2 =
      ((u pq : ℂ) • boolTwoQubitPauli pq.1.1 pq.1.2)
    rfl]
  exact linearIndependent_boolNonidentityTwoQubitPauli.units_smul u

end

end GaloisForLFunctions.HTGeometry
