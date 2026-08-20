import GaloisForLFunctions.HTGeometry.HLSKinematics
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

/-!
# Finite scattering data for Haag--Łopuszański--Sohnius systems

This module formalizes the finite-dimensional equational core of an HLS input:
unitary scattering, a unitary Poincaré action, a fermion-parity grading, and an
odd scattering symmetry.  `hlsFiniteScatteringWitness` is a closed inhabitant
with nonidentity scattering.

It is deliberately *not* claimed to be a physical QFT S-matrix.  A physical
HLS application additionally needs an infinite Fock/Hilbert construction,
positive-energy Poincaré representations, locality or analyticity of
scattering, and spin-statistics.  Those analytic hypotheses are not present in
the current Lean corpus.
-/

noncomputable section

open Matrix
open scoped Kronecker Matrix

namespace GaloisForLFunctions.HTGeometry

/-- A finite labelled asymptotic Hilbert sector.  This is a finite sector only, not a
completed bosonic or fermionic Fock space. -/
abbrev HLSFiniteAsymptoticSector (ι : Type) := ι → ℂ

/-- Total four-momentum of an ordered finite asymptotic configuration. -/
def hlsTotalMomentum {ι : Type} (momentum : ι → HLSMinkowskiVector)
    (configuration : List ι) : HLSMinkowskiVector :=
  (configuration.map momentum).sum

/-- Total momentum is additive under concatenating incoming/outgoing labelled configurations. -/
theorem hlsTotalMomentum_append {ι : Type} (momentum : ι → HLSMinkowskiVector)
    (left right : List ι) :
    hlsTotalMomentum momentum (left ++ right) =
      hlsTotalMomentum momentum left + hlsTotalMomentum momentum right := by
  simp [hlsTotalMomentum]

/-- Matrix anticommutator. -/
def hlsMatrixAnticommutator {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  A * B + B * A

/-- Matrix-level finite HLS scattering data.  The fields state the algebraic invariances which
are meaningful in finite dimension; they intentionally do not encode analyticity or locality. -/
structure HLSFiniteScatteringSystem (ι : Type) [Fintype ι] [DecidableEq ι] where
  /-- Unitary scattering operator on the finite asymptotic sector. -/
  sMatrix : Matrix.unitaryGroup ι ℂ
  /-- Unitary action of the proper orthochronous Poincaré group on that sector. -/
  poincareAction : HLSPhysicalPoincareGroup →* Matrix.unitaryGroup ι ℂ
  /-- Fermion-parity involution. -/
  parity : Matrix.unitaryGroup ι ℂ
  /-- Odd infinitesimal symmetry candidate. -/
  supercharge : Matrix ι ι ℂ
  /-- Excludes the identity S-matrix case that evades HLS/Coleman--Mandula rigidity. -/
  sMatrix_nonidentity : (sMatrix : Matrix ι ι ℂ) ≠ 1
  /-- Poincaré invariance of the scattering operator. -/
  poincare_invariant : ∀ g,
    (sMatrix : Matrix ι ι ℂ) * (poincareAction g : Matrix ι ι ℂ) =
      (poincareAction g : Matrix ι ι ℂ) * sMatrix
  /-- The parity grading is a `ℤ₂` involution. -/
  parity_squared : (parity : Matrix ι ι ℂ) * parity = 1
  /-- Scattering preserves the fermion-parity grading. -/
  sMatrix_even : (sMatrix : Matrix ι ι ℂ) * parity = parity * sMatrix
  /-- The distinguished charge is odd for that grading. -/
  supercharge_odd : (parity : Matrix ι ι ℂ) * supercharge = -(supercharge * parity)
  /-- The distinguished charge is a symmetry of scattering. -/
  supercharge_symmetry : (sMatrix : Matrix ι ι ℂ) * supercharge = supercharge * sMatrix
  /-- Finite one-charge Clifford closure.  A physical Weyl relation is recorded separately in
`HLSWeylSuperalgebraData`. -/
  supercharge_anticommutator : hlsMatrixAnticommutator supercharge supercharge = (2 : ℂ) • 1

/-- Two binary labels: first is boson/fermion parity, second is an internal flavour. -/
abbrev HLSTwoQubit := Fin 2 × Fin 2

private abbrev HLSQubit := Fin 2

private def hlsIdTwo : Matrix HLSQubit HLSQubit ℂ := 1

private def hlsPauliX : Matrix HLSQubit HLSQubit ℂ :=
  !![0, 1;
     1, 0]

private def hlsPauliZ : Matrix HLSQubit HLSQubit ℂ :=
  !![1, 0;
     0, -1]

private theorem hlsIdTwo_unitary : hlsIdTwo ∈ Matrix.unitaryGroup HLSQubit ℂ := by
  simp [hlsIdTwo]

private theorem hlsPauliX_unitary : hlsPauliX ∈ Matrix.unitaryGroup HLSQubit ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hlsPauliX, Matrix.mul_apply, Fin.sum_univ_two]

private theorem hlsPauliX_squared : hlsPauliX * hlsPauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hlsPauliX, Matrix.mul_apply, Fin.sum_univ_two]

private theorem hlsPauliZ_unitary : hlsPauliZ ∈ Matrix.unitaryGroup HLSQubit ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hlsPauliZ, Matrix.mul_apply, Fin.sum_univ_two]

private theorem hlsPauliZ_squared : hlsPauliZ * hlsPauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hlsPauliZ, Matrix.mul_apply, Fin.sum_univ_two]

private theorem hlsPauliZ_mul_hlsPauliX :
    hlsPauliZ * hlsPauliX = -hlsPauliX * hlsPauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hlsPauliZ, hlsPauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- Nonidentity unitary finite scattering: flips internal flavour and preserves parity. -/
def hlsFiniteScatteringMatrix : Matrix HLSTwoQubit HLSTwoQubit ℂ :=
  Matrix.kronecker hlsIdTwo hlsPauliX

/-- Fermion parity on the finite witness. -/
def hlsFiniteParityMatrix : Matrix HLSTwoQubit HLSTwoQubit ℂ :=
  Matrix.kronecker hlsPauliZ hlsIdTwo

/-- Odd charge on the finite witness. -/
def hlsFiniteSupercharge : Matrix HLSTwoQubit HLSTwoQubit ℂ :=
  Matrix.kronecker hlsPauliX hlsIdTwo

private theorem hlsFiniteScatteringMatrix_unitary :
    hlsFiniteScatteringMatrix ∈ Matrix.unitaryGroup HLSTwoQubit ℂ :=
  Matrix.kronecker_mem_unitary hlsIdTwo_unitary hlsPauliX_unitary

private theorem hlsFiniteParityMatrix_unitary :
    hlsFiniteParityMatrix ∈ Matrix.unitaryGroup HLSTwoQubit ℂ :=
  Matrix.kronecker_mem_unitary hlsPauliZ_unitary hlsIdTwo_unitary

private theorem hlsFiniteScatteringMatrix_nonidentity : hlsFiniteScatteringMatrix ≠ 1 := by
  intro h
  have h01 := congr_fun (congr_fun h (0, 0)) (0, 1)
  norm_num [hlsFiniteScatteringMatrix, hlsIdTwo, hlsPauliX, Matrix.one_apply] at h01

private theorem hlsFiniteScattering_commutes_supercharge :
    hlsFiniteScatteringMatrix * hlsFiniteSupercharge =
      hlsFiniteSupercharge * hlsFiniteScatteringMatrix := by
  rw [show hlsFiniteScatteringMatrix = hlsIdTwo ⊗ₖ hlsPauliX by rfl,
    show hlsFiniteSupercharge = hlsPauliX ⊗ₖ hlsIdTwo by rfl,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp [hlsIdTwo]

private theorem hlsFiniteSupercharge_is_odd :
    hlsFiniteParityMatrix * hlsFiniteSupercharge =
      -(hlsFiniteSupercharge * hlsFiniteParityMatrix) := by
  rw [show hlsFiniteParityMatrix = hlsPauliZ ⊗ₖ hlsIdTwo by rfl,
    show hlsFiniteSupercharge = hlsPauliX ⊗ₖ hlsIdTwo by rfl,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    hlsPauliZ_mul_hlsPauliX]
  ext i j
  simp [hlsIdTwo]

private theorem hlsFiniteSupercharge_squared :
    hlsFiniteSupercharge * hlsFiniteSupercharge = 1 := by
  rw [show hlsFiniteSupercharge = hlsPauliX ⊗ₖ hlsIdTwo by rfl,
    ← Matrix.mul_kronecker_mul]
  simp [hlsIdTwo, hlsPauliX_squared]

/-- Closed one-charge Clifford relation in the finite witness. -/
theorem hlsFiniteSupercharge_anticommutator :
    hlsMatrixAnticommutator hlsFiniteSupercharge hlsFiniteSupercharge = (2 : ℂ) • 1 := by
  rw [hlsMatrixAnticommutator, hlsFiniteSupercharge_squared]
  simp [two_smul]

private def hlsFiniteTrivialPoincareAction :
    HLSPhysicalPoincareGroup →* Matrix.unitaryGroup HLSTwoQubit ℂ := 1

private theorem hlsFiniteScattering_poincare_invariant (g : HLSPhysicalPoincareGroup) :
    hlsFiniteScatteringMatrix *
        (hlsFiniteTrivialPoincareAction g : Matrix HLSTwoQubit HLSTwoQubit ℂ) =
      (hlsFiniteTrivialPoincareAction g : Matrix HLSTwoQubit HLSTwoQubit ℂ) *
        hlsFiniteScatteringMatrix := by
  simp [hlsFiniteTrivialPoincareAction]

/-- Closed finite witness for the matrix-level HLS invariance interface.  Its Poincaré action is
trivial, so it establishes consistency of the algebraic interface only; it is not a physical
one-particle representation. -/
def hlsFiniteScatteringWitness : HLSFiniteScatteringSystem HLSTwoQubit where
  sMatrix := ⟨hlsFiniteScatteringMatrix, hlsFiniteScatteringMatrix_unitary⟩
  poincareAction := hlsFiniteTrivialPoincareAction
  parity := ⟨hlsFiniteParityMatrix, hlsFiniteParityMatrix_unitary⟩
  supercharge := hlsFiniteSupercharge
  sMatrix_nonidentity := hlsFiniteScatteringMatrix_nonidentity
  poincare_invariant := hlsFiniteScattering_poincare_invariant
  parity_squared := by
    change hlsFiniteParityMatrix * hlsFiniteParityMatrix = 1
    rw [show hlsFiniteParityMatrix = hlsPauliZ ⊗ₖ hlsIdTwo by rfl,
      ← Matrix.mul_kronecker_mul]
    simp [hlsIdTwo, hlsPauliZ_squared]
  sMatrix_even := by
    change hlsFiniteScatteringMatrix * hlsFiniteParityMatrix =
      hlsFiniteParityMatrix * hlsFiniteScatteringMatrix
    rw [show hlsFiniteScatteringMatrix = hlsIdTwo ⊗ₖ hlsPauliX by rfl,
      show hlsFiniteParityMatrix = hlsPauliZ ⊗ₖ hlsIdTwo by rfl,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp [hlsIdTwo]
  supercharge_odd := hlsFiniteSupercharge_is_odd
  supercharge_symmetry := hlsFiniteScattering_commutes_supercharge
  supercharge_anticommutator := hlsFiniteSupercharge_anticommutator

/-- Closed finite version of the indispensable HLS/Coleman--Mandula boundary: when `S = 1`,
a nonidentity internal unitary can commute with scattering.  Thus no premise-free classification
of all scattering symmetries is possible. -/
theorem hlsIdentityScattering_has_nontrivial_commuting_unitary :
    hlsPauliX ∈ Matrix.unitaryGroup HLSQubit ℂ ∧ hlsPauliX ≠ 1 ∧
      (1 : Matrix HLSQubit HLSQubit ℂ) * hlsPauliX = hlsPauliX * 1 := by
  refine ⟨hlsPauliX_unitary, ?_, by simp⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  norm_num [hlsPauliX, Matrix.one_apply] at h00

end GaloisForLFunctions.HTGeometry
