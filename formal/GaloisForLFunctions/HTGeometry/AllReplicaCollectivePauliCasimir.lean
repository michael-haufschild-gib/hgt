import GaloisForLFunctions.HTGeometry.AntisymmetricStructureCasimir
import GaloisForLFunctions.HTGeometry.TwoReplicaRationalLocalRotationCovariance
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# All-replica collective-Pauli Casimir

The diagonal Pauli action on an arbitrary finite replica register realizes the
exact `su(2)` bracket.  Vectorization turns its commutator action on operators
into a Hermitian matrix representation, whose quadratic Casimir is central at
every finite replica order.
-/

open scoped BigOperators Matrix Kronecker
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Structure constants of the Pauli bracket, in the `X,Y,Z` ordering. -/
def pauliStructureCoeff (a b k : Fin 3) : ℂ :=
  if (a = 0 ∧ b = 1 ∧ k = 2) ∨
      (a = 1 ∧ b = 2 ∧ k = 0) ∨
      (a = 2 ∧ b = 0 ∧ k = 1) then
    2 * Complex.I
  else if (a = 1 ∧ b = 0 ∧ k = 2) ∨
      (a = 2 ∧ b = 1 ∧ k = 0) ∨
      (a = 0 ∧ b = 2 ∧ k = 1) then
    -(2 * Complex.I)
  else 0

/-- Exact one-qubit Pauli Lie bracket. -/
theorem finiteQubitPauli_bracket (a b : Fin 3) :
    finiteQubitPauli a * finiteQubitPauli b -
        finiteQubitPauli b * finiteQubitPauli a =
      ∑ k : Fin 3, pauliStructureCoeff a b k • finiteQubitPauli k := by
  ext x y
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    simp [pauliStructureCoeff, finiteQubitPauli, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    ring_nf <;>
    simp [Complex.I_sq]

/-- Antisymmetry needed by the quadratic-Casimir contraction. -/
theorem pauliStructureCoeff_antisymmetric_contracted (a b k : Fin 3) :
    pauliStructureCoeff k b a = -pauliStructureCoeff a b k := by
  fin_cases a <;> fin_cases b <;> fin_cases k <;>
    simp [pauliStructureCoeff]

/-- Lifting a one-qubit matrix to one site is linear. -/
def finiteSingleSiteMatrixLinear
    {R : Type*} [Fintype R] [DecidableEq R]
    (j : R) :
    Matrix Bool Bool ℂ →ₗ[ℂ]
      Matrix (FiniteQubitConfiguration R) (FiniteQubitConfiguration R) ℂ where
  toFun := finiteSingleSiteMatrix j
  map_add' := finiteSingleSiteMatrix_add j
  map_smul' := finiteSingleSiteMatrix_smul j

/-- Operators lifted to distinct replica sites commute. -/
theorem finiteSingleSiteMatrix_comm_of_ne
    {R : Type*} [Fintype R] [DecidableEq R]
    {j l : R} (hjl : j ≠ l) (M N : Matrix Bool Bool ℂ) :
    finiteSingleSiteMatrix j M * finiteSingleSiteMatrix l N =
      finiteSingleSiteMatrix l N * finiteSingleSiteMatrix j M := by
  rw [finiteSingleSiteMatrix, finiteSingleSiteMatrix,
    finiteLocalMatrix_mul, finiteLocalMatrix_mul]
  congr 1
  funext s
  by_cases hsj : s = j
  · have hsl : s ≠ l := by
      intro h
      exact hjl (hsj.symm.trans h)
    simp [hsj, hjl]
  · by_cases hsl : s = l <;> simp [hsj, hsl, Ne.symm hjl]

/-- The Pauli bracket survives exact lifting to any distinguished replica. -/
theorem finiteSingleSitePauli_bracket
    {R : Type*} [Fintype R] [DecidableEq R]
    (j : R) (a b : Fin 3) :
    finiteSingleSiteMatrix j (finiteQubitPauli a) *
          finiteSingleSiteMatrix j (finiteQubitPauli b) -
        finiteSingleSiteMatrix j (finiteQubitPauli b) *
          finiteSingleSiteMatrix j (finiteQubitPauli a) =
      ∑ k : Fin 3, pauliStructureCoeff a b k •
        finiteSingleSiteMatrix j (finiteQubitPauli k) := by
  rw [finiteSingleSiteMatrix_mul, finiteSingleSiteMatrix_mul]
  change finiteSingleSiteMatrixLinear j
        (finiteQubitPauli a * finiteQubitPauli b) -
      finiteSingleSiteMatrixLinear j
        (finiteQubitPauli b * finiteQubitPauli a) = _
  rw [← map_sub]
  rw [finiteQubitPauli_bracket]
  simp only [map_sum, map_smul]
  rfl

/-- A sum commutator reduces to diagonal terms when distinct-site terms
commute. -/
private theorem ringCommutator_sum_eq_diagonal
    {R : Type*} [Fintype R] [DecidableEq R]
    {A : Type*} [Ring A]
    (f g : R → A)
    (hcross : ∀ j l, j ≠ l → f j * g l = g l * f j) :
    ringCommutator (∑ j, f j) (∑ j, g j) =
      ∑ j, ringCommutator (f j) (g j) := by
  classical
  have hfg : (∑ j, f j) * (∑ l, g l) = ∑ j, ∑ l, f j * g l := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  have hgf : (∑ j, g j) * (∑ l, f l) = ∑ j, ∑ l, g j * f l := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  have hswap : (∑ j, ∑ l, g j * f l) = ∑ j, ∑ l, g l * f j := by
    rw [Finset.sum_comm]
  rw [ringCommutator, hfg, hgf]
  calc
    (∑ j, ∑ l, f j * g l) - ∑ j, ∑ l, g j * f l =
        (∑ j, ∑ l, f j * g l) - ∑ j, ∑ l, g l * f j := by rw [hswap]
    _ = ∑ j, ∑ l, (f j * g l - g l * f j) := by
          simp only [Finset.sum_sub_distrib]
    _ = ∑ j, (f j * g j - g j * f j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_eq_single j]
          · intro l _ hlj
            rw [hcross j l (Ne.symm hlj), sub_self]
          · simp

/-- Diagonal Pauli generator on an arbitrary finite replica register. -/
def finiteReplicaCollectivePauli
    (R : Type*) [Fintype R] [DecidableEq R]
    (a : Fin 3) :
    Matrix (FiniteQubitConfiguration R) (FiniteQubitConfiguration R) ℂ :=
  ∑ j : R, finiteSingleSiteMatrix j (finiteQubitPauli a)

/-- Every diagonal collective Pauli generator is Hermitian. -/
theorem finiteReplicaCollectivePauli_isHermitian
    (R : Type*) [Fintype R] [DecidableEq R]
    (a : Fin 3) :
    (finiteReplicaCollectivePauli R a).IsHermitian := by
  rw [Matrix.IsHermitian, finiteReplicaCollectivePauli,
    Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [finiteSingleSiteMatrix_pauli]
  exact finitePauliMatrix_isHermitian _

/-- The diagonal Pauli generators realize the exact Pauli Lie bracket for
every finite replica register. -/
theorem finiteReplicaCollectivePauli_bracket
    (R : Type*) [Fintype R] [DecidableEq R]
    (a b : Fin 3) :
    finiteReplicaCollectivePauli R a * finiteReplicaCollectivePauli R b -
        finiteReplicaCollectivePauli R b * finiteReplicaCollectivePauli R a =
      ∑ k : Fin 3, pauliStructureCoeff a b k •
        finiteReplicaCollectivePauli R k := by
  change ringCommutator (finiteReplicaCollectivePauli R a)
      (finiteReplicaCollectivePauli R b) = _
  rw [finiteReplicaCollectivePauli, finiteReplicaCollectivePauli,
    ringCommutator_sum_eq_diagonal]
  · simp only [ringCommutator]
    simp_rw [finiteSingleSitePauli_bracket]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.smul_sum]
    rw [finiteReplicaCollectivePauli]
  · intro j l hjl
    exact finiteSingleSiteMatrix_comm_of_ne hjl _ _

/-- Matrix of the commutator action under column-stacking vectorization. -/
def matrixCommutatorRepresentation
    {C : Type*} [Fintype C] [DecidableEq C] :
    Matrix C C ℂ →ₗ[ℂ] Matrix (C × C) (C × C) ℂ where
  toFun G :=
    (1 : Matrix C C ℂ) ⊗ₖ G -
      G.transpose ⊗ₖ (1 : Matrix C C ℂ)
  map_add' G H := by
    ext
    simp
    ring
  map_smul' z G := by
    ext
    simp
    ring

/-- The matrix representation acts as the literal operator commutator. -/
theorem matrixCommutatorRepresentation_mulVec_vec
    {C : Type*} [Fintype C] [DecidableEq C]
    (G X : Matrix C C ℂ) :
    matrixCommutatorRepresentation G *ᵥ Matrix.vec X =
      Matrix.vec (ringCommutator G X) := by
  change (((1 : Matrix C C ℂ) ⊗ₖ G -
      G.transpose ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ Matrix.vec X) = _
  rw [Matrix.sub_mulVec,
    Matrix.kronecker_mulVec_vec, Matrix.kronecker_mulVec_vec]
  simp [ringCommutator]

/-- Commutator representations preserve Lie brackets exactly. -/
theorem matrixCommutatorRepresentation_bracket
    {C : Type*} [Fintype C] [DecidableEq C]
    (G H : Matrix C C ℂ) :
    matrixCommutatorRepresentation G *
          matrixCommutatorRepresentation H -
        matrixCommutatorRepresentation H *
          matrixCommutatorRepresentation G =
      matrixCommutatorRepresentation (G * H - H * G) := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  obtain ⟨X, rfl⟩ := Matrix.vec_bijective.2 v
  calc
    (matrixCommutatorRepresentation G *
          matrixCommutatorRepresentation H -
        matrixCommutatorRepresentation H *
          matrixCommutatorRepresentation G) *ᵥ Matrix.vec X =
      matrixCommutatorRepresentation G *ᵥ
          (matrixCommutatorRepresentation H *ᵥ Matrix.vec X) -
        matrixCommutatorRepresentation H *ᵥ
          (matrixCommutatorRepresentation G *ᵥ Matrix.vec X) := by
            simp [Matrix.sub_mulVec, Matrix.mulVec_mulVec]
    _ = Matrix.vec (ringCommutator G (ringCommutator H X)) -
        Matrix.vec (ringCommutator H (ringCommutator G X)) := by
          rw [matrixCommutatorRepresentation_mulVec_vec,
            matrixCommutatorRepresentation_mulVec_vec,
            matrixCommutatorRepresentation_mulVec_vec,
            matrixCommutatorRepresentation_mulVec_vec]
    _ = Matrix.vec (ringCommutator (G * H - H * G) X) := by
          change Matrix.vec
            (ringCommutator G (ringCommutator H X) -
              ringCommutator H (ringCommutator G X)) = _
          apply Matrix.vec_inj.mpr
          simp only [ringCommutator]
          noncomm_ring
    _ = matrixCommutatorRepresentation (G * H - H * G) *ᵥ
        Matrix.vec X :=
      (matrixCommutatorRepresentation_mulVec_vec _ _).symm

/-- Commuting generators have commuting commutator representations. -/
theorem matrixCommutatorRepresentation_comm_of_comm
    {C : Type*} [Fintype C] [DecidableEq C]
    {G H : Matrix C C ℂ} (hGH : G * H = H * G) :
    matrixCommutatorRepresentation G * matrixCommutatorRepresentation H =
      matrixCommutatorRepresentation H * matrixCommutatorRepresentation G := by
  rw [← sub_eq_zero, matrixCommutatorRepresentation_bracket, hGH, sub_self]
  simp

/-- Hermitian generators give Hermitian commutator-representation matrices. -/
theorem matrixCommutatorRepresentation_conjTranspose
    {C : Type*} [Fintype C] [DecidableEq C]
    {G : Matrix C C ℂ} (hG : G.conjTranspose = G) :
    (matrixCommutatorRepresentation G).conjTranspose =
      matrixCommutatorRepresentation G := by
  change (((1 : Matrix C C ℂ) ⊗ₖ G -
      G.transpose ⊗ₖ (1 : Matrix C C ℂ)).conjTranspose) =
    ((1 : Matrix C C ℂ) ⊗ₖ G -
      G.transpose ⊗ₖ (1 : Matrix C C ℂ))
  rw [Matrix.conjTranspose_sub,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, hG]

abbrev FiniteReplicaOperatorIndex (R : Type*) :=
  FiniteQubitConfiguration R × FiniteQubitConfiguration R

/-- Literal collective-Pauli commutator matrix at arbitrary replica order. -/
def finiteReplicaCollectiveCommutatorMatrix
    (R : Type*) [Fintype R] [DecidableEq R]
    (a : Fin 3) :
    Matrix (FiniteReplicaOperatorIndex R) (FiniteReplicaOperatorIndex R) ℂ :=
  matrixCommutatorRepresentation (finiteReplicaCollectivePauli R a)

/-- The physical collective-commutator matrices are Hermitian. -/
theorem finiteReplicaCollectiveCommutatorMatrix_conjTranspose
    (R : Type*) [Fintype R] [DecidableEq R]
    (a : Fin 3) :
    (finiteReplicaCollectiveCommutatorMatrix R a).conjTranspose =
      finiteReplicaCollectiveCommutatorMatrix R a :=
  matrixCommutatorRepresentation_conjTranspose
    (finiteReplicaCollectivePauli_isHermitian R a)

/-- Exact all-replica collective-commutator Lie bracket. -/
theorem finiteReplicaCollectiveCommutatorMatrix_bracket
    (R : Type*) [Fintype R] [DecidableEq R]
    (a b : Fin 3) :
    finiteReplicaCollectiveCommutatorMatrix R a *
          finiteReplicaCollectiveCommutatorMatrix R b -
        finiteReplicaCollectiveCommutatorMatrix R b *
          finiteReplicaCollectiveCommutatorMatrix R a =
      ∑ k : Fin 3, pauliStructureCoeff a b k •
        finiteReplicaCollectiveCommutatorMatrix R k := by
  rw [finiteReplicaCollectiveCommutatorMatrix,
    finiteReplicaCollectiveCommutatorMatrix,
    matrixCommutatorRepresentation_bracket,
    finiteReplicaCollectivePauli_bracket]
  simp only [map_sum, map_smul]
  rfl

/-- The arbitrary-replica quadratic collective-Pauli Casimir commutes with
every physical generator. -/
theorem finiteReplicaCollectiveCommutator_quadraticCasimir_commutes
    (R : Type*) [Fintype R] [DecidableEq R]
    (b : Fin 3) :
    (∑ a : Fin 3,
        finiteReplicaCollectiveCommutatorMatrix R a *
          finiteReplicaCollectiveCommutatorMatrix R a) *
        finiteReplicaCollectiveCommutatorMatrix R b =
      finiteReplicaCollectiveCommutatorMatrix R b *
        (∑ a : Fin 3,
          finiteReplicaCollectiveCommutatorMatrix R a *
            finiteReplicaCollectiveCommutatorMatrix R a) := by
  exact quadraticCasimir_commutes_of_antisymmetric_structure
    (finiteReplicaCollectiveCommutatorMatrix R)
    pauliStructureCoeff
    (finiteReplicaCollectiveCommutatorMatrix_bracket R)
    pauliStructureCoeff_antisymmetric_contracted
    b

/-- Zero matrix action is exactly zero physical operator commutator. -/
theorem finiteReplicaCollectiveCommutatorMatrix_mulVec_eq_zero_iff
    (R : Type*) [Fintype R] [DecidableEq R]
    (a : Fin 3)
    (X : Matrix (FiniteQubitConfiguration R) (FiniteQubitConfiguration R) ℂ) :
    finiteReplicaCollectiveCommutatorMatrix R a *ᵥ Matrix.vec X = 0 ↔
      ringCommutator (finiteReplicaCollectivePauli R a) X = 0 := by
  rw [finiteReplicaCollectiveCommutatorMatrix,
    matrixCommutatorRepresentation_mulVec_vec,
    Matrix.vec_eq_zero_iff]

/-! ## Arbitrary physical sites and arbitrary replicas -/

/-- Collective Pauli generator at physical site `i`, summed over every
replica. -/
def finiteReplicatedSiteCollectivePauli
    (I R : Type*) [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R]
    (i : I) (a : Fin 3) :
    Matrix (FiniteQubitConfiguration (I × R))
      (FiniteQubitConfiguration (I × R)) ℂ :=
  ∑ r : R, finiteSingleSiteMatrix (i, r) (finiteQubitPauli a)

/-- Physical-site collective generators are Hermitian at every replica
order. -/
theorem finiteReplicatedSiteCollectivePauli_isHermitian
    (I R : Type*) [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R]
    (i : I) (a : Fin 3) :
    (finiteReplicatedSiteCollectivePauli I R i a).IsHermitian := by
  rw [Matrix.IsHermitian, finiteReplicatedSiteCollectivePauli,
    Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [finiteSingleSiteMatrix_pauli]
  exact finitePauliMatrix_isHermitian _

/-- At each physical site, replica-diagonal generators realize the exact
Pauli Lie bracket, uniformly in replica order. -/
theorem finiteReplicatedSiteCollectivePauli_bracket
    (I R : Type*) [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R]
    (i : I) (a b : Fin 3) :
    finiteReplicatedSiteCollectivePauli I R i a *
          finiteReplicatedSiteCollectivePauli I R i b -
        finiteReplicatedSiteCollectivePauli I R i b *
          finiteReplicatedSiteCollectivePauli I R i a =
      ∑ k : Fin 3, pauliStructureCoeff a b k •
        finiteReplicatedSiteCollectivePauli I R i k := by
  change ringCommutator (finiteReplicatedSiteCollectivePauli I R i a)
      (finiteReplicatedSiteCollectivePauli I R i b) = _
  rw [finiteReplicatedSiteCollectivePauli,
    finiteReplicatedSiteCollectivePauli,
    ringCommutator_sum_eq_diagonal]
  · simp only [ringCommutator]
    simp_rw [finiteSingleSitePauli_bracket]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.smul_sum]
    rw [finiteReplicatedSiteCollectivePauli]
  · intro r s hrs
    apply finiteSingleSiteMatrix_comm_of_ne
    intro h
    exact hrs (congrArg Prod.snd h)

/-- Collective generators on distinct physical sites commute, including all
cross-replica terms. -/
theorem finiteReplicatedSiteCollectivePauli_comm_of_ne
    (I R : Type*) [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R]
    {i j : I} (hij : i ≠ j) (a b : Fin 3) :
    finiteReplicatedSiteCollectivePauli I R i a *
        finiteReplicatedSiteCollectivePauli I R j b =
      finiteReplicatedSiteCollectivePauli I R j b *
        finiteReplicatedSiteCollectivePauli I R i a := by
  rw [finiteReplicatedSiteCollectivePauli,
    finiteReplicatedSiteCollectivePauli]
  let f : R → Matrix (FiniteQubitConfiguration (I × R))
      (FiniteQubitConfiguration (I × R)) ℂ :=
    fun r => finiteSingleSiteMatrix (i, r) (finiteQubitPauli a)
  let g : R → Matrix (FiniteQubitConfiguration (I × R))
      (FiniteQubitConfiguration (I × R)) ℂ :=
    fun r => finiteSingleSiteMatrix (j, r) (finiteQubitPauli b)
  change (∑ r, f r) * (∑ s, g s) = (∑ s, g s) * (∑ r, f r)
  have hfg : (∑ r, f r) * (∑ s, g s) = ∑ r, ∑ s, f r * g s := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [Matrix.mul_sum]
  have hgf : (∑ s, g s) * (∑ r, f r) = ∑ s, ∑ r, g s * f r := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Matrix.mul_sum]
  rw [hfg, hgf]
  calc
    (∑ r, ∑ s, f r * g s) = ∑ r, ∑ s, g s * f r := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      apply finiteSingleSiteMatrix_comm_of_ne
      intro h
      exact hij (congrArg Prod.fst h)
    _ = ∑ s, ∑ r, g s * f r := by rw [Finset.sum_comm]

abbrev FiniteAllReplicaOperatorIndex (I R : Type*) :=
  FiniteQubitConfiguration (I × R) × FiniteQubitConfiguration (I × R)

/-- Literal operator-commutator representation for physical site `i` and
Pauli axis `a`, at arbitrary finite replica order. -/
def finiteAllReplicaCollectiveCommutatorMatrix
    (I R : Type*) [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R]
    (i : I) (a : Fin 3) :
    Matrix (FiniteAllReplicaOperatorIndex I R)
      (FiniteAllReplicaOperatorIndex I R) ℂ :=
  matrixCommutatorRepresentation
    (finiteReplicatedSiteCollectivePauli I R i a)

/-- Every physical all-replica commutator matrix is Hermitian. -/
theorem finiteAllReplicaCollectiveCommutatorMatrix_conjTranspose
    (I R : Type*) [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R]
    (i : I) (a : Fin 3) :
    (finiteAllReplicaCollectiveCommutatorMatrix I R i a).conjTranspose =
      finiteAllReplicaCollectiveCommutatorMatrix I R i a :=
  matrixCommutatorRepresentation_conjTranspose
    (finiteReplicatedSiteCollectivePauli_isHermitian I R i a)

/-- Exact sitewise `su(2)` bracket for the physical all-replica commutator
matrices. -/
theorem finiteAllReplicaCollectiveCommutatorMatrix_bracket
    (I R : Type*) [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R]
    (i : I) (a b : Fin 3) :
    finiteAllReplicaCollectiveCommutatorMatrix I R i a *
          finiteAllReplicaCollectiveCommutatorMatrix I R i b -
        finiteAllReplicaCollectiveCommutatorMatrix I R i b *
          finiteAllReplicaCollectiveCommutatorMatrix I R i a =
      ∑ k : Fin 3, pauliStructureCoeff a b k •
        finiteAllReplicaCollectiveCommutatorMatrix I R i k := by
  rw [finiteAllReplicaCollectiveCommutatorMatrix,
    finiteAllReplicaCollectiveCommutatorMatrix,
    matrixCommutatorRepresentation_bracket,
    finiteReplicatedSiteCollectivePauli_bracket]
  simp only [map_sum, map_smul]
  rfl

/-- Distinct physical sites give commuting all-replica commutator matrices. -/
theorem finiteAllReplicaCollectiveCommutatorMatrix_comm_of_ne
    (I R : Type*) [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R]
    {i j : I} (hij : i ≠ j) (a b : Fin 3) :
    finiteAllReplicaCollectiveCommutatorMatrix I R i a *
        finiteAllReplicaCollectiveCommutatorMatrix I R j b =
      finiteAllReplicaCollectiveCommutatorMatrix I R j b *
        finiteAllReplicaCollectiveCommutatorMatrix I R i a :=
  matrixCommutatorRepresentation_comm_of_comm
    (finiteReplicatedSiteCollectivePauli_comm_of_ne I R hij a b)

/-- Each physical site's three-axis quadratic Casimir commutes with every
axis at that site. -/
theorem finiteAllReplicaSiteQuadraticCasimir_commutes
    (I R : Type*) [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R]
    (i : I) (b : Fin 3) :
    (∑ a : Fin 3,
        finiteAllReplicaCollectiveCommutatorMatrix I R i a *
          finiteAllReplicaCollectiveCommutatorMatrix I R i a) *
        finiteAllReplicaCollectiveCommutatorMatrix I R i b =
      finiteAllReplicaCollectiveCommutatorMatrix I R i b *
        (∑ a : Fin 3,
          finiteAllReplicaCollectiveCommutatorMatrix I R i a *
            finiteAllReplicaCollectiveCommutatorMatrix I R i a) := by
  exact quadraticCasimir_commutes_of_antisymmetric_structure
    (finiteAllReplicaCollectiveCommutatorMatrix I R i)
    pauliStructureCoeff
    (finiteAllReplicaCollectiveCommutatorMatrix_bracket I R i)
    pauliStructureCoeff_antisymmetric_contracted
    b

/-- Full arbitrary-site, arbitrary-replica collective-Pauli Casimir
centrality.  The generator index is the physical-site/Pauli-axis pair. -/
theorem finiteAllReplicaCollectiveCommutator_quadraticCasimir_commutes
    (I R : Type*) [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R]
    (j : I) (b : Fin 3) :
    (∑ p : I × Fin 3,
        finiteAllReplicaCollectiveCommutatorMatrix I R p.1 p.2 *
          finiteAllReplicaCollectiveCommutatorMatrix I R p.1 p.2) *
        finiteAllReplicaCollectiveCommutatorMatrix I R j b =
      finiteAllReplicaCollectiveCommutatorMatrix I R j b *
        (∑ p : I × Fin 3,
          finiteAllReplicaCollectiveCommutatorMatrix I R p.1 p.2 *
            finiteAllReplicaCollectiveCommutatorMatrix I R p.1 p.2) := by
  rw [Fintype.sum_prod_type, Finset.sum_mul, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : i = j
  · subst i
    exact finiteAllReplicaSiteQuadraticCasimir_commutes I R j b
  · rw [Finset.sum_mul, Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    let A := finiteAllReplicaCollectiveCommutatorMatrix I R i a
    let B := finiteAllReplicaCollectiveCommutatorMatrix I R j b
    have hAB : A * B = B * A :=
      finiteAllReplicaCollectiveCommutatorMatrix_comm_of_ne I R hij a b
    change (A * A) * B = B * (A * A)
    calc
      (A * A) * B = A * (A * B) := by noncomm_ring
      _ = A * (B * A) := by rw [hAB]
      _ = (A * B) * A := by noncomm_ring
      _ = (B * A) * A := by rw [hAB]
      _ = B * (A * A) := by noncomm_ring

end

end GaloisForLFunctions.HTGeometry
