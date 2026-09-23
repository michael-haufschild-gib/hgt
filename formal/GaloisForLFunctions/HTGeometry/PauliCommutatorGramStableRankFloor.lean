import GaloisForLFunctions.HTGeometry.PauliCommutatorDirectionEnergyFloor
import GaloisForLFunctions.HTGeometry.SingularTraceCapCompiler
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperatorBound
import GaloisForLFunctions.HTGeometry.ActivePauliShellRateLaw
import GaloisForLFunctions.HTGeometry.GaussianCovarianceStableRankLowerTail

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem pauliWeight_eq_zero_iff_eq_identity
    {n : ℕ} (P : Fin n → Option (Fin 3)) :
    pauliWeight P = 0 ↔ P = pauliIdentityLabel n := by
  constructor
  · intro hzero
    funext i
    by_contra hi
    have himem : i ∈ pauliSupport P := mem_pauliSupport.mpr hi
    have hcard : 0 < (pauliSupport P).card := Finset.card_pos.mpr ⟨i, himem⟩
    rw [← pauliWeight_eq_card_pauliSupport, hzero] at hcard
    omega
  · rintro rfl
    simp [pauliWeight, pauliIdentityLabel]

def boundedLocalPauliLabelEquivTraceless (n q : ℕ) :
    boundedLocalPauliLabel n q ≃ PauliTracelessLabel n q where
  toFun Q := ⟨Q.1, by
    have hQ := mem_nonidentityPauliWords.mp Q.2
    exact ⟨hQ.2, fun hidentity => by
      have hzero := (pauliWeight_eq_zero_iff_eq_identity Q.1).mpr hidentity
      omega⟩⟩
  invFun Q := ⟨Q.1, mem_nonidentityPauliWords.mpr ⟨by
    have hnezero : pauliWeight Q.1 ≠ 0 := fun hzero =>
      Q.2.2 ((pauliWeight_eq_zero_iff_eq_identity Q.1).mp hzero)
    omega, Q.2.1⟩⟩
  left_inv Q := Subtype.ext rfl
  right_inv Q := Subtype.ext rfl

theorem sum_traceless_commutatorWeight_eq_boundedLocal
    {n q : ℕ}
    (A : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    (∑ Q : PauliTracelessLabel n q,
      frobSq (finitePauliMatrix Q.1 * A - A * finitePauliMatrix Q.1)) =
      ∑ Q : boundedLocalPauliLabel n q,
        boundedLocalPauliCommutatorWeight A Q := by
  symm
  apply Fintype.sum_equiv (boundedLocalPauliLabelEquivTraceless n q)
  intro Q
  rfl

abbrev TwoLocalPauliCoefficientSpace (n : ℕ) :=
  EuclideanSpace ℝ (PauliTracelessLabel n 2)

def realActivePauliHamiltonian
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) :
    Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ :=
  activePauliHamiltonian fun Q => ((WithLp.ofLp x Q : ℝ) : ℂ)

theorem realActivePauliHamiltonian_add
    {n : ℕ} (x y : TwoLocalPauliCoefficientSpace n) :
    realActivePauliHamiltonian (x + y) =
      realActivePauliHamiltonian x + realActivePauliHamiltonian y := by
  simp [realActivePauliHamiltonian, activePauliHamiltonian,
    add_smul, Finset.sum_add_distrib]

theorem realActivePauliHamiltonian_smul
    {n : ℕ} (r : ℝ) (x : TwoLocalPauliCoefficientSpace n) :
    realActivePauliHamiltonian (r • x) =
      (r : ℂ) • realActivePauliHamiltonian x := by
  rw [realActivePauliHamiltonian, realActivePauliHamiltonian,
    activePauliHamiltonian, activePauliHamiltonian, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro Q _
  rw [smul_smul]
  congr 1
  norm_cast

def twoLocalPauliUnitaryCommutatorMap
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    TwoLocalPauliCoefficientSpace n →ₗ[ℝ]
      EuclideanSpace ℂ
        (FiniteQubitConfiguration (Fin n) × FiniteQubitConfiguration (Fin n)) where
  toFun x := matVec
    (realActivePauliHamiltonian x *
        (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) -
      (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) *
        realActivePauliHamiltonian x)
  map_add' x y := by
    rw [realActivePauliHamiltonian_add]
    have hmatrix :
        (realActivePauliHamiltonian x + realActivePauliHamiltonian y) *
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) -
          (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) *
            (realActivePauliHamiltonian x + realActivePauliHamiltonian y) =
          (realActivePauliHamiltonian x * U - U * realActivePauliHamiltonian x) +
            (realActivePauliHamiltonian y * U - U * realActivePauliHamiltonian y) := by
      noncomm_ring
    rw [hmatrix]
    rfl
  map_smul' r x := by
    rw [realActivePauliHamiltonian_smul]
    rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
    rfl

theorem norm_twoLocalPauliUnitaryCommutatorMap_sq
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (x : TwoLocalPauliCoefficientSpace n) :
    ‖twoLocalPauliUnitaryCommutatorMap U x‖ ^ (2 : ℕ) =
      frobSq
        (realActivePauliHamiltonian x *
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) -
          (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) *
            realActivePauliHamiltonian x) := by
  change hsNorm
      (realActivePauliHamiltonian x *
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) -
        (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) *
          realActivePauliHamiltonian x) ^ (2 : ℕ) = _
  rw [hsNorm_sq]
  rfl

theorem realActivePauliHamiltonian_basisFun
    {n : ℕ} (Q : PauliTracelessLabel n 2) :
    realActivePauliHamiltonian
        ((EuclideanSpace.basisFun (PauliTracelessLabel n 2) ℝ) Q) =
      finitePauliMatrix Q.1 := by
  simp [realActivePauliHamiltonian, activePauliHamiltonian]

theorem hsNorm_commutator_unitary_le_two
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    hsNorm (H * (U : Matrix ι ι ℂ) - (U : Matrix ι ι ℂ) * H) ≤
      2 * hsNorm H := by
  have hUnorm : ‖(U : Matrix ι ι ℂ)‖ = 1 := by
    exact CStarRing.norm_coe_unitary ⟨(U : Matrix ι ι ℂ), U.2⟩
  have hright : hsNorm (H * (U : Matrix ι ι ℂ)) ≤ hsNorm H := by
    simpa [hUnorm] using hsNorm_mul_le' H (U : Matrix ι ι ℂ)
  have hleft : hsNorm ((U : Matrix ι ι ℂ) * H) ≤ hsNorm H := by
    simpa [hUnorm] using hsNorm_mul_le (U : Matrix ι ι ℂ) H
  calc
    hsNorm (H * (U : Matrix ι ι ℂ) - (U : Matrix ι ι ℂ) * H) =
        ‖matVec (H * (U : Matrix ι ι ℂ)) -
          matVec ((U : Matrix ι ι ℂ) * H)‖ := rfl
    _ ≤ ‖matVec (H * (U : Matrix ι ι ℂ))‖ +
        ‖matVec ((U : Matrix ι ι ℂ) * H)‖ := norm_sub_le _ _
    _ = hsNorm (H * (U : Matrix ι ι ℂ)) +
        hsNorm ((U : Matrix ι ι ℂ) * H) := rfl
    _ ≤ hsNorm H + hsNorm H := add_le_add hright hleft
    _ = 2 * hsNorm H := by ring

theorem frobSq_realActivePauliHamiltonian
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) :
    frobSq (realActivePauliHamiltonian x) =
      (2 : ℝ) ^ n * ‖x‖ ^ (2 : ℕ) := by
  rw [realActivePauliHamiltonian, frobSq_activePauliHamiltonian]
  rw [EuclideanSpace.norm_sq_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro Q _
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem frobSq_eq_hsNorm_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    frobSq A = hsNorm A ^ (2 : ℕ) := by
  rw [hsNorm_sq]
  rfl

theorem twoLocalPauliUnitaryCommutatorMap_norm_sq_le
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (x : TwoLocalPauliCoefficientSpace n) :
    ‖twoLocalPauliUnitaryCommutatorMap U x‖ ^ (2 : ℕ) ≤
      (4 * (2 : ℝ) ^ n) * ‖x‖ ^ (2 : ℕ) := by
  let H := realActivePauliHamiltonian x
  have hcomm := hsNorm_commutator_unitary_le_two H U
  have hsquare :
      hsNorm
          (H * (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) -
            (U : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ) * H) ^ (2 : ℕ) ≤
        (2 * hsNorm H) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (hsNorm_nonneg _) hcomm 2
  rw [norm_twoLocalPauliUnitaryCommutatorMap_sq]
  change frobSq
      (H * (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) -
        (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) * H) ≤ _
  rw [frobSq_eq_hsNorm_sq]
  calc
    hsNorm
        (H * (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) -
          (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) * H) ^ (2 : ℕ) ≤
        (2 * hsNorm H) ^ (2 : ℕ) := hsquare
    _ = 4 * hsNorm H ^ (2 : ℕ) := by ring
    _ = 4 * frobSq H := by rw [frobSq_eq_hsNorm_sq]
    _ = (4 * (2 : ℝ) ^ n) * ‖x‖ ^ (2 : ℕ) := by
      rw [show frobSq H = (2 : ℝ) ^ n * ‖x‖ ^ (2 : ℕ) by
        exact frobSq_realActivePauliHamiltonian x]
      ring

theorem sum_basis_twoLocalPauliUnitaryCommutatorMap_norm_sq
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    (∑ Q : PauliTracelessLabel n 2,
        ‖twoLocalPauliUnitaryCommutatorMap U
          ((EuclideanSpace.basisFun (PauliTracelessLabel n 2) ℝ) Q)‖ ^ (2 : ℕ)) =
      ∑ Q : boundedLocalPauliLabel n 2,
        boundedLocalPauliCommutatorWeight
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) Q := by
  rw [← sum_traceless_commutatorWeight_eq_boundedLocal]
  apply Finset.sum_congr rfl
  intro Q _
  rw [norm_twoLocalPauliUnitaryCommutatorMap_sq,
    realActivePauliHamiltonian_basisFun]

theorem sum_basis_twoLocalPauliUnitaryCommutatorMap_norm_sq_ge
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    4 * ((n - 1 : ℕ) : ℝ) *
        frobSq
          ((U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) -
            pauliScalarPart
              (U : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ)) ≤
      ∑ Q : PauliTracelessLabel n 2,
        ‖twoLocalPauliUnitaryCommutatorMap U
          ((EuclideanSpace.basisFun (PauliTracelessLabel n 2) ℝ) Q)‖ ^ (2 : ℕ) := by
  rw [sum_basis_twoLocalPauliUnitaryCommutatorMap_norm_sq]
  simpa [boundedLocalPauliCommutatorWeight] using
    boundedLocalPauli_commutator_energy_ge_scalarDistance
      (n := n) (q := 2) (by omega)
      (U : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)

def twoLocalPauliUnitaryCommutatorGramStableRatio
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) : ℝ :=
  (∑ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
      (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ)) ^ (2 : ℕ) /
    ∑ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
      (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (4 : ℕ)

/-- Target-specific mass of Pauli coefficients seen by the complete two-local
anticommutation incidence relation.  Unlike normalized trace deficit, this
retains whether target mass is low-weight, extensive, or fully spread. -/
def twoLocalPauliUnitaryAnticommutingIncidenceMass
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) : ℝ :=
  ∑ Q : boundedLocalPauliLabel n 2,
    pauliAnticommutingIncidenceMass
      (fun P => ‖pauliCoeff
        (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) P.1‖ ^ (2 : ℕ)) Q

/-- Pauli-support boundary moment of a unitary target.  Coefficient mass at
weight `w` is charged by `w(n-w)`, the number of active/inactive site pairs. -/
def twoLocalPauliUnitaryBoundaryMoment
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) : ℝ :=
  ∑ P : NonzeroPauliCharacter (Fin n),
    ((pauliWeight P.1 * (n - pauliWeight P.1) : ℕ) : ℝ) *
      ‖pauliCoeff
        (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) P.1‖ ^ (2 : ℕ)

/-- Active-support moment of a unitary target.  Coefficient mass at Pauli
weight `w` is charged by `w(n-1)`, so full-support mass is not lost. -/
def twoLocalPauliUnitaryActiveWeightMoment
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) : ℝ :=
  ∑ P : NonzeroPauliCharacter (Fin n),
    ((pauliWeight P.1 * (n - 1) : ℕ) : ℝ) *
      ‖pauliCoeff
        (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) P.1‖ ^ (2 : ℕ)

/-- Enhanced active-support moment.  Weight `w` is charged by `2wn`, retaining
both anticommuting axes and all one-site directions. -/
def twoLocalPauliUnitaryEnhancedActiveWeightMoment
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) : ℝ :=
  ∑ P : NonzeroPauliCharacter (Fin n),
    ((2 * pauliWeight P.1 * n : ℕ) : ℝ) *
      ‖pauliCoeff
        (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) P.1‖ ^ (2 : ℕ)

/-- Full ordinary-two-local Pauli-weight moment.  Weight `w` is charged by
`2w(3n-2w)`, retaining all axes on every active/inactive site pair. -/
def twoLocalPauliUnitaryFullWeightPolynomialMoment
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) : ℝ :=
  ∑ P : NonzeroPauliCharacter (Fin n),
    ((2 * pauliWeight P.1 * (3 * n - 2 * pauliWeight P.1) : ℕ) : ℝ) *
      ‖pauliCoeff
        (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) P.1‖ ^ (2 : ℕ)

theorem twoLocalPauliUnitaryAnticommutingIncidenceMass_nonneg
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    0 ≤ twoLocalPauliUnitaryAnticommutingIncidenceMass U := by
  rw [twoLocalPauliUnitaryAnticommutingIncidenceMass]
  apply Finset.sum_nonneg
  intro Q _
  rw [pauliAnticommutingIncidenceMass]
  apply Finset.sum_nonneg
  intro P _
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

theorem twoLocalPauliUnitaryBoundaryMoment_nonneg
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    0 ≤ twoLocalPauliUnitaryBoundaryMoment U := by
  rw [twoLocalPauliUnitaryBoundaryMoment]
  exact Finset.sum_nonneg fun P _ =>
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem twoLocalPauliUnitaryActiveWeightMoment_nonneg
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    0 ≤ twoLocalPauliUnitaryActiveWeightMoment U := by
  rw [twoLocalPauliUnitaryActiveWeightMoment]
  exact Finset.sum_nonneg fun P _ =>
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem twoLocalPauliUnitaryEnhancedActiveWeightMoment_nonneg
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    0 ≤ twoLocalPauliUnitaryEnhancedActiveWeightMoment U := by
  rw [twoLocalPauliUnitaryEnhancedActiveWeightMoment]
  exact Finset.sum_nonneg fun P _ =>
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem twoLocalPauliUnitaryFullWeightPolynomialMoment_nonneg
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    0 ≤ twoLocalPauliUnitaryFullWeightPolynomialMoment U := by
  rw [twoLocalPauliUnitaryFullWeightPolynomialMoment]
  exact Finset.sum_nonneg fun P _ =>
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- Pauli isoperimetry: target incidence dominates its support-boundary
moment.  Extensive-weight target mass therefore forces quadratic incidence. -/
theorem twoLocalPauliUnitaryBoundaryMoment_le_incidenceMass
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    twoLocalPauliUnitaryBoundaryMoment U ≤
      twoLocalPauliUnitaryAnticommutingIncidenceMass U := by
  simpa [twoLocalPauliUnitaryBoundaryMoment,
    twoLocalPauliUnitaryAnticommutingIncidenceMass] using
    total_pauliAnticommutingIncidenceMass_ge_boundaryMoment
      (n := n) (q := 2) (by omega)
      (fun P : NonzeroPauliCharacter (Fin n) =>
        ‖pauliCoeff
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) P.1‖ ^ (2 : ℕ))
      (fun P => sq_nonneg _)

/-- Active-support incidence law.  Exact two-local incidence dominates
`w(n-1)` coefficient mass, including Pauli strings supported on every site. -/
theorem twoLocalPauliUnitaryActiveWeightMoment_le_incidenceMass
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    twoLocalPauliUnitaryActiveWeightMoment U ≤
      twoLocalPauliUnitaryAnticommutingIncidenceMass U := by
  simpa [twoLocalPauliUnitaryActiveWeightMoment,
    twoLocalPauliUnitaryAnticommutingIncidenceMass] using
    total_pauliAnticommutingIncidenceMass_ge_activeWeightMoment
      (n := n) (q := 2) (by omega)
      (fun P : NonzeroPauliCharacter (Fin n) =>
        ‖pauliCoeff
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) P.1‖ ^ (2 : ℕ))
      (fun P => sq_nonneg _)

/-- Enhanced active-support incidence law.  Exact two-local incidence
dominates the full `2wn` coefficient moment. -/
theorem twoLocalPauliUnitaryEnhancedActiveWeightMoment_le_incidenceMass
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    twoLocalPauliUnitaryEnhancedActiveWeightMoment U ≤
      twoLocalPauliUnitaryAnticommutingIncidenceMass U := by
  simpa [twoLocalPauliUnitaryEnhancedActiveWeightMoment,
    twoLocalPauliUnitaryAnticommutingIncidenceMass] using
    total_pauliAnticommutingIncidenceMass_ge_enhancedActiveWeightMoment
      (n := n) (q := 2) (by omega)
      (fun P : NonzeroPauliCharacter (Fin n) =>
        ‖pauliCoeff
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) P.1‖ ^ (2 : ℕ))
      (fun P => sq_nonneg _)

/-- Exact full Pauli-weight polynomial incidence law for a unitary target. -/
theorem twoLocalPauliUnitaryFullWeightPolynomialMoment_eq_incidenceMass
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    twoLocalPauliUnitaryFullWeightPolynomialMoment U =
      twoLocalPauliUnitaryAnticommutingIncidenceMass U := by
  simpa [twoLocalPauliUnitaryFullWeightPolynomialMoment,
    twoLocalPauliUnitaryAnticommutingIncidenceMass] using
    total_pauliAnticommutingIncidenceMass_eq_fullWeightPolynomialMoment
      (n := n)
      (fun P : NonzeroPauliCharacter (Fin n) =>
        ‖pauliCoeff
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) P.1‖ ^ (2 : ℕ))

theorem twoLocalPauliUnitaryFullWeightPolynomialMoment_le_incidenceMass
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    twoLocalPauliUnitaryFullWeightPolynomialMoment U ≤
      twoLocalPauliUnitaryAnticommutingIncidenceMass U :=
  (twoLocalPauliUnitaryFullWeightPolynomialMoment_eq_incidenceMass U).le

/-- Exact Gram trace: target-specific incidence mass is not a surrogate but
the literal covariance trace after the universal Pauli normalization. -/
theorem sum_sq_twoLocalPauliUnitaryCommutator_singularValues_eq_incidenceMass
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    (∑ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
        (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ)) =
      4 * (2 : ℝ) ^ n *
        twoLocalPauliUnitaryAnticommutingIncidenceMass U := by
  have hnrank :
      Module.finrank ℝ (TwoLocalPauliCoefficientSpace n) =
        Fintype.card (PauliTracelessLabel n 2) := by
    exact finrank_euclideanSpace
  rw [sum_sq_singularValues_eq_sum_norm_orthonormalBasis
    (twoLocalPauliUnitaryCommutatorMap U) hnrank
    (EuclideanSpace.basisFun (PauliTracelessLabel n 2) ℝ)]
  rw [sum_basis_twoLocalPauliUnitaryCommutatorMap_norm_sq]
  rw [show (∑ Q : boundedLocalPauliLabel n 2,
      boundedLocalPauliCommutatorWeight
        (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) Q) =
      ∑ Q : boundedLocalPauliLabel n 2,
        frobSq
          (finitePauliMatrix Q.1 *
              (U : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ) -
            (U : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ) *
              finitePauliMatrix Q.1) by rfl]
  exact boundedLocalPauli_total_commutator_energy_matrix_eq_incidenceMass
    (q := 2)
    (U : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)

/-- Exact observer-Jacobian trace law.  The full covariance trace is the
explicit support polynomial `2w(3n-2w)` integrated against Pauli coefficient
mass; no incidence surrogate or inequality remains. -/
theorem sum_sq_twoLocalPauliUnitaryCommutator_singularValues_eq_fullWeightPolynomialMoment
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    (∑ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
        (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ)) =
      4 * (2 : ℝ) ^ n *
        twoLocalPauliUnitaryFullWeightPolynomialMoment U := by
  rw [sum_sq_twoLocalPauliUnitaryCommutator_singularValues_eq_incidenceMass,
    twoLocalPauliUnitaryFullWeightPolynomialMoment_eq_incidenceMass]

theorem twoLocalPauliUnitaryCommutatorGramStableRatio_nonneg
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    0 ≤ twoLocalPauliUnitaryCommutatorGramStableRatio U := by
  rw [twoLocalPauliUnitaryCommutatorGramStableRatio]
  exact div_nonneg (sq_nonneg _)
    (Finset.sum_nonneg fun i _ => by positivity)

/-- Target-adaptive genuine Gram theorem.  Stable rank is at least the exact
two-local Pauli incidence mass; this can scale quadratically even though its
worst-target trace-only corollary is merely linear. -/
theorem twoLocalPauliUnitaryCommutatorGramStableRatio_ge_incidenceMass
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    twoLocalPauliUnitaryAnticommutingIncidenceMass U ≤
      twoLocalPauliUnitaryCommutatorGramStableRatio U := by
  let incidence := twoLocalPauliUnitaryAnticommutingIncidenceMass U
  by_cases hincidence : incidence = 0
  · change incidence ≤ _
    rw [hincidence]
    exact twoLocalPauliUnitaryCommutatorGramStableRatio_nonneg U
  have hincidencePos : 0 < incidence :=
    lt_of_le_of_ne
      (twoLocalPauliUnitaryAnticommutingIncidenceMass_nonneg U)
      (Ne.symm hincidence)
  have hpowPos : 0 < (2 : ℝ) ^ n := by positivity
  have hmassPos : 0 < 4 * (2 : ℝ) ^ n * incidence := by positivity
  have hcapPos : 0 < 4 * (2 : ℝ) ^ n := by positivity
  have hnrank :
      Module.finrank ℝ (TwoLocalPauliCoefficientSpace n) =
        Fintype.card (PauliTracelessLabel n 2) := by
    exact finrank_euclideanSpace
  have hmass :
      4 * (2 : ℝ) ^ n * incidence ≤
        ∑ Q : PauliTracelessLabel n 2,
          ‖twoLocalPauliUnitaryCommutatorMap U
            ((EuclideanSpace.basisFun (PauliTracelessLabel n 2) ℝ) Q)‖ ^ (2 : ℕ) := by
    rw [← sum_sq_singularValues_eq_sum_norm_orthonormalBasis
      (twoLocalPauliUnitaryCommutatorMap U) hnrank
      (EuclideanSpace.basisFun (PauliTracelessLabel n 2) ℝ)]
    rw [sum_sq_twoLocalPauliUnitaryCommutator_singularValues_eq_incidenceMass]
  have hratio := singularStableRatio_ge_of_basis_trace_norm_cap
    (twoLocalPauliUnitaryCommutatorMap U) hnrank
    (EuclideanSpace.basisFun (PauliTracelessLabel n 2) ℝ)
    hmassPos hcapPos hmass
    (twoLocalPauliUnitaryCommutatorMap_norm_sq_le U)
  change incidence ≤ _
  rw [twoLocalPauliUnitaryCommutatorGramStableRatio]
  convert hratio using 1
  field_simp [ne_of_gt hpowPos]

theorem twoLocalPauliUnitaryCommutatorGramStableRatio_ge_boundaryMoment
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    twoLocalPauliUnitaryBoundaryMoment U ≤
      twoLocalPauliUnitaryCommutatorGramStableRatio U :=
  (twoLocalPauliUnitaryBoundaryMoment_le_incidenceMass U).trans
    (twoLocalPauliUnitaryCommutatorGramStableRatio_ge_incidenceMass U)

/-- Active-support genuine Gram theorem.  Pauli mass at weight `w` forces
stable rank at least `w(n-1)` times that mass, with no full-support exception. -/
theorem twoLocalPauliUnitaryCommutatorGramStableRatio_ge_activeWeightMoment
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    twoLocalPauliUnitaryActiveWeightMoment U ≤
      twoLocalPauliUnitaryCommutatorGramStableRatio U :=
  (twoLocalPauliUnitaryActiveWeightMoment_le_incidenceMass U).trans
    (twoLocalPauliUnitaryCommutatorGramStableRatio_ge_incidenceMass U)

/-- Enhanced active-support genuine Gram theorem.  Weight-`w` target mass
forces stable rank at least its `2wn` moment. -/
theorem twoLocalPauliUnitaryCommutatorGramStableRatio_ge_enhancedActiveWeightMoment
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    twoLocalPauliUnitaryEnhancedActiveWeightMoment U ≤
      twoLocalPauliUnitaryCommutatorGramStableRatio U :=
  (twoLocalPauliUnitaryEnhancedActiveWeightMoment_le_incidenceMass U).trans
    (twoLocalPauliUnitaryCommutatorGramStableRatio_ge_incidenceMass U)

/-- Full polynomial genuine Gram theorem.  Target mass at Pauli weight `w`
forces stable rank at least its `2w(3n-2w)` moment. -/
theorem twoLocalPauliUnitaryCommutatorGramStableRatio_ge_fullWeightPolynomialMoment
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    twoLocalPauliUnitaryFullWeightPolynomialMoment U ≤
      twoLocalPauliUnitaryCommutatorGramStableRatio U :=
  (twoLocalPauliUnitaryFullWeightPolynomialMoment_le_incidenceMass U).trans
    (twoLocalPauliUnitaryCommutatorGramStableRatio_ge_incidenceMass U)

theorem twoLocalPauliUnitaryAnticommutingIncidenceMass_ge_sixNSubFour_traceDeficit
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    ((6 * n - 4 : ℕ) : ℝ) *
        (1 - ‖pauliCoeff
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)
          pauliCharacterZero‖ ^ (2 : ℕ)) ≤
      twoLocalPauliUnitaryAnticommutingIncidenceMass U := by
  rw [← unitary_nonzero_pauliCoeff_mass_eq_traceDeficit U]
  simpa [twoLocalPauliUnitaryAnticommutingIncidenceMass] using
    total_pauliAnticommutingIncidenceMass_ge_sixNSubFour
      (n := n)
      (fun P : NonzeroPauliCharacter (Fin n) =>
        ‖pauliCoeff
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) P.1‖ ^ (2 : ℕ))
      (fun P => sq_nonneg _)

/-- Sharp worst-Pauli-sector genuine Gram theorem.  Every nonprojective
unitary target pays `6n-4` times its trace deficit; weight one is extremal. -/
theorem twoLocalPauliUnitaryCommutatorGramStableRatio_ge_sixNSubFour_traceDeficit
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    ((6 * n - 4 : ℕ) : ℝ) *
        (1 - ‖pauliCoeff
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)
          pauliCharacterZero‖ ^ (2 : ℕ)) ≤
      twoLocalPauliUnitaryCommutatorGramStableRatio U :=
  (twoLocalPauliUnitaryAnticommutingIncidenceMass_ge_sixNSubFour_traceDeficit U).trans
    (twoLocalPauliUnitaryCommutatorGramStableRatio_ge_incidenceMass U)

theorem twoLocalPauliUnitaryCommutatorGramStableRatio_ge_sixNSubFour_normalizedTraceDeficit
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    ((6 * n - 4 : ℕ) : ℝ) *
        (1 - ‖Matrix.trace
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
          ((2 : ℝ) ^ n) ^ (2 : ℕ)) ≤
      twoLocalPauliUnitaryCommutatorGramStableRatio U := by
  have htrace := norm_pauliScalarCoefficient_sq_eq_normalizedTrace
    (U : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)
  simp only [Fintype.card_fin] at htrace
  rw [← htrace]
  exact
    twoLocalPauliUnitaryCommutatorGramStableRatio_ge_sixNSubFour_traceDeficit U

/-- Genuine Gram stable-rank floor for the commutator response of the complete
ordinary two-local Pauli ensemble.  The floor is linear in qubit count and in
Hilbert--Schmidt distance from projective recurrence. -/
theorem twoLocalPauliUnitaryCommutatorGramStableRatio_ge_scalarDistance
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    ((n - 1 : ℕ) : ℝ) *
        frobSq
          ((U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) -
            pauliScalarPart
              (U : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ)) /
        (2 : ℝ) ^ n ≤
      twoLocalPauliUnitaryCommutatorGramStableRatio U := by
  let distance := frobSq
    ((U : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) -
      pauliScalarPart
        (U : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ))
  by_cases hdistance : distance = 0
  · change ((n - 1 : ℕ) : ℝ) * distance / (2 : ℝ) ^ n ≤ _
    rw [hdistance, mul_zero, zero_div]
    exact twoLocalPauliUnitaryCommutatorGramStableRatio_nonneg U
  by_cases hnsmall : n ≤ 1
  · have hz : n - 1 = 0 := by omega
    change ((n - 1 : ℕ) : ℝ) * distance / (2 : ℝ) ^ n ≤ _
    rw [hz, Nat.cast_zero, zero_mul, zero_div]
    exact twoLocalPauliUnitaryCommutatorGramStableRatio_nonneg U
  have hdistancePos : 0 < distance :=
    lt_of_le_of_ne (frobSq_nonneg _) (Ne.symm hdistance)
  have hnPos : 0 < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt (by omega : 1 < n))
  have hmassPos : 0 < 4 * ((n - 1 : ℕ) : ℝ) * distance := by
    positivity
  have hpowPos : 0 < (2 : ℝ) ^ n := by positivity
  have hcapPos : 0 < 4 * (2 : ℝ) ^ n := by positivity
  have hnrank :
      Module.finrank ℝ (TwoLocalPauliCoefficientSpace n) =
        Fintype.card (PauliTracelessLabel n 2) := by
    exact finrank_euclideanSpace
  have hmass :
      4 * ((n - 1 : ℕ) : ℝ) * distance ≤
        ∑ Q : PauliTracelessLabel n 2,
          ‖twoLocalPauliUnitaryCommutatorMap U
            ((EuclideanSpace.basisFun (PauliTracelessLabel n 2) ℝ) Q)‖ ^ (2 : ℕ) := by
    exact sum_basis_twoLocalPauliUnitaryCommutatorMap_norm_sq_ge U
  have hratio := singularStableRatio_ge_of_basis_trace_norm_cap
    (twoLocalPauliUnitaryCommutatorMap U) hnrank
    (EuclideanSpace.basisFun (PauliTracelessLabel n 2) ℝ)
    hmassPos hcapPos hmass
    (twoLocalPauliUnitaryCommutatorMap_norm_sq_le U)
  change ((n - 1 : ℕ) : ℝ) * distance / (2 : ℝ) ^ n ≤ _
  rw [twoLocalPauliUnitaryCommutatorGramStableRatio]
  convert hratio using 1
  field_simp [ne_of_gt hpowPos]

theorem twoLocalPauliUnitaryCommutatorGramStableRatio_ge_traceDeficit
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    ((n - 1 : ℕ) : ℝ) *
        (1 - ‖pauliCoeff
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)
          pauliCharacterZero‖ ^ (2 : ℕ)) ≤
      twoLocalPauliUnitaryCommutatorGramStableRatio U := by
  rw [← unitary_scalarDistance_ratio_eq_traceDeficit U,
    frobSq_unitaryGroup_finiteQubit U]
  simpa [mul_div_assoc] using
    twoLocalPauliUnitaryCommutatorGramStableRatio_ge_scalarDistance U

/-- Physical normalized-trace form of the genuine Gram theorem.  Every unitary
outside a projective-return tube forces dimension-linear anti-concentration for
the ordinary two-local Gaussian Hamiltonian ensemble. -/
theorem twoLocalPauliUnitaryCommutatorGramStableRatio_ge_normalizedTraceDeficit
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    ((n - 1 : ℕ) : ℝ) *
        (1 - ‖Matrix.trace
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
          ((2 : ℝ) ^ n) ^ (2 : ℕ)) ≤
      twoLocalPauliUnitaryCommutatorGramStableRatio U := by
  have htrace := norm_pauliScalarCoefficient_sq_eq_normalizedTrace
    (U : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)
  simp only [Fintype.card_fin] at htrace
  rw [← htrace]
  exact twoLocalPauliUnitaryCommutatorGramStableRatio_ge_traceDeficit U

/-- Explicit covariance-trace floor.  It removes singular values from the
activation threshold: only qubit count and projective trace deficit remain. -/
theorem sum_sq_twoLocalPauliUnitaryCommutator_singularValues_ge_traceDeficit
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    4 * ((n - 1 : ℕ) : ℝ) * (2 : ℝ) ^ n *
        (1 - ‖Matrix.trace
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
          ((2 : ℝ) ^ n) ^ (2 : ℕ)) ≤
      ∑ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
        (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ (2 : ℕ) := by
  have hnrank :
      Module.finrank ℝ (TwoLocalPauliCoefficientSpace n) =
        Fintype.card (PauliTracelessLabel n 2) := by
    exact finrank_euclideanSpace
  have htrace := norm_pauliScalarCoefficient_sq_eq_normalizedTrace
    (U : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ)
  simp only [Fintype.card_fin] at htrace
  have hdistance := unitary_scalarDistance_ratio_eq_traceDeficit U
  rw [frobSq_unitaryGroup_finiteQubit U, htrace] at hdistance
  have hpowPos : 0 < (2 : ℝ) ^ n := by positivity
  have hdistanceEq :
      frobSq
          ((U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) -
            pauliScalarPart
              (U : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ)) =
        (2 : ℝ) ^ n *
          (1 - ‖Matrix.trace
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
            ((2 : ℝ) ^ n) ^ (2 : ℕ)) := by
    field_simp [ne_of_gt hpowPos] at hdistance ⊢
    exact hdistance
  rw [sum_sq_singularValues_eq_sum_norm_orthonormalBasis
    (twoLocalPauliUnitaryCommutatorMap U) hnrank
    (EuclideanSpace.basisFun (PauliTracelessLabel n 2) ℝ)]
  calc
    4 * ((n - 1 : ℕ) : ℝ) * (2 : ℝ) ^ n *
          (1 - ‖Matrix.trace
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
            ((2 : ℝ) ^ n) ^ (2 : ℕ)) =
        4 * ((n - 1 : ℕ) : ℝ) *
          frobSq
            ((U : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ) -
              pauliScalarPart
                (U : Matrix (FiniteQubitConfiguration (Fin n))
                  (FiniteQubitConfiguration (Fin n)) ℂ)) := by
      rw [hdistanceEq]
      ring
    _ ≤ _ := sum_basis_twoLocalPauliUnitaryCommutatorMap_norm_sq_ge U

/-- Complete finite-family, return-removed centralizer anti-concentration law.
No common deficit premise is required: every target pays its own exact
normalized-trace deficit, and the complete family pays only the finite union. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_commutatorTube_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              ∑ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
                (twoLocalPauliUnitaryCommutatorMap (U c)).singularValues i ^ (2 : ℕ)}) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          (((n - 1 : ℕ) : ℝ) *
            (1 - ‖Matrix.trace
              (U c : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
              ((2 : ℝ) ^ n) ^ (2 : ℕ)))) := by
  have hnrank :
      Module.finrank ℝ (TwoLocalPauliCoefficientSpace n) =
        Fintype.card (PauliTracelessLabel n 2) := by
    exact finrank_euclideanSpace
  calc
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              ∑ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
                (twoLocalPauliUnitaryCommutatorMap (U c)).singularValues i ^ (2 : ℕ)}) ≤
      ∑ c, (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              ∑ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
                (twoLocalPauliUnitaryCommutatorMap (U c)).singularValues i ^ (2 : ℕ)} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          (((n - 1 : ℕ) : ℝ) *
            (1 - ‖Matrix.trace
              (U c : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
              ((2 : ℝ) ^ n) ^ (2 : ℕ)))) := by
      apply Finset.sum_le_sum
      intro c _
      refine (stdGaussian_measure_linearMap_norm_sq_le_halfActivation
        (twoLocalPauliUnitaryCommutatorMap (U c)) hnrank).trans ?_
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left
        (twoLocalPauliUnitaryCommutatorGramStableRatio_ge_normalizedTraceDeficit
          (U c))
        (neg_nonpos.mpr (by positivity))

/-- Target-adaptive finite-family law.  Each circuit pays its exact Pauli
incidence mass in both activation scale and exponent.  For extensively spread
targets this improves the trace-only linear exponent to the quadratic number
of ordinary two-local directions. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_incidenceCommutatorTube_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryAnticommutingIncidenceMass (U c))}) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryAnticommutingIncidenceMass (U c)) := by
  have hnrank :
      Module.finrank ℝ (TwoLocalPauliCoefficientSpace n) =
        Fintype.card (PauliTracelessLabel n 2) := by
    exact finrank_euclideanSpace
  calc
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryAnticommutingIncidenceMass (U c))}) ≤
      ∑ c, (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryAnticommutingIncidenceMass (U c))} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryAnticommutingIncidenceMass (U c)) := by
      apply Finset.sum_le_sum
      intro c _
      have hsingle := stdGaussian_measure_linearMap_norm_sq_le_halfActivation
        (twoLocalPauliUnitaryCommutatorMap (U c)) hnrank
      rw [sum_sq_twoLocalPauliUnitaryCommutator_singularValues_eq_incidenceMass]
        at hsingle
      refine hsingle.trans ?_
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left
        (by simpa [twoLocalPauliUnitaryCommutatorGramStableRatio,
            sum_sq_twoLocalPauliUnitaryCommutator_singularValues_eq_incidenceMass]
          using
            twoLocalPauliUnitaryCommutatorGramStableRatio_ge_incidenceMass
              (U c))
        (neg_nonpos.mpr (by positivity))

/-- Support-isoperimetric finite-family corollary.  It exposes a quadratic
`w(n-w)` exponent directly from target Pauli-weight distribution. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_boundaryCommutatorTube_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryBoundaryMoment (U c))}) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryBoundaryMoment (U c)) := by
  calc
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryBoundaryMoment (U c))}) ≤
      (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryAnticommutingIncidenceMass (U c))}) := by
      refine measureReal_mono ?_ (by finiteness)
      intro x hx
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
      obtain ⟨c, hc⟩ := hx
      refine ⟨c, hc.trans ?_⟩
      apply mul_le_mul_of_nonneg_left _
        (by linarith [gaussianIntervalActivationMass_pos])
      exact mul_le_mul_of_nonneg_left
        (twoLocalPauliUnitaryBoundaryMoment_le_incidenceMass (U c))
        (by positivity)
    _ ≤ ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryAnticommutingIncidenceMass (U c)) :=
      stdGaussian_twoLocalPauli_measure_iUnion_incidenceCommutatorTube_le U
    _ ≤ ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryBoundaryMoment (U c)) := by
      apply Finset.sum_le_sum
      intro c _
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left
        (twoLocalPauliUnitaryBoundaryMoment_le_incidenceMass (U c))
        (neg_nonpos.mpr (by positivity))

/-- Active-support finite-family law.  Weight-`w` Pauli mass pays the
nonvanishing `w(n-1)` exponent, including targets with full Pauli support. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_activeWeightCommutatorTube_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryActiveWeightMoment (U c))}) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryActiveWeightMoment (U c)) := by
  calc
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryActiveWeightMoment (U c))}) ≤
      (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryAnticommutingIncidenceMass (U c))}) := by
      refine measureReal_mono ?_ (by finiteness)
      intro x hx
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
      obtain ⟨c, hc⟩ := hx
      refine ⟨c, hc.trans ?_⟩
      apply mul_le_mul_of_nonneg_left _
        (by linarith [gaussianIntervalActivationMass_pos])
      exact mul_le_mul_of_nonneg_left
        (twoLocalPauliUnitaryActiveWeightMoment_le_incidenceMass (U c))
        (by positivity)
    _ ≤ ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryAnticommutingIncidenceMass (U c)) :=
      stdGaussian_twoLocalPauli_measure_iUnion_incidenceCommutatorTube_le U
    _ ≤ ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryActiveWeightMoment (U c)) := by
      apply Finset.sum_le_sum
      intro c _
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left
        (twoLocalPauliUnitaryActiveWeightMoment_le_incidenceMass (U c))
        (neg_nonpos.mpr (by positivity))

/-- Enhanced active-support finite-family law.  Weight-`w` target mass pays
the explicit `2wn` incidence exponent. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_enhancedActiveWeightCommutatorTube_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryEnhancedActiveWeightMoment (U c))}) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryEnhancedActiveWeightMoment (U c)) := by
  calc
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryEnhancedActiveWeightMoment (U c))}) ≤
      (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryAnticommutingIncidenceMass (U c))}) := by
      refine measureReal_mono ?_ (by finiteness)
      intro x hx
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
      obtain ⟨c, hc⟩ := hx
      refine ⟨c, hc.trans ?_⟩
      apply mul_le_mul_of_nonneg_left _
        (by linarith [gaussianIntervalActivationMass_pos])
      exact mul_le_mul_of_nonneg_left
        (twoLocalPauliUnitaryEnhancedActiveWeightMoment_le_incidenceMass (U c))
        (by positivity)
    _ ≤ ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryAnticommutingIncidenceMass (U c)) :=
      stdGaussian_twoLocalPauli_measure_iUnion_incidenceCommutatorTube_le U
    _ ≤ ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryEnhancedActiveWeightMoment (U c)) := by
      apply Finset.sum_le_sum
      intro c _
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left
        (twoLocalPauliUnitaryEnhancedActiveWeightMoment_le_incidenceMass (U c))
        (neg_nonpos.mpr (by positivity))

/-- Full Pauli-weight finite-family law.  Each target pays its explicit
`2w(3n-2w)`-weighted Pauli mass in both tube scale and exponent. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_fullWeightPolynomialCommutatorTube_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryFullWeightPolynomialMoment (U c))}) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryFullWeightPolynomialMoment (U c)) := by
  calc
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryFullWeightPolynomialMoment (U c))}) ≤
      (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryAnticommutingIncidenceMass (U c))}) := by
      refine measureReal_mono ?_ (by finiteness)
      intro x hx
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
      obtain ⟨c, hc⟩ := hx
      refine ⟨c, hc.trans ?_⟩
      apply mul_le_mul_of_nonneg_left _
        (by linarith [gaussianIntervalActivationMass_pos])
      exact mul_le_mul_of_nonneg_left
        (twoLocalPauliUnitaryFullWeightPolynomialMoment_le_incidenceMass (U c))
        (by positivity)
    _ ≤ ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryAnticommutingIncidenceMass (U c)) :=
      stdGaussian_twoLocalPauli_measure_iUnion_incidenceCommutatorTube_le U
    _ ≤ ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryFullWeightPolynomialMoment (U c)) := by
      apply Finset.sum_le_sum
      intro c _
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left
        (twoLocalPauliUnitaryFullWeightPolynomialMoment_le_incidenceMass (U c))
        (neg_nonpos.mpr (by positivity))

/-- Sharp worst-target finite-family law.  Every nonprojective target pays
`6n-4` times normalized trace deficit, while target-specific Pauli weight can
only improve this exponent. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_sixNSubFourCommutatorTube_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                (((6 * n - 4 : ℕ) : ℝ) *
                  (1 - ‖Matrix.trace
                    (U c : Matrix (FiniteQubitConfiguration (Fin n))
                      (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
                    ((2 : ℝ) ^ n) ^ (2 : ℕ))))}) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          (((6 * n - 4 : ℕ) : ℝ) *
            (1 - ‖Matrix.trace
              (U c : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
              ((2 : ℝ) ^ n) ^ (2 : ℕ)))) := by
  calc
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                (((6 * n - 4 : ℕ) : ℝ) *
                  (1 - ‖Matrix.trace
                    (U c : Matrix (FiniteQubitConfiguration (Fin n))
                      (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
                    ((2 : ℝ) ^ n) ^ (2 : ℕ))))}) ≤
      (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                twoLocalPauliUnitaryAnticommutingIncidenceMass (U c))}) := by
      refine measureReal_mono ?_ (by finiteness)
      intro x hx
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
      obtain ⟨c, hc⟩ := hx
      refine ⟨c, hc.trans ?_⟩
      apply mul_le_mul_of_nonneg_left _
        (by linarith [gaussianIntervalActivationMass_pos])
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have htrace := norm_pauliScalarCoefficient_sq_eq_normalizedTrace
        (U c : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)
      simp only [Fintype.card_fin] at htrace
      rw [← htrace]
      exact
        twoLocalPauliUnitaryAnticommutingIncidenceMass_ge_sixNSubFour_traceDeficit
          (U c)
    _ ≤ ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryAnticommutingIncidenceMass (U c)) :=
      stdGaussian_twoLocalPauli_measure_iUnion_incidenceCommutatorTube_le U
    _ ≤ ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          (((6 * n - 4 : ℕ) : ℝ) *
            (1 - ‖Matrix.trace
              (U c : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
              ((2 : ℝ) ^ n) ^ (2 : ℕ)))) := by
      apply Finset.sum_le_sum
      intro c _
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr (by positivity))
      have hinc :=
        twoLocalPauliUnitaryAnticommutingIncidenceMass_ge_sixNSubFour_traceDeficit
          (U c)
      have htrace := norm_pauliScalarCoefficient_sq_eq_normalizedTrace
        (U c : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)
      simp only [Fintype.card_fin] at htrace
      rw [htrace] at hinc
      exact hinc

/-- Fully explicit finite-circuit union law.  Both activation radius and
exponential penalty are expressed only through qubit count and each target's
normalized-trace deficit; no hidden singular-value or spectral-gap input
remains. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_explicitCommutatorTube_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ c, {x |
          ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * ((n - 1 : ℕ) : ℝ) * (2 : ℝ) ^ n *
                (1 - ‖Matrix.trace
                  (U c : Matrix (FiniteQubitConfiguration (Fin n))
                    (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
                  ((2 : ℝ) ^ n) ^ (2 : ℕ)))}) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          (((n - 1 : ℕ) : ℝ) *
            (1 - ‖Matrix.trace
              (U c : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) /
              ((2 : ℝ) ^ n) ^ (2 : ℕ)))) := by
  apply (measureReal_mono ?_).trans
    (stdGaussian_twoLocalPauli_measure_iUnion_commutatorTube_le U)
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
  obtain ⟨c, hc⟩ := hx
  refine ⟨c, hc.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (sum_sq_twoLocalPauliUnitaryCommutator_singularValues_ge_traceDeficit
      (U c))
    (by linarith [gaussianIntervalActivationMass_pos])

end

end GaloisForLFunctions.HTGeometry
