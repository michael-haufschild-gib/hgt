import GaloisForLFunctions.HTGeometry.TwoReplicaPauliHallSymmetryReduction
import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Designs.QubitTwoDesign
import Mathlib.LinearAlgebra.Projection

/-!
# Clifford-twirl reduction of the two-replica Hall obstruction

The exact single-qubit Clifford lift normalizes the three collective Pauli
commutators.  Consequently the canonical greatest Hall obstruction is fixed
by every doubled Clifford conjugation.  Averaging those conjugations gives an
idempotent whose range is exactly the identity/swap algebra.  Every canonical
obstruction therefore splits into its identity/swap part and its zero-twirl
part.

This is an algebraic finite-group argument.  It does not infer fourth-moment
control from doubled-commutant completeness and uses no differentiation.
-/

open scoped BigOperators Matrix Kronecker
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open QuantumAlg

abbrev CliffordTwoReplicaIndex := Fin 2 × Fin 2
abbrev CliffordTwoReplicaMatrix :=
  Matrix CliffordTwoReplicaIndex CliffordTwoReplicaIndex ℂ

/-- The raw Pauli axes in the same `Fin 3` order as the Hall family. -/
def cliffordQubitPauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![pauliX, pauliY, pauliZ]

/-- Positive quarter-turn Clifford codes about the `X`, `Y`, and `Z` axes.
The reversed quaternion-coordinate order matches the Pauli order above. -/
def cliffordQuarterTurnCode : Fin 3 → QubitTwoDesign.BinaryOctahedral :=
  ![.edge 2 false false, .edge 1 false false, .edge 0 false false]

/-- The strict Clifford lift of an axis quarter-turn is exactly
`2⁻¹/² (I + iP)`. -/
theorem cliffordQuarterTurn_matrix (a : Fin 3) :
    QubitTwoDesign.qubitClifford (cliffordQuarterTurnCode a) =
      rt2inv • ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
        Complex.I • cliffordQubitPauli a) := by
  have hsq : ((Real.sqrt 2 : ℂ) ^ (2 : ℕ)) = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  fin_cases a <;>
    first
    | change QubitTwoDesign.qubitClifford (.edge 2 false false) =
        rt2inv • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + Complex.I • pauliX)
    | change QubitTwoDesign.qubitClifford (.edge 1 false false) =
        rt2inv • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + Complex.I • pauliY)
    | change QubitTwoDesign.qubitClifford (.edge 0 false false) =
        rt2inv • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + Complex.I • pauliZ)
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
    simp_all [QubitTwoDesign.qubitClifford,
      QubitTwoDesign.binaryOctahedralQuaternion, QubitTwoDesign.sqrtTwoHalf,
      QubitTwoDesign.signed, QubitTwoDesign.coordinatePair,
      QubitTwoDesign.quaternionBasis, QubitTwoDesign.realQuaternion,
      QubitTwoDesign.sqrtTwoEval_apply, QubitTwoDesign.quaternionMatrix,
      pauliX, pauliY, pauliZ, rt2inv,
      Matrix.smul_apply, Fin.isValue, of_apply, cons_val, cons_val',
      cons_val_fin_one, cons_val_zero, cons_val_one] <;>
    field_simp <;>
    ring_nf <;>
    simp [hsq] <;>
    ring

/-- The Pauli acting identically on both replicas. -/
def cliffordTwoReplicaPauliPair (a : Fin 3) : CliffordTwoReplicaMatrix :=
  cliffordQubitPauli a ⊗ₖ cliffordQubitPauli a

theorem cliffordQubitPauli_mem_signedRawPauliSet (a : Fin 3) :
    cliffordQubitPauli a ∈ QubitTwoDesign.signedRawPauliSet := by
  fin_cases a <;>
    simp [cliffordQubitPauli, QubitTwoDesign.signedRawPauliSet]

theorem exists_cliffordQubitPauli_sign_of_mem_signedRawPauliSet
    {P : Matrix (Fin 2) (Fin 2) ℂ}
    (hP : P ∈ QubitTwoDesign.signedRawPauliSet) :
    ∃ a : Fin 3, P = cliffordQubitPauli a ∨ P = -cliffordQubitPauli a := by
  change P = pauliX ∨ P = -pauliX ∨ P = pauliY ∨ P = -pauliY ∨
    P = pauliZ ∨ P = -pauliZ at hP
  rcases hP with hP | hP | hP | hP | hP | hP
  · exact ⟨0, Or.inl (by simpa [cliffordQubitPauli] using hP)⟩
  · exact ⟨0, Or.inr (by simpa [cliffordQubitPauli] using hP)⟩
  · exact ⟨1, Or.inl (by simpa [cliffordQubitPauli] using hP)⟩
  · exact ⟨1, Or.inr (by simpa [cliffordQubitPauli] using hP)⟩
  · exact ⟨2, Or.inl (by simpa [cliffordQubitPauli] using hP)⟩
  · exact ⟨2, Or.inr (by simpa [cliffordQubitPauli] using hP)⟩

/-- The diagonal two-replica Pauli Hamiltonian on one physical qubit. -/
def cliffordTwoReplicaCollectivePauli (a : Fin 3) :
    CliffordTwoReplicaMatrix :=
  cliffordQubitPauli a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ cliffordQubitPauli a

/-- The three collective commutators in the `Fin 2` Clifford convention. -/
def cliffordTwoReplicaCollectiveCommutatorLinear (a : Fin 3) :
    CliffordTwoReplicaMatrix →ₗ[ℂ] CliffordTwoReplicaMatrix where
  toFun X := ringCommutator (cliffordTwoReplicaCollectivePauli a) X
  map_add' X Y := by
    simp [ringCommutator, Matrix.mul_add, Matrix.add_mul]
    module
  map_smul' c X := by
    simp [ringCommutator]
    module

/-- Conjugation by a square unitary matrix, as a linear equivalence. -/
def unitaryMatrixConjugationEquiv
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G : Matrix κ κ ℂ) (hunit : Gᴴ * G = 1) :
    Matrix κ κ ℂ ≃ₗ[ℂ] Matrix κ κ ℂ where
  toLinearMap :=
    { toFun := fun X => G * X * Gᴴ
      map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c X; simp }
  invFun := fun X => Gᴴ * X * G
  left_inv X := by
    change Gᴴ * (G * X * Gᴴ) * G = X
    calc
      Gᴴ * (G * X * Gᴴ) * G = (Gᴴ * G) * X * (Gᴴ * G) := by
        noncomm_ring
      _ = X := by rw [hunit]; simp
  right_inv X := by
    have hunit' : G * Gᴴ = 1 := mul_eq_one_comm.mp hunit
    change G * (Gᴴ * X * G) * Gᴴ = X
    calc
      G * (Gᴴ * X * G) * Gᴴ = (G * Gᴴ) * X * (G * Gᴴ) := by
        noncomm_ring
      _ = X := by rw [hunit']; simp

/-- Doubled Clifford conjugation on the two-replica operator space. -/
def cliffordDoubledConjugationEquiv
    (g : QubitTwoDesign.BinaryOctahedral) :
    CliffordTwoReplicaMatrix ≃ₗ[ℂ] CliffordTwoReplicaMatrix :=
  unitaryMatrixConjugationEquiv
    (doubledRep QubitTwoDesign.qubitClifford g)
    (doubledRep_unit QubitTwoDesign.qubitClifford
      QubitTwoDesign.qubitClifford_unitary g)

@[simp] theorem cliffordDoubledConjugationEquiv_apply
    (g : QubitTwoDesign.BinaryOctahedral) (X : CliffordTwoReplicaMatrix) :
    cliffordDoubledConjugationEquiv g X =
      doubledRep QubitTwoDesign.qubitClifford g * X *
        (doubledRep QubitTwoDesign.qubitClifford g)ᴴ := rfl

@[simp] theorem cliffordDoubledConjugationEquiv_symm_apply
    (g : QubitTwoDesign.BinaryOctahedral) (X : CliffordTwoReplicaMatrix) :
    (cliffordDoubledConjugationEquiv g).symm X =
      (doubledRep QubitTwoDesign.qubitClifford g)ᴴ * X *
        doubledRep QubitTwoDesign.qubitClifford g := rfl

theorem cliffordDoubledConjugationEquiv_symm_eq
    (g : QubitTwoDesign.BinaryOctahedral) :
    (cliffordDoubledConjugationEquiv g).symm =
      cliffordDoubledConjugationEquiv g⁻¹ := by
  apply LinearEquiv.ext
  intro X
  change (doubledRep QubitTwoDesign.qubitClifford g)ᴴ * X *
      doubledRep QubitTwoDesign.qubitClifford g =
    doubledRep QubitTwoDesign.qubitClifford g⁻¹ * X *
      (doubledRep QubitTwoDesign.qubitClifford g⁻¹)ᴴ
  rw [← doubledRep_conjTranspose_eq_inv
      QubitTwoDesign.qubitClifford QubitTwoDesign.qubitClifford_mul
        QubitTwoDesign.qubitClifford_unitary g]
  simp

set_option maxHeartbeats 4000000 in
/-- Exact finite-group interpolation of the collective Casimir.

For each Pauli axis, the square of the collective commutator is a group-ring
combination of identity, the two inverse quarter-turn conjugations, and the
paired half-turn conjugation.  Thus no infinitesimal closure or fourth moment
is needed to recover Casimir invariance from finite Clifford invariance. -/
theorem cliffordTwoReplicaCollectiveCommutator_square_groupAlgebra
    (a : Fin 3) (X : CliffordTwoReplicaMatrix) :
    cliffordTwoReplicaCollectiveCommutatorLinear a
        (cliffordTwoReplicaCollectiveCommutatorLinear a X) =
      (6 : ℂ) • X - (4 : ℂ) •
        (cliffordDoubledConjugationEquiv (cliffordQuarterTurnCode a) X +
          (cliffordDoubledConjugationEquiv
            (cliffordQuarterTurnCode a)).symm X) +
        (2 : ℂ) •
          (cliffordTwoReplicaPauliPair a * X *
            cliffordTwoReplicaPauliPair a) := by
  rw [cliffordDoubledConjugationEquiv_apply,
    cliffordDoubledConjugationEquiv_symm_apply]
  rw [QuantumAlg.doubledRep, cliffordQuarterTurn_matrix]
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_smul,
    rt2inv_conj]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases a <;> fin_cases i₁ <;> fin_cases i₂ <;>
    fin_cases j₁ <;> fin_cases j₂ <;>
    simp [cliffordTwoReplicaCollectiveCommutatorLinear,
      cliffordTwoReplicaCollectivePauli, cliffordQubitPauli,
      cliffordTwoReplicaPauliPair, ringCommutator,
      pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.one_apply,
      Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply] <;>
    ring_nf <;>
    simp [Complex.I_sq,
      show rt2inv ^ (4 : ℕ) = (1 / 4 : ℂ) by
        rw [show rt2inv ^ (4 : ℕ) =
          (rt2inv * rt2inv) * (rt2inv * rt2inv) by ring,
          rt2inv_mul_self]
        norm_num] <;>
    ring

/-- Commutators are natural under arbitrary unitary conjugation. -/
theorem ringCommutator_unitary_conjugation
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G P X : Matrix κ κ ℂ) (hunit : Gᴴ * G = 1) :
    G * ringCommutator P (Gᴴ * X * G) * Gᴴ =
      ringCommutator (G * P * Gᴴ) X := by
  have hunit' : G * Gᴴ = 1 := mul_eq_one_comm.mp hunit
  unfold ringCommutator
  calc
    G * (P * (Gᴴ * X * G) - (Gᴴ * X * G) * P) * Gᴴ =
        (G * P * Gᴴ) * X * (G * Gᴴ) -
          (G * Gᴴ) * X * (G * P * Gᴴ) := by
      noncomm_ring
    _ = (G * P * Gᴴ) * X - X * (G * P * Gᴴ) := by
      rw [hunit']
      simp

theorem ringCommutator_add_left'
    {A : Type*} [Ring A] (p q x : A) :
    ringCommutator (p + q) x =
      ringCommutator p x + ringCommutator q x := by
  unfold ringCommutator
  noncomm_ring

/-- A doubled Clifford gate sends each collective Pauli Hamiltonian to a
signed member of the same three-axis family. -/
theorem cliffordDoubled_conj_collectivePauli
    (g : QubitTwoDesign.BinaryOctahedral) (a : Fin 3) :
    ∃ b : Fin 3,
      doubledRep QubitTwoDesign.qubitClifford g *
          cliffordTwoReplicaCollectivePauli a *
            (doubledRep QubitTwoDesign.qubitClifford g)ᴴ =
          cliffordTwoReplicaCollectivePauli b ∨
      doubledRep QubitTwoDesign.qubitClifford g *
          cliffordTwoReplicaCollectivePauli a *
            (doubledRep QubitTwoDesign.qubitClifford g)ᴴ =
          -cliffordTwoReplicaCollectivePauli b := by
  let C := QubitTwoDesign.qubitClifford g
  let P := cliffordQubitPauli a
  have hunit : Cᴴ * C = 1 := QubitTwoDesign.qubitClifford_unitary g
  have hunit' : C * Cᴴ = 1 := mul_eq_one_comm.mp hunit
  have hP : C * P * Cᴴ ∈ QubitTwoDesign.signedRawPauliSet :=
    QubitTwoDesign.qubitClifford_conj_pauli_mem g
      (cliffordQubitPauli_mem_signedRawPauliSet a)
  obtain ⟨b, hb | hb⟩ :=
    exists_cliffordQubitPauli_sign_of_mem_signedRawPauliSet hP
  · refine ⟨b, Or.inl ?_⟩
    change (C ⊗ₖ C) *
        (P ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + 1 ⊗ₖ P) *
          (C ⊗ₖ C)ᴴ = _
    rw [Matrix.conjTranspose_kronecker, Matrix.mul_add, Matrix.add_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, hunit', hb]
    simp [cliffordTwoReplicaCollectivePauli]
  · refine ⟨b, Or.inr ?_⟩
    change (C ⊗ₖ C) *
        (P ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + 1 ⊗ₖ P) *
          (C ⊗ₖ C)ᴴ = _
    rw [Matrix.conjTranspose_kronecker, Matrix.mul_add, Matrix.add_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, hunit', hb]
    ext i j
    simp [cliffordTwoReplicaCollectivePauli]
    ring

/-- Operator-span covariance of the collective commutator family under one
doubled Clifford conjugation. -/
theorem cliffordDoubled_conjugatedCollectiveCommutator_mem_span
    (a : Fin 3) (g : QubitTwoDesign.BinaryOctahedral) :
    (((cliffordDoubledConjugationEquiv g :
        CliffordTwoReplicaMatrix →ₗ[ℂ] CliffordTwoReplicaMatrix).comp
      (cliffordTwoReplicaCollectiveCommutatorLinear a)).comp
      ((cliffordDoubledConjugationEquiv g).symm :
        CliffordTwoReplicaMatrix →ₗ[ℂ] CliffordTwoReplicaMatrix)) ∈
      linearFamilyOperatorSpan
        cliffordTwoReplicaCollectiveCommutatorLinear := by
  obtain ⟨b, hb | hb⟩ := cliffordDoubled_conj_collectivePauli g a
  · have heq :
        (((cliffordDoubledConjugationEquiv g :
            CliffordTwoReplicaMatrix →ₗ[ℂ] CliffordTwoReplicaMatrix).comp
          (cliffordTwoReplicaCollectiveCommutatorLinear a)).comp
          ((cliffordDoubledConjugationEquiv g).symm :
            CliffordTwoReplicaMatrix →ₗ[ℂ] CliffordTwoReplicaMatrix)) =
          cliffordTwoReplicaCollectiveCommutatorLinear b := by
      apply LinearMap.ext
      intro X
      change doubledRep QubitTwoDesign.qubitClifford g *
          ringCommutator (cliffordTwoReplicaCollectivePauli a)
            ((doubledRep QubitTwoDesign.qubitClifford g)ᴴ * X *
              doubledRep QubitTwoDesign.qubitClifford g) *
            (doubledRep QubitTwoDesign.qubitClifford g)ᴴ = _
      rw [ringCommutator_unitary_conjugation _ _ _
          (doubledRep_unit QubitTwoDesign.qubitClifford
            QubitTwoDesign.qubitClifford_unitary g), hb]
      rfl
    rw [heq]
    exact Submodule.subset_span ⟨b, rfl⟩
  · have heq :
        (((cliffordDoubledConjugationEquiv g :
            CliffordTwoReplicaMatrix →ₗ[ℂ] CliffordTwoReplicaMatrix).comp
          (cliffordTwoReplicaCollectiveCommutatorLinear a)).comp
          ((cliffordDoubledConjugationEquiv g).symm :
            CliffordTwoReplicaMatrix →ₗ[ℂ] CliffordTwoReplicaMatrix)) =
          -cliffordTwoReplicaCollectiveCommutatorLinear b := by
      apply LinearMap.ext
      intro X
      change doubledRep QubitTwoDesign.qubitClifford g *
          ringCommutator (cliffordTwoReplicaCollectivePauli a)
            ((doubledRep QubitTwoDesign.qubitClifford g)ᴴ * X *
              doubledRep QubitTwoDesign.qubitClifford g) *
            (doubledRep QubitTwoDesign.qubitClifford g)ᴴ = _
      rw [ringCommutator_unitary_conjugation _ _ _
          (doubledRep_unit QubitTwoDesign.qubitClifford
            QubitTwoDesign.qubitClifford_unitary g), hb,
        ringCommutator_neg_left]
      rfl
    rw [heq]
    exact (linearFamilyOperatorSpan
      cliffordTwoReplicaCollectiveCommutatorLinear).neg_mem
        (Submodule.subset_span ⟨b, rfl⟩)

/-- The canonical greatest local Hall obstruction is fixed by every doubled
Clifford conjugation. -/
theorem cliffordTwoReplicaCollectiveCommutator_greatestMaximizer_fixed
    (U : Submodule ℂ CliffordTwoReplicaMatrix)
    (hgreatest : ∀ V : Submodule ℂ CliffordTwoReplicaMatrix,
      linearFamilyDefect cliffordTwoReplicaCollectiveCommutatorLinear V =
        linearFamilyDefect cliffordTwoReplicaCollectiveCommutatorLinear U →
      V ≤ U)
    (g : QubitTwoDesign.BinaryOctahedral) :
    U.map (cliffordDoubledConjugationEquiv g :
      CliffordTwoReplicaMatrix →ₗ[ℂ] CliffordTwoReplicaMatrix) = U := by
  apply linearFamilyDefect_greatestMaximizer_map_eq_of_spanCovariant
      cliffordTwoReplicaCollectiveCommutatorLinear U
      (cliffordDoubledConjugationEquiv g)
      (cliffordDoubledConjugationEquiv g) hgreatest
  · exact fun a =>
      cliffordDoubled_conjugatedCollectiveCommutator_mem_span a g
  · intro a
    rw [cliffordDoubledConjugationEquiv_symm_eq]
    simpa [cliffordDoubledConjugationEquiv_symm_eq] using
      cliffordDoubled_conjugatedCollectiveCommutator_mem_span a g⁻¹

/-- The doubled Clifford twirl, packaged as a linear endomorphism. -/
def cliffordTwoReplicaTwirlLinear :
    CliffordTwoReplicaMatrix →ₗ[ℂ] CliffordTwoReplicaMatrix where
  toFun X := twirl2 QubitTwoDesign.qubitClifford X
  map_add' X Y := by
    simp [twirl2, repTwirl, Matrix.mul_add, Matrix.add_mul,
      Finset.sum_add_distrib]
  map_smul' c X := by
    simp [twirl2_smul]

/-- The exact doubled Clifford average fixes every operator in the doubled
Clifford commutant. -/
theorem qubitClifford_twirl_eq_self_of_commute
    (X : CliffordTwoReplicaMatrix)
    (hX : ∀ g, doubledRep QubitTwoDesign.qubitClifford g * X =
      X * doubledRep QubitTwoDesign.qubitClifford g) :
    twirl2 QubitTwoDesign.qubitClifford X = X := by
  haveI : Nonempty QubitTwoDesign.BinaryOctahedral := ⟨1⟩
  have hcard :
      (Fintype.card QubitTwoDesign.BinaryOctahedral : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hterm : ∀ g : QubitTwoDesign.BinaryOctahedral,
      doubledRep QubitTwoDesign.qubitClifford g * X *
          (doubledRep QubitTwoDesign.qubitClifford g)ᴴ = X := by
    intro g
    rw [hX g, Matrix.mul_assoc,
      doubledRep_unit' QubitTwoDesign.qubitClifford
        QubitTwoDesign.qubitClifford_unitary g,
      Matrix.mul_one]
  rw [twirl2, repTwirl,
    Finset.sum_congr rfl (fun g _ => hterm g),
    Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

/-- The range of the doubled Clifford twirl is exactly the two-dimensional
identity/swap algebra. -/
theorem cliffordTwoReplicaTwirlLinear_range_eq :
    LinearMap.range cliffordTwoReplicaTwirlLinear =
      Submodule.span ℂ
        ({(1 : CliffordTwoReplicaMatrix), QubitTwoDesign.qubitSwap} :
          Set CliffordTwoReplicaMatrix) := by
  apply le_antisymm
  · rintro Y ⟨X, rfl⟩
    change twirl2 QubitTwoDesign.qubitClifford X ∈ _
    have hnormal := QubitTwoDesign.qubitClifford_commutant_normal_form
      (twirl2 QubitTwoDesign.qubitClifford X)
      (fun g => twirl2_commute QubitTwoDesign.qubitClifford
        QubitTwoDesign.qubitClifford_mul
        QubitTwoDesign.qubitClifford_unitary X g)
    rw [hnormal]
    exact (Submodule.span ℂ
      ({(1 : CliffordTwoReplicaMatrix), QubitTwoDesign.qubitSwap} :
        Set CliffordTwoReplicaMatrix)).add_mem
      ((Submodule.span ℂ _).smul_mem _
        (Submodule.subset_span (by simp)))
      ((Submodule.span ℂ _).smul_mem _
        (Submodule.subset_span (by simp)))
  · rw [Submodule.span_le]
    intro X hX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl
    · refine ⟨1, ?_⟩
      exact qubitClifford_twirl_eq_self_of_commute 1 (by simp)
    · refine ⟨QubitTwoDesign.qubitSwap, ?_⟩
      exact qubitClifford_twirl_eq_self_of_commute
        QubitTwoDesign.qubitSwap
        (fun g => by
          simpa [doubledRep] using
            QubitTwoDesign.kronecker_self_commute_qubitSwap
              (QubitTwoDesign.qubitClifford g))

theorem cliffordTwoReplicaTwirlLinear_idempotent :
    ∀ X, cliffordTwoReplicaTwirlLinear
      (cliffordTwoReplicaTwirlLinear X) =
        cliffordTwoReplicaTwirlLinear X := by
  intro X
  exact twirl2_idem QubitTwoDesign.qubitClifford
    QubitTwoDesign.qubitClifford_mul X

/-- Every subspace preserved by an idempotent splits into its range and kernel
parts. -/
theorem invariantSubspace_eq_rangeKernel_split
    {𝕜 X : Type*} [Field 𝕜] [AddCommGroup X] [Module 𝕜 X]
    (P : X →ₗ[𝕜] X) (hP : ∀ x, P (P x) = P x)
    (U : Submodule 𝕜 X) (hU : ∀ x ∈ U, P x ∈ U) :
    U = (U ⊓ LinearMap.range P) ⊔ (U ⊓ LinearMap.ker P) := by
  apply le_antisymm
  · intro x hx
    refine Submodule.mem_sup.mpr ⟨P x, ⟨hU x hx, ⟨x, rfl⟩⟩,
      x - P x, ⟨U.sub_mem hx (hU x hx), ?_⟩, by abel⟩
    change P (x - P x) = 0
    rw [map_sub, hP, sub_self]
  · exact sup_le inf_le_left inf_le_left

/-- Clifford averaging preserves the canonical greatest Hall obstruction. -/
theorem cliffordTwoReplicaTwirlLinear_mem_greatestMaximizer
    (U : Submodule ℂ CliffordTwoReplicaMatrix)
    (hgreatest : ∀ V : Submodule ℂ CliffordTwoReplicaMatrix,
      linearFamilyDefect cliffordTwoReplicaCollectiveCommutatorLinear V =
        linearFamilyDefect cliffordTwoReplicaCollectiveCommutatorLinear U →
      V ≤ U)
    {X : CliffordTwoReplicaMatrix} (hX : X ∈ U) :
    cliffordTwoReplicaTwirlLinear X ∈ U := by
  have hterm : ∀ g : QubitTwoDesign.BinaryOctahedral,
      doubledRep QubitTwoDesign.qubitClifford g * X *
          (doubledRep QubitTwoDesign.qubitClifford g)ᴴ ∈ U := by
    intro g
    have hm : cliffordDoubledConjugationEquiv g X ∈
        U.map (cliffordDoubledConjugationEquiv g :
          CliffordTwoReplicaMatrix →ₗ[ℂ] CliffordTwoReplicaMatrix) :=
      Submodule.mem_map_of_mem hX
    rw [cliffordTwoReplicaCollectiveCommutator_greatestMaximizer_fixed
      U hgreatest g] at hm
    exact hm
  change twirl2 QubitTwoDesign.qubitClifford X ∈ U
  rw [twirl2_eq_sum_doubledConj]
  exact U.smul_mem _ (Submodule.sum_mem U fun g _ => hterm g)

/-- Canonical Clifford-twirl split of every greatest maximum-defect subspace:
the visible part is precisely identity/swap, and the complementary part has
zero doubled Clifford average. -/
theorem cliffordTwoReplicaCollectiveCommutator_greatestMaximizer_split
    (U : Submodule ℂ CliffordTwoReplicaMatrix)
    (hgreatest : ∀ V : Submodule ℂ CliffordTwoReplicaMatrix,
      linearFamilyDefect cliffordTwoReplicaCollectiveCommutatorLinear V =
        linearFamilyDefect cliffordTwoReplicaCollectiveCommutatorLinear U →
      V ≤ U) :
    U =
      (U ⊓ Submodule.span ℂ
        ({(1 : CliffordTwoReplicaMatrix), QubitTwoDesign.qubitSwap} :
          Set CliffordTwoReplicaMatrix)) ⊔
      (U ⊓ LinearMap.ker cliffordTwoReplicaTwirlLinear) := by
  rw [← cliffordTwoReplicaTwirlLinear_range_eq]
  exact invariantSubspace_eq_rangeKernel_split
    cliffordTwoReplicaTwirlLinear
    cliffordTwoReplicaTwirlLinear_idempotent U
    (fun x hx => cliffordTwoReplicaTwirlLinear_mem_greatestMaximizer
      U hgreatest hx)

/-! ## Transport to the Boolean-indexed physical two-replica model -/

/-- Reindex the strict Clifford convention to the Boolean computational basis
used by the physical Pauli/Casimir modules. -/
def cliffordTwoReplicaIndexEquiv :
    CliffordTwoReplicaIndex ≃ TwoReplicaLocalIndex :=
  Equiv.prodCongr finTwoEquiv finTwoEquiv

/-- Algebra equivalence between the two exact one-site matrix conventions. -/
def cliffordToBooleanTwoReplicaAlgEquiv :
    CliffordTwoReplicaMatrix ≃ₐ[ℂ] TwoReplicaLocalMatrix :=
  Matrix.reindexAlgEquiv ℂ ℂ cliffordTwoReplicaIndexEquiv

theorem cliffordQubitPauli_reindex (a : Fin 3) :
    Matrix.reindex finTwoEquiv finTwoEquiv (cliffordQubitPauli a) =
      finiteQubitPauli a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.reindex_apply, cliffordQubitPauli,
      finiteQubitPauli, pauliX, pauliY, pauliZ, finTwoEquiv]

@[simp] theorem cliffordToBooleanTwoReplicaAlgEquiv_one :
    cliffordToBooleanTwoReplicaAlgEquiv (1 : CliffordTwoReplicaMatrix) =
      (1 : TwoReplicaLocalMatrix) := by
  exact map_one cliffordToBooleanTwoReplicaAlgEquiv

theorem qubitSwap_reindex_eq_twoReplicaSwap :
    cliffordToBooleanTwoReplicaAlgEquiv QubitTwoDesign.qubitSwap =
      twoReplicaSwap := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    norm_num [cliffordToBooleanTwoReplicaAlgEquiv,
      Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      cliffordTwoReplicaIndexEquiv, finTwoEquiv,
      QubitTwoDesign.qubitSwap, twoReplicaSwap]

theorem cliffordTwoReplicaCollectivePauli_reindex (a : Fin 3) :
    cliffordToBooleanTwoReplicaAlgEquiv
        (cliffordTwoReplicaCollectivePauli a) =
      twoReplicaPauliLeft a + twoReplicaPauliRight a := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases a <;> fin_cases i₁ <;> fin_cases i₂ <;>
    fin_cases j₁ <;> fin_cases j₂ <;>
    norm_num [cliffordToBooleanTwoReplicaAlgEquiv,
      Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      cliffordTwoReplicaIndexEquiv, finTwoEquiv,
      cliffordTwoReplicaCollectivePauli, cliffordQubitPauli,
      twoReplicaPauliLeft, twoReplicaPauliRight,
      finiteQubitPauli, pauliX, pauliY, pauliZ,
      Matrix.kronecker_apply, Matrix.one_apply]

theorem cliffordTwoReplicaPauliPair_reindex (a : Fin 3) :
    cliffordToBooleanTwoReplicaAlgEquiv
        (cliffordTwoReplicaPauliPair a) =
      twoReplicaPauliPair a := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases a <;> fin_cases i₁ <;> fin_cases i₂ <;>
    fin_cases j₁ <;> fin_cases j₂ <;>
    norm_num [cliffordToBooleanTwoReplicaAlgEquiv,
      Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      cliffordTwoReplicaIndexEquiv, finTwoEquiv,
      cliffordTwoReplicaPauliPair, cliffordQubitPauli,
      twoReplicaPauliPair, finiteQubitPauli,
      pauliX, pauliY, pauliZ, Matrix.kronecker_apply]

/-- Reindexing exactly intertwines the three collective commutator families. -/
theorem cliffordTwoReplicaCollectiveCommutator_reindex
    (a : Fin 3) (X : CliffordTwoReplicaMatrix) :
    cliffordToBooleanTwoReplicaAlgEquiv
        (cliffordTwoReplicaCollectiveCommutatorLinear a X) =
      twoReplicaLocalCollectiveCommutatorLinear a
        (cliffordToBooleanTwoReplicaAlgEquiv X) := by
  change cliffordToBooleanTwoReplicaAlgEquiv
      (ringCommutator (cliffordTwoReplicaCollectivePauli a) X) =
    twoReplicaLocalCollectiveCommutator a
      (cliffordToBooleanTwoReplicaAlgEquiv X)
  rw [twoReplicaLocalCollectiveCommutator]
  simp only [ringCommutator, map_sub, map_mul,
    cliffordTwoReplicaCollectivePauli_reindex]
  noncomm_ring

theorem cliffordToBooleanTwoReplicaAlgEquiv_conjTranspose
    (X : CliffordTwoReplicaMatrix) :
    cliffordToBooleanTwoReplicaAlgEquiv Xᴴ =
      (cliffordToBooleanTwoReplicaAlgEquiv X)ᴴ := by
  change Matrix.reindex cliffordTwoReplicaIndexEquiv
      cliffordTwoReplicaIndexEquiv Xᴴ =
    (Matrix.reindex cliffordTwoReplicaIndexEquiv
      cliffordTwoReplicaIndexEquiv X)ᴴ
  exact (Matrix.conjTranspose_reindex
    cliffordTwoReplicaIndexEquiv cliffordTwoReplicaIndexEquiv X).symm

/-- The doubled Clifford representation in the Boolean computational basis. -/
def booleanCliffordDoubledGate
    (g : QubitTwoDesign.BinaryOctahedral) :
    Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ :=
  cliffordToBooleanTwoReplicaAlgEquiv
    (doubledRep QubitTwoDesign.qubitClifford g)

theorem booleanCliffordDoubledGate_mul
    (g h : QubitTwoDesign.BinaryOctahedral) :
    booleanCliffordDoubledGate (g * h) =
      booleanCliffordDoubledGate g * booleanCliffordDoubledGate h := by
  rw [booleanCliffordDoubledGate, booleanCliffordDoubledGate,
    booleanCliffordDoubledGate,
    doubledRep_mul QubitTwoDesign.qubitClifford
      QubitTwoDesign.qubitClifford_mul, map_mul]

theorem booleanCliffordDoubledGate_unitary
    (g : QubitTwoDesign.BinaryOctahedral) :
    (booleanCliffordDoubledGate g)ᴴ * booleanCliffordDoubledGate g = 1 := by
  rw [booleanCliffordDoubledGate,
    ← cliffordToBooleanTwoReplicaAlgEquiv_conjTranspose,
    ← map_mul,
    doubledRep_unit QubitTwoDesign.qubitClifford
      QubitTwoDesign.qubitClifford_unitary,
    map_one]

theorem booleanCliffordDoubledGate_conjTranspose_eq_inv
    (g : QubitTwoDesign.BinaryOctahedral) :
    (booleanCliffordDoubledGate g)ᴴ =
      booleanCliffordDoubledGate g⁻¹ := by
  rw [booleanCliffordDoubledGate, booleanCliffordDoubledGate,
    ← cliffordToBooleanTwoReplicaAlgEquiv_conjTranspose,
    doubledRep_conjTranspose_eq_inv QubitTwoDesign.qubitClifford
      QubitTwoDesign.qubitClifford_mul
      QubitTwoDesign.qubitClifford_unitary]

/-- Boolean-indexed doubled Clifford conjugation. -/
def booleanCliffordDoubledConjugationEquiv
    (g : QubitTwoDesign.BinaryOctahedral) :
    TwoReplicaLocalMatrix ≃ₗ[ℂ] TwoReplicaLocalMatrix :=
  unitaryMatrixConjugationEquiv (booleanCliffordDoubledGate g)
    (booleanCliffordDoubledGate_unitary g)

@[simp] theorem booleanCliffordDoubledConjugationEquiv_apply
    (g : QubitTwoDesign.BinaryOctahedral) (X : TwoReplicaLocalMatrix) :
    booleanCliffordDoubledConjugationEquiv g X =
      booleanCliffordDoubledGate g * X *
        (booleanCliffordDoubledGate g)ᴴ := rfl

@[simp] theorem booleanCliffordDoubledConjugationEquiv_symm_apply
    (g : QubitTwoDesign.BinaryOctahedral) (X : TwoReplicaLocalMatrix) :
    (booleanCliffordDoubledConjugationEquiv g).symm X =
      (booleanCliffordDoubledGate g)ᴴ * X *
        booleanCliffordDoubledGate g := rfl

theorem booleanCliffordDoubledConjugationEquiv_symm_eq
    (g : QubitTwoDesign.BinaryOctahedral) :
    (booleanCliffordDoubledConjugationEquiv g).symm =
      booleanCliffordDoubledConjugationEquiv g⁻¹ := by
  apply LinearEquiv.ext
  intro X
  change (booleanCliffordDoubledGate g)ᴴ * X *
      booleanCliffordDoubledGate g =
    booleanCliffordDoubledGate g⁻¹ * X *
      (booleanCliffordDoubledGate g⁻¹)ᴴ
  rw [← booleanCliffordDoubledGate_conjTranspose_eq_inv g]
  simp

/-- Reindexing intertwines doubled Clifford conjugation. -/
theorem cliffordDoubledConjugation_reindex
    (g : QubitTwoDesign.BinaryOctahedral)
    (X : CliffordTwoReplicaMatrix) :
    cliffordToBooleanTwoReplicaAlgEquiv
        (cliffordDoubledConjugationEquiv g X) =
      booleanCliffordDoubledConjugationEquiv g
        (cliffordToBooleanTwoReplicaAlgEquiv X) := by
  simp only [cliffordDoubledConjugationEquiv_apply,
    booleanCliffordDoubledConjugationEquiv_apply,
    booleanCliffordDoubledGate, map_mul,
    cliffordToBooleanTwoReplicaAlgEquiv_conjTranspose]

/-- Reindexing also intertwines inverse doubled Clifford conjugation. -/
theorem cliffordDoubledConjugation_symm_reindex
    (g : QubitTwoDesign.BinaryOctahedral)
    (X : CliffordTwoReplicaMatrix) :
    cliffordToBooleanTwoReplicaAlgEquiv
        ((cliffordDoubledConjugationEquiv g).symm X) =
      (booleanCliffordDoubledConjugationEquiv g).symm
        (cliffordToBooleanTwoReplicaAlgEquiv X) := by
  simp only [cliffordDoubledConjugationEquiv_symm_apply,
    booleanCliffordDoubledConjugationEquiv_symm_apply,
    booleanCliffordDoubledGate, map_mul,
    cliffordToBooleanTwoReplicaAlgEquiv_conjTranspose]

/-- Physical Boolean-indexed form of exact finite-group interpolation of the
collective Casimir. -/
theorem booleanTwoReplicaCollectiveCommutator_square_groupAlgebra
    (a : Fin 3) (X : TwoReplicaLocalMatrix) :
    twoReplicaLocalCollectiveCommutatorLinear a
        (twoReplicaLocalCollectiveCommutatorLinear a X) =
      (6 : ℂ) • X - (4 : ℂ) •
        (booleanCliffordDoubledConjugationEquiv
            (cliffordQuarterTurnCode a) X +
          (booleanCliffordDoubledConjugationEquiv
            (cliffordQuarterTurnCode a)).symm X) +
        (2 : ℂ) •
          (twoReplicaPauliPair a * X * twoReplicaPauliPair a) := by
  let Y : CliffordTwoReplicaMatrix :=
    cliffordToBooleanTwoReplicaAlgEquiv.symm X
  have h := congrArg cliffordToBooleanTwoReplicaAlgEquiv
    (cliffordTwoReplicaCollectiveCommutator_square_groupAlgebra a Y)
  simp only [map_add, map_sub, map_smul, map_mul] at h
  rw [cliffordTwoReplicaCollectiveCommutator_reindex,
    cliffordTwoReplicaCollectiveCommutator_reindex,
    cliffordDoubledConjugation_reindex,
    cliffordDoubledConjugation_symm_reindex,
    cliffordTwoReplicaPauliPair_reindex] at h
  simpa [Y] using h

/-- The exact Clifford normalizer action transported into the physical
Boolean two-replica matrix convention. -/
theorem booleanCliffordDoubled_conj_collectivePauli
    (g : QubitTwoDesign.BinaryOctahedral) (a : Fin 3) :
    ∃ b : Fin 3,
      booleanCliffordDoubledGate g *
          (twoReplicaPauliLeft a + twoReplicaPauliRight a) *
            (booleanCliffordDoubledGate g)ᴴ =
          twoReplicaPauliLeft b + twoReplicaPauliRight b ∨
      booleanCliffordDoubledGate g *
          (twoReplicaPauliLeft a + twoReplicaPauliRight a) *
            (booleanCliffordDoubledGate g)ᴴ =
          -(twoReplicaPauliLeft b + twoReplicaPauliRight b) := by
  obtain ⟨b, hb | hb⟩ := cliffordDoubled_conj_collectivePauli g a
  · refine ⟨b, Or.inl ?_⟩
    have h := congrArg cliffordToBooleanTwoReplicaAlgEquiv hb
    simpa [booleanCliffordDoubledGate, map_mul,
      cliffordToBooleanTwoReplicaAlgEquiv_conjTranspose,
      cliffordTwoReplicaCollectivePauli_reindex] using h
  · refine ⟨b, Or.inr ?_⟩
    have h := congrArg cliffordToBooleanTwoReplicaAlgEquiv hb
    simpa [booleanCliffordDoubledGate, map_mul,
      cliffordToBooleanTwoReplicaAlgEquiv_conjTranspose,
      cliffordTwoReplicaCollectivePauli_reindex] using h

/-- Operator-span covariance in the literal Boolean physical convention. -/
theorem booleanCliffordDoubled_conjugatedCollectiveCommutator_mem_span
    (a : Fin 3) (g : QubitTwoDesign.BinaryOctahedral) :
    (((booleanCliffordDoubledConjugationEquiv g :
        TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix).comp
      (twoReplicaLocalCollectiveCommutatorLinear a)).comp
      ((booleanCliffordDoubledConjugationEquiv g).symm :
        TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix)) ∈
      linearFamilyOperatorSpan
        twoReplicaLocalCollectiveCommutatorLinear := by
  obtain ⟨b, hb | hb⟩ :=
    booleanCliffordDoubled_conj_collectivePauli g a
  · have heq :
        (((booleanCliffordDoubledConjugationEquiv g :
            TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix).comp
          (twoReplicaLocalCollectiveCommutatorLinear a)).comp
          ((booleanCliffordDoubledConjugationEquiv g).symm :
            TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix)) =
          twoReplicaLocalCollectiveCommutatorLinear b := by
      apply LinearMap.ext
      intro X
      change booleanCliffordDoubledGate g *
          twoReplicaLocalCollectiveCommutator a
            ((booleanCliffordDoubledGate g)ᴴ * X *
              booleanCliffordDoubledGate g) *
            (booleanCliffordDoubledGate g)ᴴ = _
      rw [twoReplicaLocalCollectiveCommutator,
        ← ringCommutator_add_left',
        ringCommutator_unitary_conjugation _ _ _
          (booleanCliffordDoubledGate_unitary g), hb]
      rw [ringCommutator_add_left']
      rfl
    rw [heq]
    exact Submodule.subset_span ⟨b, rfl⟩
  · have heq :
        (((booleanCliffordDoubledConjugationEquiv g :
            TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix).comp
          (twoReplicaLocalCollectiveCommutatorLinear a)).comp
          ((booleanCliffordDoubledConjugationEquiv g).symm :
            TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix)) =
          -twoReplicaLocalCollectiveCommutatorLinear b := by
      apply LinearMap.ext
      intro X
      change booleanCliffordDoubledGate g *
          twoReplicaLocalCollectiveCommutator a
            ((booleanCliffordDoubledGate g)ᴴ * X *
              booleanCliffordDoubledGate g) *
            (booleanCliffordDoubledGate g)ᴴ = _
      rw [twoReplicaLocalCollectiveCommutator,
        ← ringCommutator_add_left',
        ringCommutator_unitary_conjugation _ _ _
          (booleanCliffordDoubledGate_unitary g), hb,
        ringCommutator_neg_left, ringCommutator_add_left']
      rfl
    rw [heq]
    exact (linearFamilyOperatorSpan
      twoReplicaLocalCollectiveCommutatorLinear).neg_mem
        (Submodule.subset_span ⟨b, rfl⟩)

/-- The canonical greatest physical one-site Hall obstruction is fixed by
every strict doubled Clifford conjugation. -/
theorem booleanTwoReplicaCollectiveCommutator_greatestMaximizer_fixed
    (U : Submodule ℂ TwoReplicaLocalMatrix)
    (hgreatest : ∀ V : Submodule ℂ TwoReplicaLocalMatrix,
      linearFamilyDefect twoReplicaLocalCollectiveCommutatorLinear V =
        linearFamilyDefect twoReplicaLocalCollectiveCommutatorLinear U →
      V ≤ U)
    (g : QubitTwoDesign.BinaryOctahedral) :
    U.map (booleanCliffordDoubledConjugationEquiv g :
      TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix) = U := by
  apply linearFamilyDefect_greatestMaximizer_map_eq_of_spanCovariant
      twoReplicaLocalCollectiveCommutatorLinear U
      (booleanCliffordDoubledConjugationEquiv g)
      (booleanCliffordDoubledConjugationEquiv g) hgreatest
  · exact fun a =>
      booleanCliffordDoubled_conjugatedCollectiveCommutator_mem_span a g
  · intro a
    rw [booleanCliffordDoubledConjugationEquiv_symm_eq]
    simpa [booleanCliffordDoubledConjugationEquiv_symm_eq] using
      booleanCliffordDoubled_conjugatedCollectiveCommutator_mem_span a g⁻¹

/-- Every physical one-axis collective-Casimir summand preserves the
canonical greatest Hall obstruction. -/
theorem booleanTwoReplicaCollectiveCommutator_square_mem_greatestMaximizer
    (U : Submodule ℂ TwoReplicaLocalMatrix)
    (hgreatest : ∀ V : Submodule ℂ TwoReplicaLocalMatrix,
      linearFamilyDefect twoReplicaLocalCollectiveCommutatorLinear V =
        linearFamilyDefect twoReplicaLocalCollectiveCommutatorLinear U →
      V ≤ U)
    (a : Fin 3) {X : TwoReplicaLocalMatrix} (hX : X ∈ U) :
    twoReplicaLocalCollectiveCommutatorLinear a
        (twoReplicaLocalCollectiveCommutatorLinear a X) ∈ U := by
  have hmap (g : QubitTwoDesign.BinaryOctahedral) :
      booleanCliffordDoubledConjugationEquiv g X ∈ U := by
    rw [← booleanTwoReplicaCollectiveCommutator_greatestMaximizer_fixed
      U hgreatest g]
    exact ⟨X, hX, rfl⟩
  have hquarter :
      booleanCliffordDoubledConjugationEquiv
        (cliffordQuarterTurnCode a) X ∈ U := hmap _
  have hquarterInv :
      (booleanCliffordDoubledConjugationEquiv
        (cliffordQuarterTurnCode a)).symm X ∈ U := by
    rw [booleanCliffordDoubledConjugationEquiv_symm_eq]
    exact hmap _
  have hhalf :
      twoReplicaPauliPair a * X * twoReplicaPauliPair a ∈ U := by
    have hm : twoReplicaPairedPauliConjugationLinear a X ∈ U := by
      rw [← twoReplicaLocalCollectiveCommutator_greatestMaximizer_fixed
        U hgreatest a]
      exact ⟨X, hX, rfl⟩
    exact hm
  rw [booleanTwoReplicaCollectiveCommutator_square_groupAlgebra]
  exact U.add_mem
    (U.sub_mem (U.smul_mem _ hX)
      (U.smul_mem _ (U.add_mem hquarter hquarterInv)))
    (U.smul_mem _ hhalf)

/-- The exact doubled-Clifford first moment on Boolean-indexed two-replica
operators. -/
def booleanCliffordTwoReplicaTwirlLinear :
    TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix where
  toFun X := repTwirl booleanCliffordDoubledGate X
  map_add' X Y := by
    simp [repTwirl, Matrix.mul_add, Matrix.add_mul,
      Finset.sum_add_distrib]
  map_smul' c X := by
    unfold repTwirl
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [← Finset.smul_sum, smul_smul, smul_smul, mul_comm]
    rfl

/-- The Boolean doubled Clifford gate commutes with the physical swap. -/
theorem booleanCliffordDoubledGate_commute_twoReplicaSwap
    (g : QubitTwoDesign.BinaryOctahedral) :
    booleanCliffordDoubledGate g * twoReplicaSwap =
      twoReplicaSwap * booleanCliffordDoubledGate g := by
  have h := congrArg cliffordToBooleanTwoReplicaAlgEquiv
    (QubitTwoDesign.kronecker_self_commute_qubitSwap
      (QubitTwoDesign.qubitClifford g))
  simpa [booleanCliffordDoubledGate, doubledRep, map_mul,
    qubitSwap_reindex_eq_twoReplicaSwap] using h

/-- The Boolean Clifford average fixes its entire commutant. -/
theorem booleanCliffordTwoReplica_twirl_eq_self_of_commute
    (X : TwoReplicaLocalMatrix)
    (hX : ∀ g, booleanCliffordDoubledGate g * X =
      X * booleanCliffordDoubledGate g) :
    repTwirl booleanCliffordDoubledGate X = X := by
  haveI : Nonempty QubitTwoDesign.BinaryOctahedral := ⟨1⟩
  have hcard :
      (Fintype.card QubitTwoDesign.BinaryOctahedral : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hterm : ∀ g : QubitTwoDesign.BinaryOctahedral,
      booleanCliffordDoubledGate g * X *
          (booleanCliffordDoubledGate g)ᴴ = X := by
    intro g
    rw [hX g, Matrix.mul_assoc,
      mul_eq_one_comm.mp (booleanCliffordDoubledGate_unitary g),
      Matrix.mul_one]
  rw [repTwirl, Finset.sum_congr rfl (fun g _ => hterm g),
    Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

/-- The Boolean physical twirl has exactly the identity/swap range. -/
theorem booleanCliffordTwoReplicaTwirlLinear_range_eq :
    LinearMap.range booleanCliffordTwoReplicaTwirlLinear =
      Submodule.span ℂ
        ({(1 : TwoReplicaLocalMatrix), twoReplicaSwap} :
          Set TwoReplicaLocalMatrix) := by
  apply le_antisymm
  · rintro Y ⟨X, rfl⟩
    change repTwirl booleanCliffordDoubledGate X ∈ _
    let T := repTwirl booleanCliffordDoubledGate X
    let M : CliffordTwoReplicaMatrix :=
      cliffordToBooleanTwoReplicaAlgEquiv.symm T
    have hcomm : ∀ g,
        doubledRep QubitTwoDesign.qubitClifford g * M =
          M * doubledRep QubitTwoDesign.qubitClifford g := by
      intro g
      apply cliffordToBooleanTwoReplicaAlgEquiv.injective
      simpa [M, booleanCliffordDoubledGate, map_mul] using
        (repTwirl_commute booleanCliffordDoubledGate
          booleanCliffordDoubledGate_mul
          booleanCliffordDoubledGate_unitary X g)
    have hnormal := QubitTwoDesign.qubitClifford_commutant_normal_form M hcomm
    have hT : T =
        M (1, 0) (1, 0) • (1 : TwoReplicaLocalMatrix) +
          (M (0, 0) (0, 0) - M (1, 0) (1, 0)) •
            twoReplicaSwap := by
      calc
        T = cliffordToBooleanTwoReplicaAlgEquiv M := by simp [M]
        _ = cliffordToBooleanTwoReplicaAlgEquiv
            (M (1, 0) (1, 0) • (1 : CliffordTwoReplicaMatrix) +
              (M (0, 0) (0, 0) - M (1, 0) (1, 0)) •
                QubitTwoDesign.qubitSwap) :=
          congrArg cliffordToBooleanTwoReplicaAlgEquiv hnormal
        _ = _ := by
          rw [map_add, map_smul, map_smul,
            cliffordToBooleanTwoReplicaAlgEquiv_one,
            qubitSwap_reindex_eq_twoReplicaSwap]
    change T ∈ _
    rw [hT]
    exact (Submodule.span ℂ
      ({(1 : TwoReplicaLocalMatrix), twoReplicaSwap} :
        Set TwoReplicaLocalMatrix)).add_mem
      ((Submodule.span ℂ _).smul_mem _
        (Submodule.subset_span (by simp)))
      ((Submodule.span ℂ _).smul_mem _
        (Submodule.subset_span (by simp)))
  · rw [Submodule.span_le]
    intro X hX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl
    · refine ⟨1, ?_⟩
      exact booleanCliffordTwoReplica_twirl_eq_self_of_commute 1 (by simp)
    · refine ⟨twoReplicaSwap, ?_⟩
      exact booleanCliffordTwoReplica_twirl_eq_self_of_commute
        twoReplicaSwap booleanCliffordDoubledGate_commute_twoReplicaSwap

theorem booleanCliffordTwoReplicaTwirlLinear_idempotent :
    ∀ X, booleanCliffordTwoReplicaTwirlLinear
      (booleanCliffordTwoReplicaTwirlLinear X) =
        booleanCliffordTwoReplicaTwirlLinear X := by
  intro X
  exact repTwirl_idem booleanCliffordDoubledGate
    booleanCliffordDoubledGate_mul X

theorem booleanCliffordTwoReplicaTwirlLinear_mem_greatestMaximizer
    (U : Submodule ℂ TwoReplicaLocalMatrix)
    (hgreatest : ∀ V : Submodule ℂ TwoReplicaLocalMatrix,
      linearFamilyDefect twoReplicaLocalCollectiveCommutatorLinear V =
        linearFamilyDefect twoReplicaLocalCollectiveCommutatorLinear U →
      V ≤ U)
    {X : TwoReplicaLocalMatrix} (hX : X ∈ U) :
    booleanCliffordTwoReplicaTwirlLinear X ∈ U := by
  have hterm : ∀ g : QubitTwoDesign.BinaryOctahedral,
      booleanCliffordDoubledGate g * X *
          (booleanCliffordDoubledGate g)ᴴ ∈ U := by
    intro g
    have hm : booleanCliffordDoubledConjugationEquiv g X ∈
        U.map (booleanCliffordDoubledConjugationEquiv g :
          TwoReplicaLocalMatrix →ₗ[ℂ] TwoReplicaLocalMatrix) :=
      Submodule.mem_map_of_mem hX
    rw [booleanTwoReplicaCollectiveCommutator_greatestMaximizer_fixed
      U hgreatest g] at hm
    exact hm
  change repTwirl booleanCliffordDoubledGate X ∈ U
  unfold repTwirl
  exact U.smul_mem _ (Submodule.sum_mem U fun g _ => hterm g)

/-- Physical one-site capstone: every canonical greatest maximum-defect
subspace splits into its identity/swap sector and an exact zero-Clifford-twirl
sector. -/
theorem booleanTwoReplicaCollectiveCommutator_greatestMaximizer_split
    (U : Submodule ℂ TwoReplicaLocalMatrix)
    (hgreatest : ∀ V : Submodule ℂ TwoReplicaLocalMatrix,
      linearFamilyDefect twoReplicaLocalCollectiveCommutatorLinear V =
        linearFamilyDefect twoReplicaLocalCollectiveCommutatorLinear U →
      V ≤ U) :
    U =
      (U ⊓ Submodule.span ℂ
        ({(1 : TwoReplicaLocalMatrix), twoReplicaSwap} :
          Set TwoReplicaLocalMatrix)) ⊔
      (U ⊓ LinearMap.ker booleanCliffordTwoReplicaTwirlLinear) := by
  rw [← booleanCliffordTwoReplicaTwirlLinear_range_eq]
  exact invariantSubspace_eq_rangeKernel_split
    booleanCliffordTwoReplicaTwirlLinear
    booleanCliffordTwoReplicaTwirlLinear_idempotent U
    (fun x hx => booleanCliffordTwoReplicaTwirlLinear_mem_greatestMaximizer
      U hgreatest hx)

end

end GaloisForLFunctions.HTGeometry
