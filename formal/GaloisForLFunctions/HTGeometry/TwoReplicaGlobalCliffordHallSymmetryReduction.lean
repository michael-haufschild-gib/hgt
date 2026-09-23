import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalPauliHallSymmetryReduction
import GaloisForLFunctions.HTGeometry.TwoReplicaCliffordTwirlHallSymmetryReduction

/-!
# Arbitrary-register product-Clifford reduction of the two-replica Hall obstruction

This file lifts the exact one-qubit Clifford normalizer law to every finite
qubit register.  Product Clifford conjugation preserves Pauli support exactly,
so it normalizes the complete weight-at-most-`q` collective-commutator family
for every `q`.  Consequently the canonical greatest Hall obstruction is fixed
by every product Clifford, with no moment or design assumption.
-/

open scoped BigOperators Matrix Kronecker
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open QuantumAlg

/-- Algebra equivalence from the strict `Fin 2` Clifford convention to the
Boolean computational basis used by the arbitrary-register Pauli modules. -/
def cliffordToBooleanQubitAlgEquiv :
    Matrix (Fin 2) (Fin 2) ℂ ≃ₐ[ℂ] Matrix Bool Bool ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ finTwoEquiv

theorem cliffordToBooleanQubitAlgEquiv_conjTranspose
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    cliffordToBooleanQubitAlgEquiv Xᴴ =
      (cliffordToBooleanQubitAlgEquiv X)ᴴ := by
  change Matrix.reindex finTwoEquiv finTwoEquiv Xᴴ =
    (Matrix.reindex finTwoEquiv finTwoEquiv X)ᴴ
  exact (Matrix.conjTranspose_reindex finTwoEquiv finTwoEquiv X).symm

theorem cliffordToBooleanQubitAlgEquiv_pauli (a : Fin 3) :
    cliffordToBooleanQubitAlgEquiv (cliffordQubitPauli a) =
      finiteQubitPauli a := by
  change Matrix.reindex finTwoEquiv finTwoEquiv (cliffordQubitPauli a) =
    finiteQubitPauli a
  exact cliffordQubitPauli_reindex a

/-- The strict one-qubit Clifford lift in the Boolean computational basis. -/
def booleanQubitClifford
    (g : QubitTwoDesign.BinaryOctahedral) : Matrix Bool Bool ℂ :=
  cliffordToBooleanQubitAlgEquiv (QubitTwoDesign.qubitClifford g)

theorem booleanQubitClifford_unitary
    (g : QubitTwoDesign.BinaryOctahedral) :
    (booleanQubitClifford g)ᴴ * booleanQubitClifford g = 1 := by
  rw [booleanQubitClifford,
    ← cliffordToBooleanQubitAlgEquiv_conjTranspose,
    ← map_mul, QubitTwoDesign.qubitClifford_unitary, map_one]

theorem qubitClifford_one :
    QubitTwoDesign.qubitClifford 1 = 1 := by
  let C := QubitTwoDesign.qubitClifford 1
  have hunit : Cᴴ * C = 1 := QubitTwoDesign.qubitClifford_unitary 1
  have hmul : C = C * C := by
    simpa [C] using QubitTwoDesign.qubitClifford_mul 1 1
  calc
    C = 1 * C := by rw [Matrix.one_mul]
    _ = (Cᴴ * C) * C := by rw [hunit]
    _ = Cᴴ * (C * C) := by rw [Matrix.mul_assoc]
    _ = Cᴴ * C := by rw [← hmul]
    _ = 1 := hunit

theorem qubitClifford_conjTranspose_eq_inv
    (g : QubitTwoDesign.BinaryOctahedral) :
    (QubitTwoDesign.qubitClifford g)ᴴ =
      QubitTwoDesign.qubitClifford g⁻¹ := by
  let C := QubitTwoDesign.qubitClifford g
  let D := QubitTwoDesign.qubitClifford g⁻¹
  have hunit : Cᴴ * C = 1 := QubitTwoDesign.qubitClifford_unitary g
  have hright : C * Cᴴ = 1 := mul_eq_one_comm.mp hunit
  have hleft : D * C = 1 := by
    calc
      D * C = QubitTwoDesign.qubitClifford (g⁻¹ * g) :=
        (QubitTwoDesign.qubitClifford_mul g⁻¹ g).symm
      _ = 1 := by simp [qubitClifford_one]
  calc
    Cᴴ = 1 * Cᴴ := by rw [Matrix.one_mul]
    _ = (D * C) * Cᴴ := by rw [hleft]
    _ = D * (C * Cᴴ) := by rw [Matrix.mul_assoc]
    _ = D := by rw [hright, Matrix.mul_one]

theorem booleanQubitClifford_conjTranspose_eq_inv
    (g : QubitTwoDesign.BinaryOctahedral) :
    (booleanQubitClifford g)ᴴ = booleanQubitClifford g⁻¹ := by
  rw [booleanQubitClifford, booleanQubitClifford,
    ← cliffordToBooleanQubitAlgEquiv_conjTranspose,
    qubitClifford_conjTranspose_eq_inv]

theorem booleanQubitClifford_conj_finiteQubitPauli
    (g : QubitTwoDesign.BinaryOctahedral) (a : Fin 3) :
    ∃ b : Fin 3,
      booleanQubitClifford g * finiteQubitPauli a *
          (booleanQubitClifford g)ᴴ = finiteQubitPauli b ∨
      booleanQubitClifford g * finiteQubitPauli a *
          (booleanQubitClifford g)ᴴ = -finiteQubitPauli b := by
  have hmem :
      QubitTwoDesign.qubitClifford g * cliffordQubitPauli a *
          (QubitTwoDesign.qubitClifford g)ᴴ ∈
        QubitTwoDesign.signedRawPauliSet :=
    QubitTwoDesign.qubitClifford_conj_pauli_mem g
      (cliffordQubitPauli_mem_signedRawPauliSet a)
  obtain ⟨b, hb | hb⟩ :=
    exists_cliffordQubitPauli_sign_of_mem_signedRawPauliSet hmem
  · refine ⟨b, Or.inl ?_⟩
    have h := congrArg cliffordToBooleanQubitAlgEquiv hb
    simpa [booleanQubitClifford, map_mul,
      cliffordToBooleanQubitAlgEquiv_conjTranspose,
      cliffordToBooleanQubitAlgEquiv_pauli] using h
  · refine ⟨b, Or.inr ?_⟩
    have h := congrArg cliffordToBooleanQubitAlgEquiv hb
    simpa [booleanQubitClifford, map_mul,
      cliffordToBooleanQubitAlgEquiv_conjTranspose,
      cliffordToBooleanQubitAlgEquiv_pauli] using h

/-- A one-qubit Clifford sends an identity/Pauli label to a label with the
same identity support, up to one scalar sign. -/
theorem exists_booleanQubitClifford_conj_boolPauliOption
    (g : QubitTwoDesign.BinaryOctahedral) (p : Option (Fin 3)) :
    ∃ p' : Option (Fin 3), ∃ c : ℂ,
      (p' = none ↔ p = none) ∧
      booleanQubitClifford g * boolPauliOption p *
          (booleanQubitClifford g)ᴴ = c • boolPauliOption p' := by
  cases p with
  | none =>
      refine ⟨none, 1, Iff.rfl, ?_⟩
      have hunit' : booleanQubitClifford g *
          (booleanQubitClifford g)ᴴ = 1 :=
        mul_eq_one_comm.mp (booleanQubitClifford_unitary g)
      simpa [boolPauliOption] using hunit'
  | some a =>
      obtain ⟨b, hb | hb⟩ :=
        booleanQubitClifford_conj_finiteQubitPauli g a
      · refine ⟨some b, 1, by simp, ?_⟩
        simpa [boolPauliOption] using hb
      · refine ⟨some b, -1, by simp, ?_⟩
        simpa [boolPauliOption] using hb

theorem finiteLocalMatrix_conjTranspose
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (M : sigma → Matrix Bool Bool ℂ) :
    (finiteLocalMatrix M)ᴴ = finiteLocalMatrix fun s => (M s)ᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, finiteLocalMatrix]
  rw [← starRingEnd_apply, map_prod]
  rfl

theorem finiteLocalMatrix_one
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma] :
    finiteLocalMatrix (fun _ : sigma => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [finiteLocalMatrix]
  · obtain ⟨s, hs⟩ : ∃ s, x s ≠ y s := by
      simpa only [Function.ne_iff] using hxy
    rw [finiteLocalMatrix, Matrix.one_apply, if_neg hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])

/-- Lift one Boolean-indexed one-qubit matrix to one distinguished site of an
arbitrary finite register. -/
def finiteSingleSiteMatrix
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (j : sigma) (M : Matrix Bool Bool ℂ) :
    Matrix (FiniteQubitConfiguration sigma) (FiniteQubitConfiguration sigma) ℂ :=
  finiteLocalMatrix fun s => if s = j then M else 1

theorem finiteSingleSiteMatrix_apply
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (j : sigma) (M : Matrix Bool Bool ℂ)
    (x y : FiniteQubitConfiguration sigma) :
    finiteSingleSiteMatrix j M x y =
      M (x j) (y j) *
        ∏ s ∈ Finset.univ.erase j,
          (1 : Matrix Bool Bool ℂ) (x s) (y s) := by
  rw [finiteSingleSiteMatrix, finiteLocalMatrix,
    ← Finset.mul_prod_erase Finset.univ
      (fun s => (if s = j then M else 1) (x s) (y s))
      (Finset.mem_univ j)]
  congr 1
  · rw [if_pos rfl]
  · refine Finset.prod_congr rfl fun s hs => ?_
    rw [if_neg (Finset.ne_of_mem_erase hs)]

theorem finiteSingleSiteMatrix_smul
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (j : sigma) (c : ℂ) (M : Matrix Bool Bool ℂ) :
    finiteSingleSiteMatrix j (c • M) =
      c • finiteSingleSiteMatrix j M := by
  ext x y
  change finiteSingleSiteMatrix j (c • M) x y =
    c * finiteSingleSiteMatrix j M x y
  rw [finiteSingleSiteMatrix_apply, finiteSingleSiteMatrix_apply]
  simp [Matrix.smul_apply, mul_assoc]

theorem finiteSingleSiteMatrix_add
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (j : sigma) (M N : Matrix Bool Bool ℂ) :
    finiteSingleSiteMatrix j (M + N) =
      finiteSingleSiteMatrix j M + finiteSingleSiteMatrix j N := by
  ext x y
  change finiteSingleSiteMatrix j (M + N) x y =
    finiteSingleSiteMatrix j M x y + finiteSingleSiteMatrix j N x y
  rw [finiteSingleSiteMatrix_apply, finiteSingleSiteMatrix_apply,
    finiteSingleSiteMatrix_apply]
  simp only [Matrix.add_apply]
  ring

theorem finiteSingleSiteMatrix_one
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (j : sigma) :
    finiteSingleSiteMatrix j (1 : Matrix Bool Bool ℂ) = 1 := by
  rw [finiteSingleSiteMatrix]
  convert finiteLocalMatrix_one (sigma := sigma) using 1
  funext s
  simp

/-- Pauli label supported on exactly one distinguished site. -/
def finiteSingleSitePauliLabel
    {sigma : Type*} [DecidableEq sigma]
    (j : sigma) (a : Fin 3) : sigma → Option (Fin 3) :=
  fun s => if s = j then some a else none

theorem finiteSingleSiteMatrix_pauli
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (j : sigma) (a : Fin 3) :
    finiteSingleSiteMatrix j (finiteQubitPauli a) =
      finitePauliMatrix (finiteSingleSitePauliLabel j a) := by
  rw [finiteSingleSiteMatrix, finitePauliMatrix_eq_finiteLocalMatrix]
  congr 1
  funext s
  by_cases hs : s = j <;>
    simp [finiteSingleSitePauliLabel, hs, boolPauliOption]

theorem finitePauliWeight_finiteSingleSitePauliLabel
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (j : sigma) (a : Fin 3) :
    finitePauliWeight (finiteSingleSitePauliLabel j a) = 1 := by
  rw [finitePauliWeight]
  have hfilter :
      Finset.univ.filter
          (fun s => finiteSingleSitePauliLabel j a s ≠ none) = {j} := by
    ext s
    by_cases hs : s = j <;>
      simp [finiteSingleSitePauliLabel, hs]
  rw [hfilter, Finset.card_singleton]

theorem booleanQubitClifford_one :
    booleanQubitClifford 1 = 1 := by
  rw [booleanQubitClifford, qubitClifford_one, map_one]

theorem booleanQubitClifford_quarterTurn_matrix (a : Fin 3) :
    booleanQubitClifford (cliffordQuarterTurnCode a) =
      rt2inv • (1 + Complex.I • finiteQubitPauli a) := by
  have h := congrArg cliffordToBooleanQubitAlgEquiv
    (cliffordQuarterTurn_matrix a)
  simpa [booleanQubitClifford, map_add, map_smul, map_one,
    cliffordToBooleanQubitAlgEquiv_pauli] using h

/-- Product-Clifford code that applies one positive Pauli quarter turn at
site `j` and the identity at every other site. -/
def finiteSingleSiteQuarterTurnCode
    {sigma : Type*} [DecidableEq sigma]
    (j : sigma) (a : Fin 3) :
    sigma → QubitTwoDesign.BinaryOctahedral :=
  fun s => if s = j then cliffordQuarterTurnCode a else 1

/-- Tensor product of independently chosen strict Clifford gates on an
arbitrary finite qubit register. -/
def finiteProductCliffordGate
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (g : sigma → QubitTwoDesign.BinaryOctahedral) :
    Matrix (FiniteQubitConfiguration sigma) (FiniteQubitConfiguration sigma) ℂ :=
  finiteLocalMatrix fun s => booleanQubitClifford (g s)

theorem finiteProductCliffordGate_singleSiteQuarterTurn
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (j : sigma) (a : Fin 3) :
    finiteProductCliffordGate (finiteSingleSiteQuarterTurnCode j a) =
      rt2inv •
        (1 + Complex.I •
          finitePauliMatrix (finiteSingleSitePauliLabel j a)) := by
  have hgate :
      finiteProductCliffordGate (finiteSingleSiteQuarterTurnCode j a) =
        finiteSingleSiteMatrix j
          (booleanQubitClifford (cliffordQuarterTurnCode a)) := by
    rw [finiteProductCliffordGate, finiteSingleSiteMatrix]
    congr 1
    funext s
    by_cases hs : s = j <;>
      simp [finiteSingleSiteQuarterTurnCode, hs, booleanQubitClifford_one]
  rw [hgate, booleanQubitClifford_quarterTurn_matrix,
    finiteSingleSiteMatrix_smul, finiteSingleSiteMatrix_add,
    finiteSingleSiteMatrix_one, finiteSingleSiteMatrix_smul,
    finiteSingleSiteMatrix_pauli]

theorem finiteProductCliffordGate_unitary
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (g : sigma → QubitTwoDesign.BinaryOctahedral) :
    (finiteProductCliffordGate g)ᴴ * finiteProductCliffordGate g = 1 := by
  rw [finiteProductCliffordGate, finiteLocalMatrix_conjTranspose,
    finiteLocalMatrix_mul]
  have hpoint :
      (fun s => (booleanQubitClifford (g s))ᴴ *
        booleanQubitClifford (g s)) =
      (fun _ : sigma => (1 : Matrix Bool Bool ℂ)) := by
    funext s
    exact booleanQubitClifford_unitary (g s)
  rw [hpoint, finiteLocalMatrix_one]

theorem finiteProductCliffordGate_conjTranspose_eq_inv
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (g : sigma → QubitTwoDesign.BinaryOctahedral) :
    (finiteProductCliffordGate g)ᴴ =
      finiteProductCliffordGate fun s => (g s)⁻¹ := by
  rw [finiteProductCliffordGate, finiteProductCliffordGate,
    finiteLocalMatrix_conjTranspose]
  congr 1
  funext s
  exact booleanQubitClifford_conjTranspose_eq_inv (g s)

/-- Product Clifford conjugation permutes Pauli strings up to scalar and
preserves their support weight exactly. -/
theorem finiteProductCliffordGate_conj_finitePauliMatrix
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (g : sigma → QubitTwoDesign.BinaryOctahedral)
    (P : sigma → Option (Fin 3)) :
    ∃ P' : sigma → Option (Fin 3), ∃ c : ℂ,
      finitePauliWeight P' = finitePauliWeight P ∧
      finiteProductCliffordGate g * finitePauliMatrix P *
          (finiteProductCliffordGate g)ᴴ =
        c • finitePauliMatrix P' := by
  classical
  have hlocal : ∀ s : sigma, ∃ p' : Option (Fin 3), ∃ c : ℂ,
      (p' = none ↔ P s = none) ∧
      booleanQubitClifford (g s) * boolPauliOption (P s) *
          (booleanQubitClifford (g s))ᴴ = c • boolPauliOption p' :=
    fun s => exists_booleanQubitClifford_conj_boolPauliOption (g s) (P s)
  choose P' c hnone hconj using hlocal
  refine ⟨P', ∏ s, c s, ?_, ?_⟩
  · rw [finitePauliWeight, finitePauliWeight]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_congr (hnone s)
  · rw [finiteProductCliffordGate,
      finitePauliMatrix_eq_finiteLocalMatrix,
      finiteLocalMatrix_conjTranspose,
      finiteLocalMatrix_mul, finiteLocalMatrix_mul]
    rw [show
      (fun s => booleanQubitClifford (g s) * boolPauliOption (P s) *
        (booleanQubitClifford (g s))ᴴ) =
      (fun s => c s • boolPauliOption (P' s)) by
        funext s
        exact hconj s]
    exact finiteLocalMatrix_pointwise_smul c
      (fun s => boolPauliOption (P' s))

/-- Pure ring identity behind finite quarter-turn recovery of a collective
Casimir.  `J` is an abstract central square root of `-1`; no topology or
differentiation occurs. -/
theorem twoInvolutionQuarterTurnCasimirIdentity
    {R : Type*} [Ring R]
    (A B J X : R)
    (hA : A * A = 1) (hB : B * B = 1) (hAB : A * B = B * A)
    (hJ : J * J = -1) (hJA : J * A = A * J)
    (hJB : J * B = B * J) (hJX : J * X = X * J) :
    let Tp : R := 1 + J * (A + B) - A * B
    let Tm : R := 1 - J * (A + B) - A * B
    ringCommutator (A + B) (ringCommutator (A + B) X) =
      6 * X - (Tp * X * Tm + Tm * X * Tp) +
        2 * ((A * B) * X * (A * B)) := by
  dsimp
  have hJAJ : J * (A * J) = -A := by
    calc
      J * (A * J) = (J * A) * J := by rw [mul_assoc]
      _ = (A * J) * J := by rw [hJA]
      _ = A * (J * J) := by rw [mul_assoc]
      _ = -A := by rw [hJ]; simp
  have hJBJ : J * (B * J) = -B := by
    calc
      J * (B * J) = (J * B) * J := by rw [mul_assoc]
      _ = (B * J) * J := by rw [hJB]
      _ = B * (J * J) := by rw [mul_assoc]
      _ = -B := by rw [hJ]; simp
  have hAAX : A * (A * X) = X := by
    rw [← mul_assoc, hA, one_mul]
  have hBBX : B * (B * X) = X := by
    rw [← mul_assoc, hB, one_mul]
  have hABX : A * (B * X) = B * (A * X) := by
    rw [← mul_assoc, hAB, mul_assoc]
  unfold ringCommutator
  noncomm_ring [hA, hB, hAB, hJ, hJA, hJB, hJX, hJAJ, hJBJ,
    hAAX, hBBX, hABX]

/-- Doubled product-Clifford representation on the two-replica register. -/
def finiteProductCliffordDoubledGate
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (g : sigma → QubitTwoDesign.BinaryOctahedral) :
    FiniteTwoReplicaMatrix sigma :=
  finiteProductCliffordGate g ⊗ₖ finiteProductCliffordGate g

theorem finiteProductCliffordDoubledGate_singleSiteQuarterTurn
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (j : sigma) (a : Fin 3) :
    finiteProductCliffordDoubledGate
        (finiteSingleSiteQuarterTurnCode j a) =
      (1 / 2 : ℂ) •
        (1 + Complex.I •
            (finiteTwoReplicaPauliLeft (finiteSingleSitePauliLabel j a) +
              finiteTwoReplicaPauliRight (finiteSingleSitePauliLabel j a)) -
          finiteTwoReplicaPairedPauli (finiteSingleSitePauliLabel j a)) := by
  rw [finiteProductCliffordDoubledGate,
    finiteProductCliffordGate_singleSiteQuarterTurn,
    Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
    rt2inv_mul_self]
  congr 1
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  have hI : Complex.I ^ (2 : ℕ) = (-1 : ℂ) := by norm_num
  by_cases h₁ : x₁ = y₁ <;> by_cases h₂ : x₂ = y₂ <;>
    simp [finiteTwoReplicaPauliLeft, finiteTwoReplicaPauliRight,
      finiteTwoReplicaPairedPauli, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, h₁, h₂] <;>
    ring_nf <;>
    rw [hI] <;>
    simp <;>
    abel

theorem finiteTwoReplicaPauliLeft_conjTranspose
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (P : sigma → Option (Fin 3)) :
    (finiteTwoReplicaPauliLeft P)ᴴ = finiteTwoReplicaPauliLeft P := by
  have hP := finitePauliMatrix_isHermitian P
  rw [Matrix.IsHermitian] at hP
  rw [finiteTwoReplicaPauliLeft, Matrix.conjTranspose_kronecker, hP]
  simp

theorem finiteTwoReplicaPauliRight_conjTranspose
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (P : sigma → Option (Fin 3)) :
    (finiteTwoReplicaPauliRight P)ᴴ = finiteTwoReplicaPauliRight P := by
  have hP := finitePauliMatrix_isHermitian P
  rw [Matrix.IsHermitian] at hP
  rw [finiteTwoReplicaPauliRight, Matrix.conjTranspose_kronecker, hP]
  simp

theorem finiteTwoReplicaPairedPauli_conjTranspose
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (P : sigma → Option (Fin 3)) :
    (finiteTwoReplicaPairedPauli P)ᴴ = finiteTwoReplicaPairedPauli P := by
  have hP := finitePauliMatrix_isHermitian P
  rw [Matrix.IsHermitian] at hP
  rw [finiteTwoReplicaPairedPauli, Matrix.conjTranspose_kronecker, hP]

theorem finiteProductCliffordDoubledGate_singleSiteQuarterTurn_conjTranspose
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (j : sigma) (a : Fin 3) :
    (finiteProductCliffordDoubledGate
        (finiteSingleSiteQuarterTurnCode j a))ᴴ =
      (1 / 2 : ℂ) •
        (1 - Complex.I •
            (finiteTwoReplicaPauliLeft (finiteSingleSitePauliLabel j a) +
              finiteTwoReplicaPauliRight (finiteSingleSitePauliLabel j a)) -
          finiteTwoReplicaPairedPauli (finiteSingleSitePauliLabel j a)) := by
  rw [finiteProductCliffordDoubledGate_singleSiteQuarterTurn,
    Matrix.conjTranspose_smul]
  have hhalf : star (1 / 2 : ℂ) = 1 / 2 := by norm_num
  rw [hhalf]
  congr 1
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add,
    finiteTwoReplicaPauliLeft_conjTranspose,
    finiteTwoReplicaPauliRight_conjTranspose,
    finiteTwoReplicaPairedPauli_conjTranspose]
  rw [show star (Complex.I : ℂ) = -Complex.I by exact Complex.conj_I]
  module

theorem finiteProductCliffordDoubledGate_unitary
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (g : sigma → QubitTwoDesign.BinaryOctahedral) :
    (finiteProductCliffordDoubledGate g)ᴴ *
        finiteProductCliffordDoubledGate g = 1 := by
  rw [finiteProductCliffordDoubledGate,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    finiteProductCliffordGate_unitary, Matrix.one_kronecker_one]

theorem finiteProductCliffordDoubledGate_conjTranspose_eq_inv
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (g : sigma → QubitTwoDesign.BinaryOctahedral) :
    (finiteProductCliffordDoubledGate g)ᴴ =
      finiteProductCliffordDoubledGate fun s => (g s)⁻¹ := by
  rw [finiteProductCliffordDoubledGate,
    finiteProductCliffordDoubledGate,
    Matrix.conjTranspose_kronecker,
    finiteProductCliffordGate_conjTranspose_eq_inv]

/-- Doubled product-Clifford conjugation as a linear equivalence. -/
def finiteProductCliffordDoubledConjugationEquiv
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (g : sigma → QubitTwoDesign.BinaryOctahedral) :
    FiniteTwoReplicaMatrix sigma ≃ₗ[ℂ] FiniteTwoReplicaMatrix sigma :=
  unitaryMatrixConjugationEquiv (finiteProductCliffordDoubledGate g)
    (finiteProductCliffordDoubledGate_unitary g)

@[simp] theorem finiteProductCliffordDoubledConjugationEquiv_apply
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (g : sigma → QubitTwoDesign.BinaryOctahedral)
    (X : FiniteTwoReplicaMatrix sigma) :
    finiteProductCliffordDoubledConjugationEquiv g X =
      finiteProductCliffordDoubledGate g * X *
        (finiteProductCliffordDoubledGate g)ᴴ := rfl

@[simp] theorem finiteProductCliffordDoubledConjugationEquiv_symm_apply
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (g : sigma → QubitTwoDesign.BinaryOctahedral)
    (X : FiniteTwoReplicaMatrix sigma) :
    (finiteProductCliffordDoubledConjugationEquiv g).symm X =
      (finiteProductCliffordDoubledGate g)ᴴ * X *
        finiteProductCliffordDoubledGate g := rfl

theorem finiteProductCliffordDoubledConjugationEquiv_symm_eq
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (g : sigma → QubitTwoDesign.BinaryOctahedral) :
    (finiteProductCliffordDoubledConjugationEquiv g).symm =
      finiteProductCliffordDoubledConjugationEquiv fun s => (g s)⁻¹ := by
  apply LinearEquiv.ext
  intro X
  change (finiteProductCliffordDoubledGate g)ᴴ * X *
      finiteProductCliffordDoubledGate g =
    finiteProductCliffordDoubledGate (fun s => (g s)⁻¹) * X *
      (finiteProductCliffordDoubledGate (fun s => (g s)⁻¹))ᴴ
  rw [← finiteProductCliffordDoubledGate_conjTranspose_eq_inv g]
  simp

/-- Exact finite product-Clifford interpolation of every one-site collective
Casimir on an arbitrary finite register. -/
theorem finiteTwoReplicaSingleSiteCollectiveCommutator_square_groupAlgebra
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (j : sigma) (a : Fin 3) (X : FiniteTwoReplicaMatrix sigma) :
    finiteTwoReplicaCollectiveCommutatorLinear
        (finiteSingleSitePauliLabel j a)
        (finiteTwoReplicaCollectiveCommutatorLinear
          (finiteSingleSitePauliLabel j a) X) =
      (6 : ℂ) • X - (4 : ℂ) •
        (finiteProductCliffordDoubledConjugationEquiv
            (finiteSingleSiteQuarterTurnCode j a) X +
          (finiteProductCliffordDoubledConjugationEquiv
            (finiteSingleSiteQuarterTurnCode j a)).symm X) +
        (2 : ℂ) •
          (finiteTwoReplicaPairedPauli (finiteSingleSitePauliLabel j a) * X *
            finiteTwoReplicaPairedPauli (finiteSingleSitePauliLabel j a)) := by
  let P := finiteSingleSitePauliLabel j a
  let A := finiteTwoReplicaPauliLeft P
  let B := finiteTwoReplicaPauliRight P
  let R := finiteTwoReplicaPairedPauli P
  let J : FiniteTwoReplicaMatrix sigma := Complex.I • 1
  let Tp : FiniteTwoReplicaMatrix sigma := 1 + J * (A + B) - A * B
  let Tm : FiniteTwoReplicaMatrix sigma := 1 - J * (A + B) - A * B
  have hA : A * A = 1 := by
    simp [A]
  have hB : B * B = 1 := by
    simp [B]
  have hAB : A * B = B * A := by
    dsimp [A, B]
    rw [finiteTwoReplicaPauliLeft_mul_right,
      finiteTwoReplicaPauliRight_mul_left]
  have hJ : J * J = -1 := by
    dsimp [J]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    norm_num
  have hJA : J * A = A * J := by
    dsimp [J]
    rw [smul_mul_assoc, mul_smul_comm]
    simp
  have hJB : J * B = B * J := by
    dsimp [J]
    rw [smul_mul_assoc, mul_smul_comm]
    simp
  have hJX : J * X = X * J := by
    dsimp [J]
    rw [smul_mul_assoc, mul_smul_comm]
    simp
  have hcasimir := twoInvolutionQuarterTurnCasimirIdentity
    A B J X hA hB hAB hJ hJA hJB hJX
  have hR : A * B = R := by
    dsimp [A, B, R]
    rw [finiteTwoReplicaPauliLeft_mul_right]
  have hgate :
      finiteProductCliffordDoubledGate
          (finiteSingleSiteQuarterTurnCode j a) =
        (1 / 2 : ℂ) • Tp := by
    rw [finiteProductCliffordDoubledGate_singleSiteQuarterTurn]
    congr 1
    dsimp [Tp, J, A, B, R, P]
    rw [smul_mul_assoc]
    simp [finiteTwoReplicaPauliLeft_mul_right]
  have hgateAdj :
      (finiteProductCliffordDoubledGate
          (finiteSingleSiteQuarterTurnCode j a))ᴴ =
        (1 / 2 : ℂ) • Tm := by
    rw [finiteProductCliffordDoubledGate_singleSiteQuarterTurn_conjTranspose]
    congr 1
    dsimp [Tm, J, A, B, R, P]
    rw [smul_mul_assoc]
    simp [finiteTwoReplicaPauliLeft_mul_right]
  have hscale (Y Z : FiniteTwoReplicaMatrix sigma) :
      (4 : ℂ) •
          (((1 / 2 : ℂ) • Y) * X * ((1 / 2 : ℂ) • Z)) =
        Y * X * Z := by
    calc
      (4 : ℂ) • (((1 / 2 : ℂ) • Y) * X * ((1 / 2 : ℂ) • Z)) =
          ((4 : ℂ) * (1 / 2) * (1 / 2)) • (Y * X * Z) := by
            simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
            congr 1
            ring
      _ = Y * X * Z := by norm_num
  have hnatSix :
      (6 : FiniteTwoReplicaMatrix sigma) * X = (6 : ℂ) • X := by
    rw [Algebra.smul_def]
    congr 1
  have hnatTwo (Y : FiniteTwoReplicaMatrix sigma) :
      (2 : FiniteTwoReplicaMatrix sigma) * Y = (2 : ℂ) • Y := by
    rw [Algebra.smul_def]
    congr 1
  rw [finiteProductCliffordDoubledConjugationEquiv_apply,
    finiteProductCliffordDoubledConjugationEquiv_symm_apply,
    hgateAdj, hgate, smul_add, hscale Tp Tm, hscale Tm Tp]
  change finiteTwoReplicaCollectiveCommutator P
      (finiteTwoReplicaCollectiveCommutator P X) =
    (6 : ℂ) • X - (Tp * X * Tm + Tm * X * Tp) +
      (2 : ℂ) • (R * X * R)
  rw [finiteTwoReplicaCollectiveCommutator]
  rw [← ringCommutator_add_left']
  rw [finiteTwoReplicaCollectiveCommutator]
  rw [← ringCommutator_add_left']
  change ringCommutator (A + B) (ringCommutator (A + B) X) =
    (6 : ℂ) • X - (Tp * X * Tm + Tm * X * Tp) +
      (2 : ℂ) • (R * X * R)
  rw [← hR]
  rw [hnatSix, hnatTwo] at hcasimir
  exact hcasimir

/-- Product Clifford conjugation sends a collective Pauli Hamiltonian to a
scalar multiple of another collective Pauli Hamiltonian of exactly the same
support weight. -/
theorem finiteProductCliffordDoubled_conj_collectivePauli
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (g : sigma → QubitTwoDesign.BinaryOctahedral)
    (P : sigma → Option (Fin 3)) :
    ∃ P' : sigma → Option (Fin 3), ∃ c : ℂ,
      finitePauliWeight P' = finitePauliWeight P ∧
      finiteProductCliffordDoubledGate g *
          (finiteTwoReplicaPauliLeft P + finiteTwoReplicaPauliRight P) *
            (finiteProductCliffordDoubledGate g)ᴴ =
        c • (finiteTwoReplicaPauliLeft P' + finiteTwoReplicaPauliRight P') := by
  obtain ⟨P', c, hweight, hconj⟩ :=
    finiteProductCliffordGate_conj_finitePauliMatrix g P
  refine ⟨P', c, hweight, ?_⟩
  let C := finiteProductCliffordGate g
  let A := finitePauliMatrix P
  let B := finitePauliMatrix P'
  have hunit : Cᴴ * C = 1 := finiteProductCliffordGate_unitary g
  have hunit' : C * Cᴴ = 1 := mul_eq_one_comm.mp hunit
  change (C ⊗ₖ C) *
      (A ⊗ₖ (1 : Matrix (FiniteQubitConfiguration sigma)
          (FiniteQubitConfiguration sigma) ℂ) + 1 ⊗ₖ A) *
        (C ⊗ₖ C)ᴴ =
      c • (B ⊗ₖ (1 : Matrix (FiniteQubitConfiguration sigma)
          (FiniteQubitConfiguration sigma) ℂ) + 1 ⊗ₖ B)
  rw [Matrix.conjTranspose_kronecker, Matrix.mul_add, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, hunit', hconj]
  simp [B, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_add]

theorem finiteProductCliffordDoubled_conjugatedQLocalCommutator_mem_span
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (q : ℕ) (g : sigma → QubitTwoDesign.BinaryOctahedral)
    (P : FiniteQLocalPauliLabel sigma q) :
    (((finiteProductCliffordDoubledConjugationEquiv g :
        FiniteTwoReplicaMatrix sigma ≃ₗ[ℂ] FiniteTwoReplicaMatrix sigma).toLinearMap.comp
      (finiteTwoReplicaQLocalCollectiveCommutatorLinear sigma q P)).comp
      ((finiteProductCliffordDoubledConjugationEquiv g).symm :
        FiniteTwoReplicaMatrix sigma →ₗ[ℂ] FiniteTwoReplicaMatrix sigma)) ∈
      linearFamilyOperatorSpan
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear sigma q) := by
  obtain ⟨P', c, hweight, hconj⟩ :=
    finiteProductCliffordDoubled_conj_collectivePauli g P.1
  let Pq : FiniteQLocalPauliLabel sigma q := ⟨P', by
    rw [hweight]
    exact P.2⟩
  have heq :
      (((finiteProductCliffordDoubledConjugationEquiv g :
          FiniteTwoReplicaMatrix sigma ≃ₗ[ℂ] FiniteTwoReplicaMatrix sigma).toLinearMap.comp
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear sigma q P)).comp
        ((finiteProductCliffordDoubledConjugationEquiv g).symm :
          FiniteTwoReplicaMatrix sigma →ₗ[ℂ] FiniteTwoReplicaMatrix sigma)) =
        c • finiteTwoReplicaQLocalCollectiveCommutatorLinear sigma q Pq := by
    apply LinearMap.ext
    intro X
    change finiteProductCliffordDoubledGate g *
        finiteTwoReplicaCollectiveCommutator P.1
          ((finiteProductCliffordDoubledGate g)ᴴ * X *
            finiteProductCliffordDoubledGate g) *
          (finiteProductCliffordDoubledGate g)ᴴ = _
    rw [finiteTwoReplicaCollectiveCommutator,
      ← ringCommutator_add_left',
      ringCommutator_unitary_conjugation _ _ _
        (finiteProductCliffordDoubledGate_unitary g),
      hconj, ringCommutator_smul_left, ringCommutator_add_left']
    rfl
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Pq, rfl⟩)

/-- For every finite register and every locality threshold, the canonical
greatest Hall obstruction is fixed by every product Clifford. -/
theorem finiteTwoReplicaQLocal_greatestMaximizer_productClifford_fixed
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (q : ℕ) (U : Submodule ℂ (FiniteTwoReplicaMatrix sigma))
    (hgreatest : ∀ V : Submodule ℂ (FiniteTwoReplicaMatrix sigma),
      linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear sigma q) V =
        linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear sigma q) U →
      V ≤ U)
    (g : sigma → QubitTwoDesign.BinaryOctahedral) :
    U.map (finiteProductCliffordDoubledConjugationEquiv g :
      FiniteTwoReplicaMatrix sigma →ₗ[ℂ] FiniteTwoReplicaMatrix sigma) = U := by
  apply linearFamilyDefect_greatestMaximizer_map_eq_of_spanCovariant
      (finiteTwoReplicaQLocalCollectiveCommutatorLinear sigma q) U
      (finiteProductCliffordDoubledConjugationEquiv g)
      (finiteProductCliffordDoubledConjugationEquiv g) hgreatest
  · exact fun P =>
      finiteProductCliffordDoubled_conjugatedQLocalCommutator_mem_span q g P
  · intro P
    simpa only [finiteProductCliffordDoubledConjugationEquiv_symm_eq,
      inv_inv] using
      finiteProductCliffordDoubled_conjugatedQLocalCommutator_mem_span q
        (fun s => (g s)⁻¹) P

/-- Every one-site collective-Casimir summand preserves the canonical
greatest weight-at-most-`q` Hall obstruction, for every finite register and
every locality threshold `q`. -/
theorem finiteTwoReplicaSingleSiteCollectiveCommutator_square_mem_greatestMaximizer
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (q : ℕ) (U : Submodule ℂ (FiniteTwoReplicaMatrix sigma))
    (hgreatest : ∀ V : Submodule ℂ (FiniteTwoReplicaMatrix sigma),
      linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear sigma q) V =
        linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear sigma q) U →
      V ≤ U)
    (j : sigma) (a : Fin 3) {X : FiniteTwoReplicaMatrix sigma}
    (hX : X ∈ U) :
    finiteTwoReplicaCollectiveCommutatorLinear
        (finiteSingleSitePauliLabel j a)
        (finiteTwoReplicaCollectiveCommutatorLinear
          (finiteSingleSitePauliLabel j a) X) ∈ U := by
  have hmap (g : sigma → QubitTwoDesign.BinaryOctahedral) :
      finiteProductCliffordDoubledConjugationEquiv g X ∈ U := by
    rw [← finiteTwoReplicaQLocal_greatestMaximizer_productClifford_fixed
      q U hgreatest g]
    exact ⟨X, hX, rfl⟩
  have hquarter :
      finiteProductCliffordDoubledConjugationEquiv
        (finiteSingleSiteQuarterTurnCode j a) X ∈ U := hmap _
  have hquarterInv :
      (finiteProductCliffordDoubledConjugationEquiv
        (finiteSingleSiteQuarterTurnCode j a)).symm X ∈ U := by
    rw [finiteProductCliffordDoubledConjugationEquiv_symm_eq]
    exact hmap _
  have hpaired :
      finiteTwoReplicaPairedPauli (finiteSingleSitePauliLabel j a) * X *
        finiteTwoReplicaPairedPauli (finiteSingleSitePauliLabel j a) ∈ U := by
    have hm :
        finiteTwoReplicaPairedPauliConjugationLinear
          (finiteSingleSitePauliLabel j a) X ∈ U := by
      rw [← finiteTwoReplicaQLocal_greatestMaximizer_fixed
        q U hgreatest (finiteSingleSitePauliLabel j a)]
      exact ⟨X, hX, rfl⟩
    exact hm
  rw [finiteTwoReplicaSingleSiteCollectiveCommutator_square_groupAlgebra]
  exact U.add_mem
    (U.sub_mem (U.smul_mem _ hX)
      (U.smul_mem _ (U.add_mem hquarter hquarterInv)))
    (U.smul_mem _ hpaired)

end

end GaloisForLFunctions.HTGeometry
