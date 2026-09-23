import GaloisForLFunctions.RHTower.StaticChoiPhysicalActionTransportLaw
import GaloisForLFunctions.HTGeometry.GaussianWeightedObserverTubeLaw
import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarReindex

/-!
# Universal quenched spectral action law for Gaussian Hermitian pencils

For every finite-dimensional real Gaussian Hermitian pencil, every finite
unitary endpoint family, and every replica order, same-draw spectral
near-action splits into exact endpoint-adaptive transverse decay and literal
probability-design mass inside observer-commutator half-activation tubes.
The quenched lower tail is governed only by exact observer-Jacobian stable
ranks.  No special Pauli structure, spectral gap, eigenbasis choice, or
endpoint union enters.
-/

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator
open Matrix Set MeasureTheory ProbabilityTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Certified finite Gaussian Hermitian pencil.  Hermiticity is part of the
object, so every theorem below is unconditional for every such pencil. -/
structure FiniteGaussianHermitianPencil
    (E ι : Type*) [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  hamiltonian : E →ₗ[ℝ] Matrix ι ι ℂ
  isHermitian : ∀ x, (hamiltonian x).IsHermitian

variable {E ι : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Observer Jacobian of a Gaussian Hermitian pencil at a unitary endpoint. -/
def FiniteGaussianHermitianPencil.commutatorMap
    (P : FiniteGaussianHermitianPencil E ι)
    (U : Matrix.unitaryGroup ι ℂ) :
    E →ₗ[ℝ] EuclideanSpace ℂ (ι × ι) where
  toFun x := matVec
    (P.hamiltonian x * (U : Matrix ι ι ℂ) -
      (U : Matrix ι ι ℂ) * P.hamiltonian x)
  map_add' x y := by
    rw [P.hamiltonian.map_add]
    have hmatrix :
        (P.hamiltonian x + P.hamiltonian y) * (U : Matrix ι ι ℂ) -
            (U : Matrix ι ι ℂ) * (P.hamiltonian x + P.hamiltonian y) =
          (P.hamiltonian x * (U : Matrix ι ι ℂ) -
              (U : Matrix ι ι ℂ) * P.hamiltonian x) +
            (P.hamiltonian y * (U : Matrix ι ι ℂ) -
              (U : Matrix ι ι ℂ) * P.hamiltonian y) := by
      noncomm_ring
    rw [hmatrix]
    rfl
  map_smul' r x := by
    rw [P.hamiltonian.map_smul]
    rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
    rfl

/-- Numbered Hamiltonian in canonical finite coordinates. -/
def FiniteGaussianHermitianPencil.reindexedHamiltonian
    (P : FiniteGaussianHermitianPencil E ι) (x : E) :
    Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι) (P.hamiltonian x)

omit [FiniteDimensional ℝ E] in
theorem FiniteGaussianHermitianPencil.reindexedHamiltonian_isHermitian
    (P : FiniteGaussianHermitianPencil E ι) (x : E) :
    (P.reindexedHamiltonian x).IsHermitian := by
  simpa [FiniteGaussianHermitianPencil.reindexedHamiltonian,
    Matrix.coe_reindexAlgEquiv] using
    (P.isHermitian x).reindex (Fintype.equivFin ι)

/-- Numbered physical endpoint, without changing its unitary geometry. -/
def finiteGaussianHermitianPencilReindexedEndpoint
    (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup (Fin (Fintype.card ι)) ℂ :=
  unitaryGroupReindex (Fintype.equivFin ι) U

/-- Endpoint in the eigenbasis of the same Gaussian Hamiltonian draw. -/
def FiniteGaussianHermitianPencil.spectralEndpoint
    (P : FiniteGaussianHermitianPencil E ι) (x : E)
    (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup (Fin (Fintype.card ι)) ℂ :=
  hermitianSpectralEndpoint (P.reindexedHamiltonian_isHermitian x)
    (finiteGaussianHermitianPencilReindexedEndpoint U)

/-- Spectrum of the same numbered Hamiltonian draw. -/
def FiniteGaussianHermitianPencil.spectralEnergy
    (P : FiniteGaussianHermitianPencil E ι) (x : E) :
    Fin (Fintype.card ι) → ℝ :=
  (P.reindexedHamiltonian_isHermitian x).eigenvalues

/-- Exact half-activation energy of an endpoint's observer Jacobian. -/
def FiniteGaussianHermitianPencil.commutatorActivation
    (P : FiniteGaussianHermitianPencil E ι)
    (U : Matrix.unitaryGroup ι ℂ) : ℝ :=
  (gaussianIntervalActivationMass / 2) *
    ∑ i : Fin (Module.finrank ℝ E),
      (P.commutatorMap U).singularValues i ^ (2 : ℕ)

theorem finiteMatrixHilbertSchmidtEnergy_eq_hsNorm_sq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℂ) :
    finiteMatrixHilbertSchmidtEnergy A = hsNorm A ^ (2 : ℕ) := by
  rw [finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq, hsNorm_sq,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (Complex.sq_norm (A i j)).symm

theorem finiteMatrixHilbertSchmidtEnergy_reindexAlgEquiv
    {κ κ' : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype κ'] [DecidableEq κ']
    (e : κ ≃ κ') (A : Matrix κ κ ℂ) :
    finiteMatrixHilbertSchmidtEnergy
        (Matrix.reindexAlgEquiv ℂ ℂ e A) =
      finiteMatrixHilbertSchmidtEnergy A := by
  rw [finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq,
    finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq]
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  have hinner (i : κ') :
      (∑ j : κ', Complex.normSq (A (e.symm j) (e.symm i))) =
        ∑ j : κ, Complex.normSq (A j (e.symm i)) := by
    exact Equiv.sum_comp e.symm (fun j : κ => Complex.normSq (A j (e.symm i)))
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  exact Equiv.sum_comp e.symm (fun i : κ => ∑ j, Complex.normSq (A j i))

omit [FiniteDimensional ℝ E] in
/-- Exact physical realization: the numbered commutator energy is the squared
norm of the original observer Jacobian on the same draw. -/
theorem FiniteGaussianHermitianPencil.reindexedCommutatorEnergy
    (P : FiniteGaussianHermitianPencil E ι) (x : E)
    (U : Matrix.unitaryGroup ι ℂ) :
    finiteMatrixHilbertSchmidtEnergy
        (P.reindexedHamiltonian x *
            (finiteGaussianHermitianPencilReindexedEndpoint U :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) -
          (finiteGaussianHermitianPencilReindexedEndpoint U :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) *
            P.reindexedHamiltonian x) =
      ‖P.commutatorMap U x‖ ^ (2 : ℕ) := by
  have hmatrix :
      P.reindexedHamiltonian x *
            (finiteGaussianHermitianPencilReindexedEndpoint U :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) -
          (finiteGaussianHermitianPencilReindexedEndpoint U :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) *
            P.reindexedHamiltonian x =
        Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι)
          (P.hamiltonian x * (U : Matrix ι ι ℂ) -
            (U : Matrix ι ι ℂ) * P.hamiltonian x) := by
    change
      Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι) (P.hamiltonian x) *
          Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι) (U : Matrix ι ι ℂ) -
        Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι) (U : Matrix ι ι ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι) (P.hamiltonian x) = _
    rw [← map_mul, ← map_mul, ← map_sub]
  rw [hmatrix, finiteMatrixHilbertSchmidtEnergy_reindexAlgEquiv,
    finiteMatrixHilbertSchmidtEnergy_eq_hsNorm_sq]
  rfl

theorem FiniteGaussianHermitianPencil.mem_halfActivationTube_iff
    (P : FiniteGaussianHermitianPencil E ι) (x : E)
    (U : Matrix.unitaryGroup ι ℂ) :
    x ∈ gaussianHalfActivationTube
        (n := Module.finrank ℝ E) (P.commutatorMap U) ↔
      ‖P.commutatorMap U x‖ ^ (2 : ℕ) ≤ P.commutatorActivation U := by
  rfl

/-- **Universal same-draw pointwise action--carrier law.** -/
theorem FiniteGaussianHermitianPencil.nearAction_le_adaptive_add_carrier
    [Nonempty ι]
    (P : FiniteGaussianHermitianPencil E ι) (x : E)
    (U : Matrix.unitaryGroup ι ℂ) (r : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass
        (choiVector
          (P.spectralEndpoint x U :
            Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
        (P.spectralEnergy x) r δ ≤
      staticChoiAdaptiveReplicaBase (P.spectralEnergy x)
          ((Fintype.card ι : ℝ)⁻¹ * P.commutatorActivation U) ^ r +
        if x ∈ gaussianHalfActivationTube
            (n := Module.finrank ℝ E) (P.commutatorMap U)
          then 1 else 0 := by
  have h :=
    directStaticChoiTargetNearActionMass_hermitianSpectralEndpoint_le_adaptivePhysicalAction
      (d := Fintype.card ι) Fintype.card_pos
      (P.reindexedHamiltonian_isHermitian x)
      (finiteGaussianHermitianPencilReindexedEndpoint U) r δ
      (P.commutatorActivation U)
  rw [P.reindexedCommutatorEnergy x U] at h
  by_cases hc : ‖P.commutatorMap U x‖ ^ (2 : ℕ) ≤ P.commutatorActivation U
  · rw [if_pos hc] at h
    rw [if_pos]
    · simpa [FiniteGaussianHermitianPencil.spectralEndpoint,
        FiniteGaussianHermitianPencil.spectralEnergy] using h
    · exact (P.mem_halfActivationTube_iff x U).2 hc
  · rw [if_neg hc] at h
    rw [if_neg]
    · simpa [FiniteGaussianHermitianPencil.spectralEndpoint,
        FiniteGaussianHermitianPencil.spectralEnergy] using h
    · exact fun hx => hc ((P.mem_halfActivationTube_iff x U).1 hx)

/-- Universal probability-design action--carrier law, pointwise in the same draw. -/
theorem FiniteGaussianHermitianPencil.weightedNearAction_le_transverse_add_tubeMass
    [Nonempty ι]
    (P : FiniteGaussianHermitianPencil E ι)
    {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup ι ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (x : E) (r : ℕ) (δ : ℝ) :
    (∑ c, w c * directStaticChoiTargetNearActionMass
        (choiVector
          (P.spectralEndpoint x (U c) :
            Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
        (P.spectralEnergy x) r δ) ≤
      (∑ c, w c * staticChoiAdaptiveReplicaBase (P.spectralEnergy x)
        ((Fintype.card ι : ℝ)⁻¹ * P.commutatorActivation (U c)) ^ r) +
      gaussianWeightedHalfActivationTubeMass
        (n := Module.finrank ℝ E) (fun c => P.commutatorMap (U c)) w x := by
  calc
    _ ≤ ∑ c, w c *
        (staticChoiAdaptiveReplicaBase (P.spectralEnergy x)
            ((Fintype.card ι : ℝ)⁻¹ * P.commutatorActivation (U c)) ^ r +
          if x ∈ gaussianHalfActivationTube
              (n := Module.finrank ℝ E) (P.commutatorMap (U c))
            then 1 else 0) := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left
        (P.nearAction_le_adaptive_add_carrier x (U c) r δ) (hw.1 c)
    _ = _ := by
      unfold gaussianWeightedHalfActivationTubeMass
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1

/-- **Universal quenched growing-replica law.**  For every finite Gaussian
Hermitian pencil, excess same-draw spectral near-action is controlled by the
exact design-averaged observer-Jacobian stable ranks. -/
theorem FiniteGaussianHermitianPencil.stdGaussian_measure_weightedNearAction_gap_le
    [Nonempty ι] [MeasurableSpace E] [BorelSpace E]
    (P : FiniteGaussianHermitianPencil E ι)
    {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup ι ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (r : ℕ) (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian E).real
        {x |
          (∑ c, w c * staticChoiAdaptiveReplicaBase (P.spectralEnergy x)
            ((Fintype.card ι : ℝ)⁻¹ * P.commutatorActivation (U c)) ^ r) + κ ≤
          ∑ c, w c * directStaticChoiTargetNearActionMass
            (choiVector
              (P.spectralEndpoint x (U c) :
                Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
            (P.spectralEnergy x) r δ} ≤
      (∑ c, w c * Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          ((∑ i : Fin (Module.finrank ℝ E),
              (P.commutatorMap (U c)).singularValues i ^ (2 : ℕ)) ^ (2 : ℕ) /
            ∑ i : Fin (Module.finrank ℝ E),
              (P.commutatorMap (U c)).singularValues i ^ (4 : ℕ)))) / κ := by
  apply (measureReal_mono ?_).trans
    (stdGaussian_measure_weightedHalfActivationTubeMass_ge_le
      (n := Module.finrank ℝ E) (fun c => P.commutatorMap (U c))
      (by rfl) w hw hκ)
  intro x hx
  have hdet := P.weightedNearAction_le_transverse_add_tubeMass U w hw x r δ
  change κ ≤ gaussianWeightedHalfActivationTubeMass
    (n := Module.finrank ℝ E) (fun c => P.commutatorMap (U c)) w x
  change _ + κ ≤ _ at hx
  linarith

/-- Physical normalized Choi dictionary for an arbitrary finite carrier. -/
noncomputable def finiteUnitaryChoiTarget
    {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup ι ℂ) : C → (ι × ι) → ℂ :=
  fun c => (choiVector (U c : Matrix ι ι ℂ)).ofLp

theorem finiteUnitaryChoiTarget_normalized
    [Nonempty ι]
    {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup ι ℂ) :
    ∀ c, finiteComplexInner
      (finiteUnitaryChoiTarget U c) (finiteUnitaryChoiTarget U c) = 1 :=
  fun c => finiteComplexInner_ofLp_self_eq_one_of_norm_eq_one
    (choiVector (U c : Matrix ι ι ℂ))
    (norm_choiVector_eq_one Fintype.card_pos
      (Unitary.coe_star_mul_self (U c)))

/-- Determinant-optimal physical Choi weights selected before the Gaussian
Hamiltonian draw, for every finite carrier and endpoint dictionary. -/
noncomputable def finiteUnitaryChoiOptimalDesignWeight
    [Nonempty ι]
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup ι ℂ) : C → ℝ :=
  replicaTargetOptimalDesignWeight r
    (finiteUnitaryChoiTarget U) (finiteUnitaryChoiTarget_normalized U)

theorem finiteUnitaryChoiOptimalDesignWeight_mem_stdSimplex
    [Nonempty ι]
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup ι ℂ) :
    finiteUnitaryChoiOptimalDesignWeight r U ∈ stdSimplex ℝ C :=
  replicaTargetOptimalDesignWeight_mem_stdSimplex r
    (finiteUnitaryChoiTarget U) (finiteUnitaryChoiTarget_normalized U)

/-- **Universal pre-draw optimal-design quenched law.**  This is the closed
probability-design specialization: for every finite Gaussian Hermitian
pencil and every finite nonempty unitary endpoint image, canonical physical
weights are fixed before the draw and no endpoint-cardinality factor occurs. -/
theorem FiniteGaussianHermitianPencil.stdGaussian_measure_optimalDesignNearAction_gap_le
    [Nonempty ι] [MeasurableSpace E] [BorelSpace E]
    (P : FiniteGaussianHermitianPencil E ι)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup ι ℂ)
    (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian E).real
        {x |
          (∑ c, finiteUnitaryChoiOptimalDesignWeight r U c *
            staticChoiAdaptiveReplicaBase (P.spectralEnergy x)
              ((Fintype.card ι : ℝ)⁻¹ * P.commutatorActivation (U c)) ^ r) + κ ≤
          ∑ c, finiteUnitaryChoiOptimalDesignWeight r U c *
            directStaticChoiTargetNearActionMass
              (choiVector
                (P.spectralEndpoint x (U c) :
                  Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
              (P.spectralEnergy x) r δ} ≤
      (∑ c, finiteUnitaryChoiOptimalDesignWeight r U c * Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          ((∑ i : Fin (Module.finrank ℝ E),
              (P.commutatorMap (U c)).singularValues i ^ (2 : ℕ)) ^ (2 : ℕ) /
            ∑ i : Fin (Module.finrank ℝ E),
              (P.commutatorMap (U c)).singularValues i ^ (4 : ℕ)))) / κ := by
  exact P.stdGaussian_measure_weightedNearAction_gap_le U
    (finiteUnitaryChoiOptimalDesignWeight r U)
    (finiteUnitaryChoiOptimalDesignWeight_mem_stdSimplex r U) r δ hκ

end

end RHTower
