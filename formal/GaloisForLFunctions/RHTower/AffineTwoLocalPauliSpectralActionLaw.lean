import GaloisForLFunctions.RHTower.GaussianAffineHermitianPencilSpectralActionLaw
import GaloisForLFunctions.RHTower.GaussianScaledAffineHermitianPencilSpectralActionLaw
import GaloisForLFunctions.HTGeometry.PauliCommutatorGramStableRankFloor
import GaloisForLFunctions.HTGeometry.TwoLocalPauliGaussianEnergyCap

/-!
# Affine ordinary two-local spectral action law

An arbitrary deterministic Hermitian seed plus one ordinary all-to-all
two-local Gaussian Pauli perturbation has dimension-linear observer
anti-concentration against every endpoint outside projective scalar
recurrence.  Drift does not enter the exponent.
-/

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator
open Matrix Set MeasureTheory ProbabilityTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Ordinary two-local Pauli Gaussian Hamiltonians as a certified Hermitian
linear pencil. -/
def twoLocalPauliGaussianHermitianPencil (n : ℕ) :
    FiniteGaussianHermitianPencil
      (TwoLocalPauliCoefficientSpace n)
      (FiniteQubitConfiguration (Fin n)) where
  hamiltonian :=
    { toFun := realActivePauliHamiltonian
      map_add' := realActivePauliHamiltonian_add
      map_smul' := by
        intro r x
        exact realActivePauliHamiltonian_smul r x }
  isHermitian := fun x =>
    Matrix.isHermitian_iff_isSelfAdjoint.mpr
      (isSelfAdjoint_realActivePauliHamiltonian x)

@[simp] theorem twoLocalPauliGaussianHermitianPencil_hamiltonian
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) :
    (twoLocalPauliGaussianHermitianPencil n).hamiltonian x =
      realActivePauliHamiltonian x := rfl

theorem twoLocalPauliGaussianHermitianPencil_commutatorMap
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    (twoLocalPauliGaussianHermitianPencil n).commutatorMap U =
      twoLocalPauliUnitaryCommutatorMap U := by
  rfl

/-- Exact stable-rank ratio of the ordinary two-local pencil observer. -/
theorem twoLocalPauliGaussianHermitianPencil_stableRatio
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    ((∑ i : Fin (Module.finrank ℝ (TwoLocalPauliCoefficientSpace n)),
        ((twoLocalPauliGaussianHermitianPencil n).commutatorMap U).singularValues i ^ (2 : ℕ)) ^ (2 : ℕ) /
      ∑ i : Fin (Module.finrank ℝ (TwoLocalPauliCoefficientSpace n)),
        ((twoLocalPauliGaussianHermitianPencil n).commutatorMap U).singularValues i ^ (4 : ℕ)) =
      twoLocalPauliUnitaryCommutatorGramStableRatio U := by
  rw [twoLocalPauliGaussianHermitianPencil_commutatorMap]
  rw [show Module.finrank ℝ (TwoLocalPauliCoefficientSpace n) =
      Fintype.card (PauliTracelessLabel n 2) from finrank_euclideanSpace]
  rfl

/-- Projective trace deficit: zero exactly on scalar unitary recurrence and
positive away from that common channel. -/
def unitaryProjectiveTraceDeficit
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) : ℝ :=
  1 - ‖Matrix.trace
      (U : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)‖ ^ (2 : ℕ) / ((2 : ℝ) ^ n) ^ (2 : ℕ)

/-- Dimension-linear stable-rank floor, expressed only through physical
distance from projective scalar recurrence. -/
theorem twoLocalPauliGaussianHermitianPencil_stableRatio_ge_projectiveTraceDeficit
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    ((6 * n - 4 : ℕ) : ℝ) * unitaryProjectiveTraceDeficit U ≤
      ((∑ i : Fin (Module.finrank ℝ (TwoLocalPauliCoefficientSpace n)),
          ((twoLocalPauliGaussianHermitianPencil n).commutatorMap U).singularValues i ^ (2 : ℕ)) ^ (2 : ℕ) /
        ∑ i : Fin (Module.finrank ℝ (TwoLocalPauliCoefficientSpace n)),
          ((twoLocalPauliGaussianHermitianPencil n).commutatorMap U).singularValues i ^ (4 : ℕ)) := by
  rw [twoLocalPauliGaussianHermitianPencil_stableRatio]
  exact twoLocalPauliUnitaryCommutatorGramStableRatio_ge_sixNSubFour_normalizedTraceDeficit U

/-- **Affine two-local dimension-linear quenched law.**  Canonical endpoint
weights are fixed before one two-local Gaussian perturbation is drawn.  For
every deterministic Hermitian seed, excess same-draw spectral near-action is
exponentially suppressed in qubit count times exact projective trace deficit;
only the common scalar recurrence channel has zero exponent. -/
theorem stdGaussian_measure_optimalDesignAffineTwoLocalNearAction_gap_le_traceDeficit
    {n : ℕ}
    {H₀ : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ} (hH₀ : H₀.IsHermitian)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ)
    (U : C → Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        {x |
          (∑ c, finiteUnitaryChoiOptimalDesignWeight r U c *
            staticChoiAdaptiveReplicaBase
              ((twoLocalPauliGaussianHermitianPencil n).affineSpectralEnergy hH₀ x)
              ((Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
                (twoLocalPauliGaussianHermitianPencil n).commutatorActivation (U c)) ^ r) + κ ≤
          ∑ c, finiteUnitaryChoiOptimalDesignWeight r U c *
            directStaticChoiTargetNearActionMass
              (choiVector
                ((twoLocalPauliGaussianHermitianPencil n).affineSpectralEndpoint hH₀ x (U c) :
                  Matrix (Fin (Fintype.card (FiniteQubitConfiguration (Fin n))))
                    (Fin (Fintype.card (FiniteQubitConfiguration (Fin n)))) ℂ))
              ((twoLocalPauliGaussianHermitianPencil n).affineSpectralEnergy hH₀ x) r δ} ≤
      (∑ c, finiteUnitaryChoiOptimalDesignWeight r U c *
        Real.exp (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          (((6 * n - 4 : ℕ) : ℝ) * unitaryProjectiveTraceDeficit (U c)))) / κ := by
  have hbase :=
    FiniteGaussianHermitianPencil.stdGaussian_measure_optimalDesignAffineNearAction_gap_le
      (twoLocalPauliGaussianHermitianPencil n) hH₀ r U δ hκ
  apply hbase.trans
  apply div_le_div_of_nonneg_right _ hκ.le
  apply Finset.sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_left _
    ((finiteUnitaryChoiOptimalDesignWeight_mem_stdSimplex r U).1 c)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonpos_left
    (twoLocalPauliGaussianHermitianPencil_stableRatio_ge_projectiveTraceDeficit
      (U c))
  exact neg_nonpos.mpr (by positivity)

/-- **Weak-noise two-local fusion law.**  The deterministic seed may be
perturbed at any nonzero scale.  Activation shrinks quadratically with that
scale, but the quenched exponent remains dimension-linear and completely
scale-free away from projective scalar recurrence. -/
theorem stdGaussian_measure_optimalDesignScaledAffineTwoLocalNearAction_gap_le_traceDeficit
    {n : ℕ}
    {H₀ : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ} (hH₀ : H₀.IsHermitian)
    {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ)
    (U : C → Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        {x |
          (∑ c, finiteUnitaryChoiOptimalDesignWeight r U c *
            staticChoiAdaptiveReplicaBase
              ((twoLocalPauliGaussianHermitianPencil n).scaledAffineSpectralEnergy
                hH₀ scale x)
              ((Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
                (scale ^ (2 : ℕ) *
                  (twoLocalPauliGaussianHermitianPencil n).commutatorActivation
                    (U c))) ^ r) + κ ≤
          ∑ c, finiteUnitaryChoiOptimalDesignWeight r U c *
            directStaticChoiTargetNearActionMass
              (choiVector
                ((twoLocalPauliGaussianHermitianPencil n).scaledAffineSpectralEndpoint
                    hH₀ scale x (U c) :
                  Matrix (Fin (Fintype.card (FiniteQubitConfiguration (Fin n))))
                    (Fin (Fintype.card (FiniteQubitConfiguration (Fin n)))) ℂ))
              ((twoLocalPauliGaussianHermitianPencil n).scaledAffineSpectralEnergy
                hH₀ scale x) r δ} ≤
      (∑ c, finiteUnitaryChoiOptimalDesignWeight r U c *
        Real.exp (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          (((6 * n - 4 : ℕ) : ℝ) * unitaryProjectiveTraceDeficit (U c)))) / κ := by
  have hbase :=
    FiniteGaussianHermitianPencil.stdGaussian_measure_optimalDesignScaledAffineNearAction_gap_le
        (twoLocalPauliGaussianHermitianPencil n) hH₀ hscale r U δ hκ
  apply hbase.trans
  apply div_le_div_of_nonneg_right _ hκ.le
  apply Finset.sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_left _
    ((finiteUnitaryChoiOptimalDesignWeight_mem_stdSimplex r U).1 c)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonpos_left
    (twoLocalPauliGaussianHermitianPencil_stableRatio_ge_projectiveTraceDeficit
      (U c))
  exact neg_nonpos.mpr (by positivity)

end

end RHTower
