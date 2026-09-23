import GaloisForLFunctions.RHTower.GaussianHermitianPencilSpectralActionLaw
import GaloisForLFunctions.HTGeometry.NearestNeighborGaussianSameDrawGrowthLaw

/-!
# Quenched spectral action law for nearest-neighbour static Hamiltonians

The universal Gaussian-pencil law is specialized to the exact ordinary
nearest-neighbour path ensemble already used by the same-draw laboratory
growth theorem.
-/

open scoped BigOperators Matrix ComplexConjugate
open Matrix MeasureTheory ProbabilityTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open GaloisForLFunctions.RHTower

noncomputable section

/-- The ordinary nearest-neighbour Hamiltonian family as a certified real
linear Hermitian Gaussian pencil. -/
def nearestNeighborPathGaussianHermitianPencil (L : ℕ) :
    FiniteGaussianHermitianPencil
      (EuclideanSpace ℝ (Fin (nearestNeighborPathLocalParameterCount L)))
      (Config (PairQubit L)) where
  hamiltonian :=
    { toFun := fun x => nearestNeighborPathLocalHamiltonian L (WithLp.ofLp x)
      map_add' := by
        intro x y
        ext a b
        simp [nearestNeighborPathLocalHamiltonian, realAffineMatrix,
          Matrix.add_apply]
        simp_rw [add_mul]
        exact Finset.sum_add_distrib
      map_smul' := by
        intro r x
        ext a b
        simp [nearestNeighborPathLocalHamiltonian, realAffineMatrix,
          Matrix.smul_apply, Finset.mul_sum]
        ring_nf }
  isHermitian := fun x =>
    nearestNeighborPathLocalHamiltonian_isHermitian L (WithLp.ofLp x)

@[simp] theorem nearestNeighborPathGaussianHermitianPencil_hamiltonian
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :
    (nearestNeighborPathGaussianHermitianPencil L).hamiltonian
        (WithLp.toLp 2 p) =
      nearestNeighborPathLocalHamiltonian L p := rfl

/-- Exact observer Jacobian for the ordinary nearest-neighbour path ensemble. -/
abbrev nearestNeighborPathCommutatorMap
    (L : ℕ) (U : Matrix.unitaryGroup (Config (PairQubit L)) ℂ) :=
  (nearestNeighborPathGaussianHermitianPencil L).commutatorMap U

/-- **Nearest-neighbour quenched growing-replica law.**  Canonical physical
optimal-design weights are fixed before one ordinary time-independent local
Hamiltonian is drawn.  Excess spectral near-action is bounded by exact
endpoint-wise nearest-neighbour observer-Jacobian stable ranks, with no
circuit union and no spectral-gap premise. -/
theorem stdGaussian_nearestNeighborPath_measure_optimalDesignNearAction_gap_le
    {L : ℕ}
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ)
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian
      (EuclideanSpace ℝ (Fin (nearestNeighborPathLocalParameterCount L)))).real
        {x |
          (∑ c, finiteUnitaryChoiOptimalDesignWeight r U c *
            staticChoiAdaptiveReplicaBase
              ((nearestNeighborPathGaussianHermitianPencil L).spectralEnergy x)
              ((Fintype.card (Config (PairQubit L)) : ℝ)⁻¹ *
                (nearestNeighborPathGaussianHermitianPencil L).commutatorActivation (U c)) ^ r) + κ ≤
          ∑ c, finiteUnitaryChoiOptimalDesignWeight r U c *
            directStaticChoiTargetNearActionMass
              (choiVector
                ((nearestNeighborPathGaussianHermitianPencil L).spectralEndpoint x (U c) :
                  Matrix (Fin (Fintype.card (Config (PairQubit L))))
                    (Fin (Fintype.card (Config (PairQubit L)))) ℂ))
              ((nearestNeighborPathGaussianHermitianPencil L).spectralEnergy x) r δ} ≤
      (∑ c, finiteUnitaryChoiOptimalDesignWeight r U c * Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          ((∑ i : Fin (Module.finrank ℝ
                (EuclideanSpace ℝ (Fin (nearestNeighborPathLocalParameterCount L)))),
              (nearestNeighborPathCommutatorMap L (U c)).singularValues i ^ (2 : ℕ)) ^ (2 : ℕ) /
            ∑ i : Fin (Module.finrank ℝ
                (EuclideanSpace ℝ (Fin (nearestNeighborPathLocalParameterCount L)))),
              (nearestNeighborPathCommutatorMap L (U c)).singularValues i ^ (4 : ℕ)))) / κ := by
  letI : Nonempty (Config (PairQubit L)) :=
    ⟨fun _ => false⟩
  exact FiniteGaussianHermitianPencil.stdGaussian_measure_optimalDesignNearAction_gap_le
    (nearestNeighborPathGaussianHermitianPencil L) r U δ hκ

end

end RHTower
