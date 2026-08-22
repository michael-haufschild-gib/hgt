import GaloisForLFunctions.HTGeometry.GaussianStableRankLowerTail
import GaloisForLFunctions.HTGeometry.PureReplicaCollectiveEnergyLaw

/-!
# Pure-replica Gaussian stable-rank barrier

Replica lifting cannot create new independent Gaussian Hamiltonian directions.
For a normalized physical pure-projector boundary, collective `r`-replica
commutator energy multiplies every generator weight by the same factor `r`.
The Gaussian stable ratio is homogeneous of degree zero, so its lower-tail
exponent is exactly unchanged for every positive replica order and is always
bounded by the number of independent generators.

Thus growing replicas can compress target fidelity and occupied-image geometry,
but cannot amplify source-side stable-rank anti-concentration.  Any complete
circuit theorem must instead control occupied-image/coarea fibre-sheet mass
after return removal.
-/

open Matrix
open scoped BigOperators ENNReal NNReal ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Stable ratio of nonnegative Gaussian generator weights. -/
def gaussianWeightStableRatio
    {I : Type*} [Fintype I] (weight : I → ℝ≥0) : ℝ :=
  (∑ i, (weight i : ℝ)) ^ 2 / ∑ i, (weight i : ℝ) ^ 2

theorem gaussianWeightStableRatio_nonneg
    {I : Type*} [Fintype I] (weight : I → ℝ≥0) :
    0 ≤ gaussianWeightStableRatio weight := by
  unfold gaussianWeightStableRatio
  positivity

/-- Stable-rank anti-concentration cannot exceed the number of independent
Gaussian coordinates. -/
theorem gaussianWeightStableRatio_le_card
    {I : Type*} [Fintype I] (weight : I → ℝ≥0) :
    gaussianWeightStableRatio weight ≤ Fintype.card I := by
  unfold gaussianWeightStableRatio
  let Q : ℝ := ∑ i, (weight i : ℝ) ^ 2
  by_cases hQ : Q = 0
  · simp [Q, hQ]
  · have hQ0 : 0 < Q := lt_of_le_of_ne (by positivity) (Ne.symm hQ)
    rw [div_le_iff₀ hQ0]
    simpa [Q] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset I)) (f := fun i => (weight i : ℝ)))

/-- Stable ratio is invariant under every nonzero common rescaling. -/
theorem gaussianWeightStableRatio_scale
    {I : Type*} [Fintype I] (weight : I → ℝ≥0)
    (a : ℝ≥0) (ha : a ≠ 0) :
    gaussianWeightStableRatio (fun i => a * weight i) =
      gaussianWeightStableRatio weight := by
  unfold gaussianWeightStableRatio
  have hsum : (∑ i, ((a * weight i : ℝ≥0) : ℝ)) =
      (a : ℝ) * ∑ i, (weight i : ℝ) := by
    simp [Finset.mul_sum]
  have hsq : (∑ i, ((a * weight i : ℝ≥0) : ℝ) ^ 2) =
      (a : ℝ) ^ 2 * ∑ i, (weight i : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  rw [hsum, hsq]
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  by_cases hQ : (∑ i, (weight i : ℝ) ^ 2) = 0
  · simp [hQ]
  · field_simp

theorem gaussianWeightStableRatio_natScale
    {I : Type*} [Fintype I] (weight : I → ℝ≥0)
    {r : ℕ} (hr : 0 < r) :
    gaussianWeightStableRatio (fun i => (r : ℝ≥0) * weight i) =
      gaussianWeightStableRatio weight := by
  apply gaussianWeightStableRatio_scale
  exact_mod_cast (ne_of_gt hr)

/-- The stable-rank Gaussian lower-tail exponential factor itself is replica-
scale invariant. -/
theorem gaussianStableRankLowerTailExponent_natScale
    {I : Type*} [Fintype I] (weight : I → ℝ≥0)
    {r : ℕ} (hr : 0 < r) :
    Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
        gaussianWeightStableRatio (fun i => (r : ℝ≥0) * weight i)) =
      Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
        gaussianWeightStableRatio weight) := by
  rw [gaussianWeightStableRatio_natScale weight hr]

/-- One-copy physical commutator Gram weight for a pure projector. -/
def pureProjectorOneCopyCommutatorWeight
    {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℂ) (ψ : n → ℂ) : ℝ≥0 :=
  ‖boundedReplicaThresholdProjectorQuadForm
    ((matrixCommutatorRepresentation G)ᴴ *
      matrixCommutatorRepresentation G)
    (Matrix.vec (rankOne ψ))‖₊

/-- Collective replica commutator Gram weight for the same physical
generator and projector. -/
def pureProjectorCollectiveReplicaCommutatorWeight
    {n : Type*} [Fintype n] [DecidableEq n]
    (r : ℕ) (G : Matrix n n ℂ) (ψ : n → ℂ) : ℝ≥0 :=
  ‖boundedReplicaThresholdProjectorQuadForm
    ((collectiveReplicaSlotOp r (matrixCommutatorRepresentation G))ᴴ *
      collectiveReplicaSlotOp r (matrixCommutatorRepresentation G))
    (replicaVector r (Matrix.vec (rankOne ψ)))‖₊

/-- Physical collective replica weights are exactly common `r`-rescalings of
their one-copy weights. -/
theorem pureProjectorCollectiveReplicaCommutatorWeight_eq_nat_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (r : ℕ) (G : Matrix n n ℂ) (ψ : n → ℂ)
    (hψ : hermInner ψ ψ = 1) :
    pureProjectorCollectiveReplicaCommutatorWeight r G ψ =
      (r : ℝ≥0) * pureProjectorOneCopyCommutatorWeight G ψ := by
  apply NNReal.eq
  simp only [pureProjectorCollectiveReplicaCommutatorWeight,
    pureProjectorOneCopyCommutatorWeight, coe_nnnorm]
  rw [pureProjector_collectiveReplicaCommutator_energy r G ψ hψ]
  simp

/-- **Pure-replica stable-rank barrier.**  Every positive replica order has
exactly the same Gaussian commutator stable ratio as one copy. -/
theorem pureProjectorCollectiveReplica_gaussianWeightStableRatio_eq
    {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]
    (G : κ → Matrix n n ℂ) (ψ : n → ℂ)
    (hψ : hermInner ψ ψ = 1) {r : ℕ} (hr : 0 < r) :
    gaussianWeightStableRatio
        (fun j => pureProjectorCollectiveReplicaCommutatorWeight r (G j) ψ) =
      gaussianWeightStableRatio
        (fun j => pureProjectorOneCopyCommutatorWeight (G j) ψ) := by
  have hweight : (fun j =>
      pureProjectorCollectiveReplicaCommutatorWeight r (G j) ψ) =
      (fun j => (r : ℝ≥0) *
        pureProjectorOneCopyCommutatorWeight (G j) ψ) := by
    funext j
    exact pureProjectorCollectiveReplicaCommutatorWeight_eq_nat_mul
      r (G j) ψ hψ
  rw [hweight]
  exact gaussianWeightStableRatio_natScale _ hr

/-- At every replica order, source-side stable rank is capped by generator
count. -/
theorem pureProjectorCollectiveReplica_gaussianWeightStableRatio_le_generatorCard
    {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]
    (r : ℕ) (G : κ → Matrix n n ℂ) (ψ : n → ℂ) :
    gaussianWeightStableRatio
        (fun j => pureProjectorCollectiveReplicaCommutatorWeight r (G j) ψ) ≤
      Fintype.card κ :=
  gaussianWeightStableRatio_le_card _

end

end GaloisForLFunctions.HTGeometry
