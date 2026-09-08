import GaloisForLFunctions.HTGeometry.FiniteGibbsDifferentialBoundary
import GaloisForLFunctions.HTGeometry.SelectionSynthesisDivergence
import GaloisForLFunctions.HTGeometry.FiniteNoiseMixingApplications
import GaloisForLFunctions.HTGeometry.PureBipartiteEntanglementEntropy

/-!
# Information capacity, Gibbs reserve, and bipartite saturation

The entropy reserve of arXiv:2608.06941, equations (1)--(6), specializes to
relative entropy from the uniform state in the existing finite Gibbs corpus.
Its positivity and free-energy formula are proved from normalized exponential
weights. Unitary diagonal observation consumes this reserve. For globally pure
bipartite states, the reserve imbalance is exactly the logarithmic dimension
imbalance; unequal subsystem dimensions forbid joint saturation.
-/

noncomputable section
open scoped BigOperators NNReal
open _root_.HTGeometry
namespace GaloisForLFunctions.HTGeometry

def gibbsInformationReserve {n : ℕ} (β : ℝ) (E : Fin (n + 1) → ℝ) : ℝ :=
  Real.log (n + 1 : ℝ) - entropy (finiteGibbsStateWeight β E)

theorem gibbsEntropy_partition_identity {n : ℕ} (β : ℝ) (E : Fin (n + 1) → ℝ) :
    entropy (finiteGibbsStateWeight β E) =
      Real.log (finiteGibbsPartition β E) + β * finiteGibbsEnergyMean β E := by
  have hlog (i : Fin (n + 1)) : Real.log (finiteGibbsStateWeight β E i) =
      -β * E i - Real.log (finiteGibbsPartition β E) := by
    rw [finiteGibbsStateWeight, Real.log_div (Real.exp_ne_zero _) (finiteGibbsPartition_pos β E).ne',
      Real.log_exp]
  simp only [entropy, tsum_fintype, hlog]
  simp_rw [show ∀ i : Fin (n + 1), -(finiteGibbsStateWeight β E i *
      (-β * E i - Real.log (finiteGibbsPartition β E))) =
      finiteGibbsStateWeight β E i * Real.log (finiteGibbsPartition β E) +
        β * (finiteGibbsStateWeight β E i * E i) by intro i; ring]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    sum_finiteGibbsStateWeight_eq_one, one_mul]
  rfl

theorem gibbsInformationReserve_eq_relativeEntropy {n : ℕ}
    (β : ℝ) (E : Fin (n + 1) → ℝ) :
    gibbsInformationReserve β E =
      relEntropy (finiteGibbsStateWeight β E) (fun _ => (n + 1 : ℝ)⁻¹) := by
  have h := entropy_add_relEntropy (fun i => (finiteGibbsStateWeight_pos β E i).le)
    (fun _ => (by positivity : 0 < (n + 1 : ℝ)⁻¹)) (hasSum_fintype _).summable (hasSum_fintype _).summable
  have hc : crossEntropy (finiteGibbsStateWeight β E) (fun _ => (n + 1 : ℝ)⁻¹) =
      Real.log (n + 1 : ℝ) := by
    simp only [crossEntropy, tsum_fintype, Real.log_inv, mul_neg, neg_neg,
      ← Finset.sum_mul, sum_finiteGibbsStateWeight_eq_one, one_mul]
  rw [hc] at h
  unfold gibbsInformationReserve
  linarith

theorem gibbsInformationReserve_nonneg {n : ℕ} (β : ℝ) (E : Fin (n + 1) → ℝ) :
    0 ≤ gibbsInformationReserve β E := by
  rw [gibbsInformationReserve_eq_relativeEntropy]
  apply relEntropy_nonneg (fun i => (finiteGibbsStateWeight_pos β E i).le)
    (fun _ => by positivity)
  · simpa only [sum_finiteGibbsStateWeight_eq_one] using hasSum_fintype (finiteGibbsStateWeight β E)
  · have hs : (∑ _ : Fin (n + 1), (n + 1 : ℝ)⁻¹) = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      exact mul_inv_cancel₀ (by positivity)
    simpa only [hs] using hasSum_fintype (fun _ : Fin (n + 1) => (n + 1 : ℝ)⁻¹)
  · exact (hasSum_fintype _).summable

theorem gibbsInformationReserve_freeEnergy {n : ℕ} (β : ℝ) (E : Fin (n + 1) → ℝ) :
    gibbsInformationReserve β E = Real.log (n + 1 : ℝ) -
      Real.log (finiteGibbsPartition β E) - β * finiteGibbsEnergyMean β E := by
  rw [gibbsInformationReserve, gibbsEntropy_partition_identity]
  ring

theorem gibbsInformationReserve_zero_inverseTemperature {n : ℕ} (E : Fin (n + 1) → ℝ) :
    gibbsInformationReserve 0 E = 0 := by
  rw [gibbsInformationReserve_freeEnergy]
  simp [finiteGibbsPartition]

/-- The information capacity splits into thermal entropy and its nonnegative reserve. -/
theorem gibbsInformation_capacity_split {n : ℕ} (β : ℝ) (E : Fin (n + 1) → ℝ) :
    entropy (finiteGibbsStateWeight β E) + gibbsInformationReserve β E = Real.log (n + 1 : ℝ) := by
  unfold gibbsInformationReserve
  ring

/-- Discarding unitary off-diagonal coordinates can only consume the entropy reserve. -/
theorem gibbsInformationReserve_after_unitary_observation {n : ℕ}
    (β : ℝ) (E : Fin (n + 1) → ℝ) (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
    Real.log (n + 1 : ℝ) - entropy (finiteUnitaryDiagonalCoordinate (finiteGibbsStateWeight β E) U) ≤
      gibbsInformationReserve β E := by
  have h := entropy_le_entropy_finiteUnitaryDiagonalCoordinate U
    (fun i => (⟨finiteGibbsStateWeight β E i, (finiteGibbsStateWeight_pos β E i).le⟩ : ℝ≥0))
  exact sub_le_sub_left h _

/-- Capacity left after tracing out the right subsystem. -/
def pureLeftInformationReserve {n m : ℕ} (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) : ℝ :=
  Real.log (n + 1 : ℝ) - finiteMatrixVonNeumannEntropy (pureStateReducedLeft ψ)
    (pureStateReducedLeft_isHermitian ψ)

/-- Capacity left after tracing out the left subsystem. -/
def pureRightInformationReserve {n m : ℕ} (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) : ℝ :=
  Real.log (m + 1 : ℝ) - finiteMatrixVonNeumannEntropy (pureStateReducedRight ψ)
    (pureStateReducedRight_isHermitian ψ)

/-- The reserve imbalance of a globally pure state depends only on subsystem dimensions. -/
theorem pureInformationReserve_dimension_balance {n m : ℕ}
    (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) :
    pureRightInformationReserve ψ - pureLeftInformationReserve ψ =
      Real.log (m + 1 : ℝ) - Real.log (n + 1 : ℝ) := by
  unfold pureRightInformationReserve pureLeftInformationReserve
  rw [pureStateReduced_entropies_eq]
  ring

/-- Unequal subsystems cannot have equal information reserves. -/
theorem pureInformationReserve_equal_iff_dimensions {n m : ℕ}
    (ψ : Fin (n + 1) × Fin (m + 1) → ℂ) :
    pureRightInformationReserve ψ = pureLeftInformationReserve ψ ↔ m = n := by
  rw [← sub_eq_zero, pureInformationReserve_dimension_balance, sub_eq_zero]
  constructor
  · intro h
    have hn : (n + 1 : ℝ) ∈ Set.Ioi (0 : ℝ) := show 0 < (n + 1 : ℝ) by positivity
    have hm : (m + 1 : ℝ) ∈ Set.Ioi (0 : ℝ) := show 0 < (m + 1 : ℝ) by positivity
    have heq := Real.strictMonoOn_log.injOn hm hn h
    have heq' : (m : ℝ) = n := by linarith
    exact_mod_cast heq'
  · intro h
    rw [h]

/-- A pure state cannot saturate both unequal subsystem capacities. -/
theorem pureInformationReserve_no_joint_saturation (n : ℕ)
    (ψ : Fin (n + 1) × Fin (n + 2) → ℂ) :
    ¬ (pureLeftInformationReserve ψ = 0 ∧ pureRightInformationReserve ψ = 0) := by
  rintro ⟨hl, hr⟩
  have hd := (pureInformationReserve_equal_iff_dimensions ψ).mp (hr.trans hl.symm)
  omega

end GaloisForLFunctions.HTGeometry
