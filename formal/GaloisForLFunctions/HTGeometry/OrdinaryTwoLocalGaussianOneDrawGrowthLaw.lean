import GaloisForLFunctions.HTGeometry.InverseSquareLocalGaussianOneDrawGrowthLaw

/-!
# Termwise two-local Gaussian one-draw complexity growth

This module removes a correlated-coordinate weakness from the first Gaussian bridge.  Independent
standard Gaussian coordinates now multiply individual matching projectors, individual bridge
projectors, and every Pauli word of weight at most two.  The coefficient vector reproducing the
inverse-square chain has sup norm at most one.  An explicit Gaussian cap around it therefore has
positive measure and, by the robust Hamiltonian tube law, every Hamiltonian in that cap obeys the
linear two-gate lower bound at every time in the laboratory interval.

All coefficients are drawn once and the Hamiltonian is time independent.  The result remains a
positive-probability theorem; it does not assert typical Brown--Susskind growth.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal NNReal
open Matrix MeasureTheory ProbabilityTheory Metric

open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

abbrev OrdinaryTwoLocalRawCoordinate (L : ℕ) :=
  Fin L ⊕ (Fin L ⊕ PairTwoLocalPauliLabel L)

abbrev OrdinaryTwoLocalGaussianCoordinate (L : ℕ) :=
  Fin (Fintype.card (OrdinaryTwoLocalRawCoordinate L))

def ordinaryTwoLocalRawEquivFin (L : ℕ) :
    OrdinaryTwoLocalRawCoordinate L ≃ OrdinaryTwoLocalGaussianCoordinate L :=
  Fintype.equivFin _

/-- One matching-edge occupation projector. -/
def matchingOccupationMatrix {L : ℕ} (j : Fin L) :
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  Matrix.diagonal fun x =>
    if x (j, false) = true ∧ x (j, true) = true then 1 else 0

/-- One consecutive bridge occupation projector, with a zero terminal entry. -/
def bridgeOccupationMatrix {L : ℕ} (j : Fin L) :
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  Matrix.diagonal fun x =>
    if h : j.val + 1 < L then
      if x (j, true) = true ∧ x (⟨j.val + 1, h⟩, false) = true then 1 else 0
    else 0

/-- Termwise local dictionary before finite numbering. -/
def ordinaryTwoLocalRawGenerator (L : ℕ) : OrdinaryTwoLocalRawCoordinate L →
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ
  | Sum.inl j => matchingOccupationMatrix j
  | Sum.inr (Sum.inl j) => bridgeOccupationMatrix j
  | Sum.inr (Sum.inr P) => finitePauliMatrix P.1

/-- Coefficients selecting the inverse-square chain from the termwise dictionary. -/
def ordinaryTwoLocalRawCenter (L : ℕ) : OrdinaryTwoLocalRawCoordinate L → ℝ
  | Sum.inl j => 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)
  | Sum.inr (Sum.inl _) => 1 / (L : ℝ) ^ 3
  | Sum.inr (Sum.inr _) => 0

def ordinaryTwoLocalGenerator (L : ℕ) (k : OrdinaryTwoLocalGaussianCoordinate L) :=
  ordinaryTwoLocalRawGenerator L ((ordinaryTwoLocalRawEquivFin L).symm k)

def ordinaryTwoLocalCenter (L : ℕ) (k : OrdinaryTwoLocalGaussianCoordinate L) :=
  ordinaryTwoLocalRawCenter L ((ordinaryTwoLocalRawEquivFin L).symm k)

/-- Static local Hamiltonian with one independent real coefficient per dictionary term. -/
def ordinaryTwoLocalGaussianHamiltonian (L : ℕ)
    (J : OrdinaryTwoLocalGaussianCoordinate L → ℝ) :
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  ∑ k, ((J k : ℝ) : ℂ) • ordinaryTwoLocalGenerator L k

/-- The declared centre is exactly the inverse-square-chain Hamiltonian. -/
theorem ordinaryTwoLocalGaussianHamiltonian_center (L : ℕ) :
    ordinaryTwoLocalGaussianHamiltonian L (ordinaryTwoLocalCenter L) =
      inverseSquareChainHamiltonian L := by
  classical
  rw [ordinaryTwoLocalGaussianHamiltonian]
  change (∑ k, ((ordinaryTwoLocalRawCenter L
    ((ordinaryTwoLocalRawEquivFin L).symm k) : ℝ) : ℂ) •
      ordinaryTwoLocalRawGenerator L ((ordinaryTwoLocalRawEquivFin L).symm k)) = _
  rw [← (ordinaryTwoLocalRawEquivFin L).sum_comp]
  simp only [Fintype.sum_sum_type]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [ordinaryTwoLocalRawCenter, ordinaryTwoLocalRawGenerator,
      matchingOccupationMatrix, bridgeOccupationMatrix,
      inverseSquareChainHamiltonian, inverseSquareChainEnergy,
      inverseSquareMatchingEnergy, inverseCubeBridgeEnergy,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.diagonal_apply_eq]
    rw [Finset.mul_sum]
    congr 1 <;>
      apply Finset.sum_congr rfl <;>
      intro j _ <;>
      split_ifs <;> simp_all
  · simp [ordinaryTwoLocalRawCenter, ordinaryTwoLocalRawGenerator,
      matchingOccupationMatrix, bridgeOccupationMatrix,
      inverseSquareChainHamiltonian, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, hxy]

def ordinaryTwoLocalGeneratorMass (L : ℕ) : ℝ :=
  ∑ k, ‖ordinaryTwoLocalGenerator L k‖

theorem matchingOccupationMatrix_isSelfAdjoint {L : ℕ} (j : Fin L) :
    IsSelfAdjoint (matchingOccupationMatrix j) := by
  apply Matrix.isHermitian_iff_isSelfAdjoint.mp
  rw [matchingOccupationMatrix, Matrix.isHermitian_diagonal_iff]
  intro x
  split_ifs <;> simp

theorem bridgeOccupationMatrix_isSelfAdjoint {L : ℕ} (j : Fin L) :
    IsSelfAdjoint (bridgeOccupationMatrix j) := by
  apply Matrix.isHermitian_iff_isSelfAdjoint.mp
  rw [bridgeOccupationMatrix, Matrix.isHermitian_diagonal_iff]
  intro x
  split_ifs <;> simp

theorem ordinaryTwoLocalRawGenerator_isSelfAdjoint (L : ℕ)
    (a : OrdinaryTwoLocalRawCoordinate L) :
    IsSelfAdjoint (ordinaryTwoLocalRawGenerator L a) := by
  rcases a with j | (j | P)
  · exact matchingOccupationMatrix_isSelfAdjoint j
  · exact bridgeOccupationMatrix_isSelfAdjoint j
  · exact Matrix.isHermitian_iff_isSelfAdjoint.mp (finitePauliMatrix_isHermitian P.1)

theorem ordinaryTwoLocalGenerator_isSelfAdjoint (L : ℕ)
    (k : OrdinaryTwoLocalGaussianCoordinate L) :
    IsSelfAdjoint (ordinaryTwoLocalGenerator L k) :=
  ordinaryTwoLocalRawGenerator_isSelfAdjoint L _

theorem ordinaryTwoLocalGaussianHamiltonian_isSelfAdjoint (L : ℕ)
    (J : OrdinaryTwoLocalGaussianCoordinate L → ℝ) :
    IsSelfAdjoint (ordinaryTwoLocalGaussianHamiltonian L J) := by
  rw [ordinaryTwoLocalGaussianHamiltonian]
  exact isSelfAdjoint_sum Finset.univ fun k _ => by
    rw [IsSelfAdjoint, star_smul,
      (ordinaryTwoLocalGenerator_isSelfAdjoint L k).star_eq]
    simp

/-- Coefficient sup-distance controls the Hamiltonian in operator norm. -/
theorem norm_ordinaryTwoLocalGaussianHamiltonian_sub_center_le
    (L : ℕ) (J : OrdinaryTwoLocalGaussianCoordinate L → ℝ) {ρ : ℝ}
    (hJ : J ∈ closedBall (ordinaryTwoLocalCenter L) ρ) :
    ‖ordinaryTwoLocalGaussianHamiltonian L J - inverseSquareChainHamiltonian L‖ ≤
      ρ * ordinaryTwoLocalGeneratorMass L := by
  classical
  have hnorm : ‖J - ordinaryTwoLocalCenter L‖ ≤ ρ := by
    simpa [mem_closedBall, dist_eq_norm] using hJ
  have hcoord : ∀ k, |J k - ordinaryTwoLocalCenter L k| ≤ ρ := by
    intro k
    have hk := norm_le_pi_norm (J - ordinaryTwoLocalCenter L) k
    rw [Pi.sub_apply, Real.norm_eq_abs] at hk
    exact hk.trans hnorm
  rw [← ordinaryTwoLocalGaussianHamiltonian_center L,
    ordinaryTwoLocalGaussianHamiltonian, ordinaryTwoLocalGaussianHamiltonian]
  calc
    ‖(∑ k, ((J k : ℝ) : ℂ) • ordinaryTwoLocalGenerator L k) -
        ∑ k, ((ordinaryTwoLocalCenter L k : ℝ) : ℂ) •
          ordinaryTwoLocalGenerator L k‖
      = ‖∑ k, (((J k - ordinaryTwoLocalCenter L k : ℝ)) : ℂ) •
          ordinaryTwoLocalGenerator L k‖ := by
          rw [← Finset.sum_sub_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          rw [← sub_smul, Complex.ofReal_sub]
    _ ≤ ∑ k, ‖((((J k - ordinaryTwoLocalCenter L k : ℝ)) : ℂ) •
          ordinaryTwoLocalGenerator L k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ρ * ‖ordinaryTwoLocalGenerator L k‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hcoord k) (norm_nonneg _)
    _ = ρ * ordinaryTwoLocalGeneratorMass L := by
      rw [ordinaryTwoLocalGeneratorMass, Finset.mul_sum]

private theorem abs_one_div_nat_pow_le_one (m p : ℕ) :
    |1 / ((m : ℝ) ^ p)| ≤ 1 := by
  cases m with
  | zero =>
      by_cases hp : p = 0
      · subst p
        norm_num
      · simp [zero_pow hp]
  | succ m =>
      rw [abs_of_nonneg (by positivity)]
      apply (div_le_one (by positivity)).2
      have hm : (1 : ℝ) ≤ (m.succ : ℕ) := by exact_mod_cast m.succ_pos
      simpa using pow_le_pow_left₀ zero_le_one hm p

/-- The coefficient vector selecting the reference chain lies in the Gaussian unit cube. -/
theorem ordinaryTwoLocalCenter_norm_le_one (L : ℕ) :
    ‖ordinaryTwoLocalCenter L‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k => ?_
  change ‖ordinaryTwoLocalRawCenter L ((ordinaryTwoLocalRawEquivFin L).symm k)‖ ≤ 1
  rcases (ordinaryTwoLocalRawEquivFin L).symm k with j | (j | P)
  · simpa [ordinaryTwoLocalRawCenter, Real.norm_eq_abs] using
      abs_one_div_nat_pow_le_one (j.val + 1) 2
  · simpa [ordinaryTwoLocalRawCenter, Real.norm_eq_abs] using
      abs_one_div_nat_pow_le_one L 3
  · simp [ordinaryTwoLocalRawCenter]

def ordinaryTwoLocalGaussianUniformGrowthEvent (L : ℕ) (T ε : ℝ) :
    Set (OrdinaryTwoLocalGaussianCoordinate L → ℝ) :=
  {J | ∀ t : ℝ,
    2048 * Real.pi * ε ≤ t →
    t ≤ ε * L →
    t ≤ T →
    ((⌊t / (256 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞) ≤
      operatorTwoGateComplexityTo L ε
        (unitaryEvolution (ordinaryTwoLocalGaussianHamiltonian L J) t)}

/-- Explicit product-Gaussian lower bound for the one-draw, all-laboratory-times growth event. -/
theorem measure_ordinaryTwoLocalGaussianUniformGrowthEvent_lower
    (L : ℕ) {T ε ρ : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hscale : T * (ρ * ordinaryTwoLocalGeneratorMass L) ≤ ε) :
    ENNReal.ofReal ((2 * gaussianFloorTwo * ρ) ^
        Fintype.card (OrdinaryTwoLocalRawCoordinate L)) ≤
      (Measure.pi fun _ : OrdinaryTwoLocalGaussianCoordinate L => gaussianReal 0 1)
        (ordinaryTwoLocalGaussianUniformGrowthEvent L T ε) := by
  have hball := measure_pi_gaussian_shifted_ball_lower
    (Fintype.card (OrdinaryTwoLocalRawCoordinate L))
    (ordinaryTwoLocalCenter_norm_le_one L) hρ0 hρ1
  refine hball.trans (measure_mono ?_)
  intro J hJ t htMin htLab htT
  have hnorm := norm_ordinaryTwoLocalGaussianHamiltonian_sub_center_le L J hJ
  have htube : T * ‖ordinaryTwoLocalGaussianHamiltonian L J -
      inverseSquareChainHamiltonian L‖ ≤ ε := by
    exact (mul_le_mul_of_nonneg_left hnorm hT).trans hscale
  exact perturbed_inverseSquareChain_uniform_laboratory_growth
    (ordinaryTwoLocalGaussianHamiltonian_isSelfAdjoint L J)
    hε hεmax htube t htMin htLab htT

/-- The termwise two-local one-draw growth event has strictly positive Gaussian probability. -/
theorem measure_ordinaryTwoLocalGaussianUniformGrowthEvent_pos
    (L : ℕ) {T ε ρ : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hscale : T * (ρ * ordinaryTwoLocalGeneratorMass L) ≤ ε) :
    0 < (Measure.pi fun _ : OrdinaryTwoLocalGaussianCoordinate L => gaussianReal 0 1)
      (ordinaryTwoLocalGaussianUniformGrowthEvent L T ε) := by
  have hlower := measure_ordinaryTwoLocalGaussianUniformGrowthEvent_lower
    L hT hε hεmax hρ.le hρ1 hscale
  exact (ENNReal.ofReal_pos.mpr (by positivity [gaussianFloorTwo_pos])).trans_le hlower

end

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
