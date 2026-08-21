import GaloisForLFunctions.HTGeometry.RobustStaticLocalLaboratoryComplexityGrowthLaw
import GaloisForLFunctions.HTGeometry.PauliEdgeBlockNorms
import GaloisForLFunctions.HTGeometry.LatticeGaussianDensity

/-!
# A one-draw Gaussian laboratory-time complexity law

A fixed local generator dictionary consists of the inverse-square-chain Hamiltonian and every
Pauli word of weight at most two on the same register.  Its coefficients are independent standard
Gaussians drawn once and held fixed for all times.  An explicit coefficient cap around the vector
selecting the reference chain is contained in the robust growth tube, so the product-Gaussian
small-ball law gives an unconditional positive lower bound for the event that one sampled static
Hamiltonian obeys linear complexity growth throughout the complete laboratory interval.

This is a positive-probability bridge, not a typical-draw Brown--Susskind theorem.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal NNReal
open Matrix MeasureTheory ProbabilityTheory Metric

open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

abbrev PairTwoLocalPauliLabel (L : ℕ) :=
  FiniteQLocalPauliLabel (PairQubit L) 2

abbrev PairTwoLocalPauliCoordinate (L : ℕ) :=
  Fin (Fintype.card (PairTwoLocalPauliLabel L))

abbrev InverseSquareGaussianCoordinate (L : ℕ) :=
  Fin (Fintype.card (PairTwoLocalPauliLabel L) + 1)

def pairTwoLocalPauliLabelEquivFin (L : ℕ) :
    PairTwoLocalPauliLabel L ≃ PairTwoLocalPauliCoordinate L :=
  Fintype.equivFin _

/-- Fixed local generator dictionary: the reference chain followed by every Pauli word of weight
at most two on the same register. -/
def inverseSquareGaussianGenerator (L : ℕ) :
    InverseSquareGaussianCoordinate L →
      Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  Fin.cases (inverseSquareChainHamiltonian L) fun k =>
    finitePauliMatrix ((pairTwoLocalPauliLabelEquivFin L).symm k).1

/-- Unit coefficient vector selecting the inverse-square generator. -/
def inverseSquareGaussianCenter (L : ℕ) : InverseSquareGaussianCoordinate L → ℝ :=
  Fin.cases 1 fun _ => 0

/-- One time-independent Hamiltonian selected by its fixed Gaussian coefficients. -/
def inverseSquareGaussianHamiltonian (L : ℕ)
    (J : InverseSquareGaussianCoordinate L → ℝ) :
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  ∑ k, ((J k : ℝ) : ℂ) • inverseSquareGaussianGenerator L k

def inverseSquareGaussianGeneratorMass (L : ℕ) : ℝ :=
  ∑ k, ‖inverseSquareGaussianGenerator L k‖

@[simp] theorem inverseSquareGaussianHamiltonian_center (L : ℕ) :
    inverseSquareGaussianHamiltonian L (inverseSquareGaussianCenter L) =
      inverseSquareChainHamiltonian L := by
  classical
  rw [inverseSquareGaussianHamiltonian, Fin.sum_univ_succ]
  simp [inverseSquareGaussianCenter, inverseSquareGaussianGenerator]

theorem inverseSquareGaussianGenerator_isSelfAdjoint (L : ℕ)
    (k : InverseSquareGaussianCoordinate L) :
    IsSelfAdjoint (inverseSquareGaussianGenerator L k) := by
  refine Fin.cases (inverseSquareChainHamiltonian_isSelfAdjoint L) (fun i => ?_) k
  exact Matrix.isHermitian_iff_isSelfAdjoint.mp
    (finitePauliMatrix_isHermitian ((pairTwoLocalPauliLabelEquivFin L).symm i).1)

theorem inverseSquareGaussianHamiltonian_isSelfAdjoint (L : ℕ)
    (J : InverseSquareGaussianCoordinate L → ℝ) :
    IsSelfAdjoint (inverseSquareGaussianHamiltonian L J) := by
  rw [inverseSquareGaussianHamiltonian]
  exact isSelfAdjoint_sum Finset.univ fun k _ => by
    rw [IsSelfAdjoint, star_smul,
      (inverseSquareGaussianGenerator_isSelfAdjoint L k).star_eq]
    simp

/-- A coefficient cap controls the Hamiltonian in operator norm by the total generator mass. -/
theorem norm_inverseSquareGaussianHamiltonian_sub_center_le
    (L : ℕ) (J : InverseSquareGaussianCoordinate L → ℝ) {ρ : ℝ}
    (hJ : J ∈ closedBall (inverseSquareGaussianCenter L) ρ) :
    ‖inverseSquareGaussianHamiltonian L J - inverseSquareChainHamiltonian L‖ ≤
      ρ * inverseSquareGaussianGeneratorMass L := by
  classical
  have hnorm : ‖J - inverseSquareGaussianCenter L‖ ≤ ρ := by
    simpa [mem_closedBall, dist_eq_norm] using hJ
  have hcoord : ∀ k, |J k - inverseSquareGaussianCenter L k| ≤ ρ := by
    intro k
    have hk := norm_le_pi_norm (J - inverseSquareGaussianCenter L) k
    rw [Pi.sub_apply, Real.norm_eq_abs] at hk
    exact hk.trans hnorm
  rw [← inverseSquareGaussianHamiltonian_center L,
    inverseSquareGaussianHamiltonian, inverseSquareGaussianHamiltonian]
  calc
    ‖(∑ k, ((J k : ℝ) : ℂ) • inverseSquareGaussianGenerator L k) -
        ∑ k, ((inverseSquareGaussianCenter L k : ℝ) : ℂ) •
          inverseSquareGaussianGenerator L k‖
      = ‖∑ k, (((J k - inverseSquareGaussianCenter L k : ℝ)) : ℂ) •
          inverseSquareGaussianGenerator L k‖ := by
          rw [← Finset.sum_sub_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          rw [← sub_smul, Complex.ofReal_sub]
    _ ≤ ∑ k, ‖((((J k - inverseSquareGaussianCenter L k : ℝ)) : ℂ) •
          inverseSquareGaussianGenerator L k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ρ * ‖inverseSquareGaussianGenerator L k‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hcoord k) (norm_nonneg _)
    _ = ρ * inverseSquareGaussianGeneratorMass L := by
      rw [inverseSquareGaussianGeneratorMass, Finset.mul_sum]

theorem inverseSquareGaussianCenter_norm_le_one (L : ℕ) :
    ‖inverseSquareGaussianCenter L‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k => ?_
  refine Fin.cases ?_ (fun i => ?_) k <;>
    simp [inverseSquareGaussianCenter]

def inverseSquareGaussianUniformGrowthEvent (L : ℕ) (T ε : ℝ) :
    Set (InverseSquareGaussianCoordinate L → ℝ) :=
  {J | ∀ t : ℝ,
    2048 * Real.pi * ε ≤ t →
    t ≤ ε * L →
    t ≤ T →
    ((⌊t / (256 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞) ≤
      operatorTwoGateComplexityTo L ε
        (unitaryEvolution (inverseSquareGaussianHamiltonian L J) t)}

/-- **Positive-probability one-draw robust ramp.** A single zero-mean product-Gaussian draw from
the fixed local dictionary obeys the linear lower bound throughout the complete laboratory
interval on an explicitly lower-bounded event. -/
theorem measure_inverseSquareGaussianUniformGrowthEvent_lower
    (L : ℕ) {T ε ρ : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hscale : T * (ρ * inverseSquareGaussianGeneratorMass L) ≤ ε) :
    ENNReal.ofReal ((2 * gaussianFloorTwo * ρ) ^
        (Fintype.card (PairTwoLocalPauliLabel L) + 1)) ≤
      (Measure.pi fun _ : InverseSquareGaussianCoordinate L => gaussianReal 0 1)
        (inverseSquareGaussianUniformGrowthEvent L T ε) := by
  have hball := measure_pi_gaussian_shifted_ball_lower
    (Fintype.card (PairTwoLocalPauliLabel L) + 1)
    (inverseSquareGaussianCenter_norm_le_one L) hρ0 hρ1
  refine hball.trans (measure_mono ?_)
  intro J hJ t htMin htLab htT
  have hnorm := norm_inverseSquareGaussianHamiltonian_sub_center_le L J hJ
  have htube : T * ‖inverseSquareGaussianHamiltonian L J -
      inverseSquareChainHamiltonian L‖ ≤ ε := by
    exact (mul_le_mul_of_nonneg_left hnorm hT).trans hscale
  exact perturbed_inverseSquareChain_uniform_laboratory_growth
    (inverseSquareGaussianHamiltonian_isSelfAdjoint L J)
    hε hεmax htube t htMin htLab htT

/-- The one-draw uniform-growth event has strictly positive Gaussian probability for every
strictly positive admissible cap radius. -/
theorem measure_inverseSquareGaussianUniformGrowthEvent_pos
    (L : ℕ) {T ε ρ : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hscale : T * (ρ * inverseSquareGaussianGeneratorMass L) ≤ ε) :
    0 < (Measure.pi fun _ : InverseSquareGaussianCoordinate L => gaussianReal 0 1)
      (inverseSquareGaussianUniformGrowthEvent L T ε) := by
  have hlower := measure_inverseSquareGaussianUniformGrowthEvent_lower
    L hT hε hεmax hρ.le hρ1 hscale
  exact (ENNReal.ofReal_pos.mpr (by positivity [gaussianFloorTwo_pos])).trans_le hlower

end

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
