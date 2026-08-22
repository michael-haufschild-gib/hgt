import GaloisForLFunctions.HTGeometry.HarmonicMatchingChoiSharpRamp
import GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw

open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal NNReal
open Matrix MeasureTheory ProbabilityTheory Metric

/-!
# Same-draw robustness of the sharp harmonic Choi ramp

Duhamel's inequality transports the sharp shell floor from the exact harmonic matching centre to
every self-adjoint Hamiltonian in the operator-norm tube of radius `η/T` about it, with any strict
error slack below `ε⋆`.  A nondegenerate product-Gaussian ordinary two-local ensemble gives that
tube explicit positive mass, so one draw obeys the ramp simultaneously on every laboratory shell
below a fixed horizon.
-/

namespace GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiSharpRamp

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.SharpControlledPhaseChoiCutGap
open GaloisForLFunctions.HTGeometry.HarmonicMatchingChoiSharpRamp
open GaloisForLFunctions.HTGeometry.HarmonicMatchingChoiLaboratoryGrowthLaw
open GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open GaloisForLFunctions.RHTower

noncomputable section

/-- A fixed operator-norm tube around the harmonic centre inherits every complete Choi shell at
the sharp error radius. -/
theorem perturbed_harmonicMatching_twoGateCount_shell_lower_sharp
    {L K : ℕ} (c : List (LocalGate (PairQubit L)))
    {H : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    {T t ε η : ℝ}
    (hH : IsSelfAdjoint H)
    (hKL : 2 * K ≤ L)
    (htlo : Real.pi * K ≤ t) (hthi : t < Real.pi * (K + 1))
    (htT : t ≤ T)
    (htube : T * ‖H - harmonicMatchingHamiltonian L‖ ≤ η)
    (hbudget : ε + η < epsilonStar)
    (hclose : choiDist (circuitMatrix c) (unitaryEvolution H t) < ε) :
    K ≤ 2 * twoGateCount c := by
  let U := unitaryEvolution H t
  let V := unitaryEvolution (harmonicMatchingHamiltonian L) t
  have ht0 : 0 ≤ t := by
    have hbase : 0 ≤ Real.pi * (K : ℝ) := mul_nonneg Real.pi_pos.le (Nat.cast_nonneg K)
    exact hbase.trans htlo
  have hC : (circuitMatrix c)ᴴ * circuitMatrix c = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp (circuitMatrix_unitary c))
  have hU : Uᴴ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp (unitaryEvolution_mem_unitary hH t))
  have hVself := harmonicMatchingHamiltonian_isSelfAdjoint L
  have hV : Vᴴ * V = 1 := by
    simpa [V, Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp
        (unitaryEvolution_mem_unitary hVself t))
  have hUV : choiDist U V ≤ η := by
    calc
      choiDist U V ≤ ‖U - V‖ := choiDist_le_l2_opNorm_sub U V hU hV
      _ ≤ |t| * ‖H - harmonicMatchingHamiltonian L‖ := by
        exact norm_unitaryEvolution_sub_le H (harmonicMatchingHamiltonian L) hH hVself t
      _ = t * ‖H - harmonicMatchingHamiltonian L‖ := by rw [abs_of_nonneg ht0]
      _ ≤ T * ‖H - harmonicMatchingHamiltonian L‖ :=
        mul_le_mul_of_nonneg_right htT (norm_nonneg _)
      _ ≤ η := htube
  have htri : choiDist (circuitMatrix c) V ≤
      choiDist (circuitMatrix c) U + choiDist U V :=
    choiDist_triangle Fintype.card_pos hC hU hV
  have hcenter : choiDist (circuitMatrix c) V < epsilonStar :=
    lt_of_le_of_lt htri <| (add_lt_add_of_lt_of_le hclose hUV).trans hbudget
  apply harmonicMatching_twoGateCount_shell_lower_sharp c hKL htlo hthi
  simpa [V, unitaryEvolution_harmonicMatchingHamiltonian] using hcenter

/-- One draw obeys the sharp Choi two-gate floor on every shell below one fixed horizon. -/
def ordinaryTwoLocalGaussianHarmonicChoiSharpRampEvent
    (L : ℕ) (T ε : ℝ) : Set (OrdinaryTwoLocalGaussianCoordinate L → ℝ) :=
  {J | ∀ (K : ℕ) (c : List (LocalGate (PairQubit L))) (t : ℝ),
    2 * K ≤ L →
    Real.pi * K ≤ t →
    t < Real.pi * (K + 1) →
    t ≤ T →
    choiDist (circuitMatrix c)
      (unitaryEvolution (ordinaryTwoLocalGaussianHamiltonian L J) t) < ε →
    K ≤ 2 * twoGateCount c}

/-- Explicit Gaussian mass of one-draw Hamiltonians satisfying every sharp harmonic Choi shell. -/
theorem measure_ordinaryTwoLocalGaussianHarmonicChoiSharpRampEvent_lower
    (L : ℕ) {T ε η ρ : ℝ}
    (hT : 0 ≤ T)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hscale : T * (ρ * ordinaryTwoLocalGeneratorMass L) ≤ η)
    (hbudget : ε + η < epsilonStar) :
    ENNReal.ofReal ((2 * gaussianFloorTwo * ρ) ^
        Fintype.card (OrdinaryTwoLocalRawCoordinate L)) ≤
      (Measure.pi fun _ : OrdinaryTwoLocalGaussianCoordinate L => gaussianReal 0 1)
        (ordinaryTwoLocalGaussianHarmonicChoiSharpRampEvent L T ε) := by
  have hball := measure_pi_gaussian_shifted_ball_lower
    (Fintype.card (OrdinaryTwoLocalRawCoordinate L))
    (harmonicOrdinaryTwoLocalCenter_norm_le_one L) hρ0 hρ1
  refine hball.trans (measure_mono ?_)
  intro J hJ K c t hKL htlo hthi htT hclose
  have hnorm :=
    norm_ordinaryTwoLocalGaussianHamiltonian_sub_harmonicCenter_le L J hJ
  have htube : T * ‖ordinaryTwoLocalGaussianHamiltonian L J -
      harmonicMatchingHamiltonian L‖ ≤ η := by
    exact (mul_le_mul_of_nonneg_left hnorm hT).trans hscale
  exact perturbed_harmonicMatching_twoGateCount_shell_lower_sharp c
    (ordinaryTwoLocalGaussianHamiltonian_isSelfAdjoint L J)
    hKL htlo hthi htT htube hbudget hclose

/-- The same-draw all-shell sharp Choi ramp event has strictly positive Gaussian probability. -/
theorem measure_ordinaryTwoLocalGaussianHarmonicChoiSharpRampEvent_pos
    (L : ℕ) {T ε η ρ : ℝ}
    (hT : 0 ≤ T)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hscale : T * (ρ * ordinaryTwoLocalGeneratorMass L) ≤ η)
    (hbudget : ε + η < epsilonStar) :
    0 < (Measure.pi fun _ : OrdinaryTwoLocalGaussianCoordinate L => gaussianReal 0 1)
      (ordinaryTwoLocalGaussianHarmonicChoiSharpRampEvent L T ε) := by
  have hlower := measure_ordinaryTwoLocalGaussianHarmonicChoiSharpRampEvent_lower
    L hT hρ.le hρ1 hscale hbudget
  exact (ENNReal.ofReal_pos.mpr (by positivity [gaussianFloorTwo_pos])).trans_le hlower

end

end GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiSharpRamp
