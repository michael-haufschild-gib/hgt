import GaloisForLFunctions.HTGeometry.SiteFactorQubitPauliWeightLaw
import GaloisForLFunctions.HTGeometry.FiniteQLocalPauliCardinalityLaw
import GaloisForLFunctions.RHTower.NearestNeighborPolynomialCircuitExponentialExcursionLaw

open Filter Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace RHTower

noncomputable section

/-- The nearest-neighbour draw bundled as its literal self-adjoint Hamiltonian. -/
def nearestNeighborPathSelfAdjointHamiltonian (L : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :
    selfAdjoint
      (Matrix (FiniteQubitConfiguration (PairQubit L))
        (FiniteQubitConfiguration (PairQubit L)) ℂ) :=
  ⟨nearestNeighborPathLocalHamiltonian L p,
    nearestNeighborPathLocalHamiltonian_isHermitian L p⟩

theorem nearestNeighborPathSelfAdjointHamiltonian_mem_localSubmodule
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :
    (nearestNeighborPathSelfAdjointHamiltonian L p :
      Matrix (FiniteQubitConfiguration (PairQubit L))
        (FiniteQubitConfiguration (PairQubit L)) ℂ) ∈
      nearestNeighborPathLocalSubmodule L := by
  change realAffineMatrix 0
      (realMatrixSubmoduleGenerator (nearestNeighborPathLocalSubmodule L)) p ∈
    nearestNeighborPathLocalSubmodule L
  exact realAffineMatrix_mem_submodule _ p

/-- Every Hamiltonian in the exact ordinary nearest-neighbour draw is literally Pauli two-local. -/
theorem nearestNeighborPathSelfAdjointHamiltonian_hasPauliWeightAtMost_two
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :
    HasPauliWeightAtMost (PairQubit L) 2
      (nearestNeighborPathSelfAdjointHamiltonian L p) := by
  exact hasPauliWeightAtMost_two_of_mem_siteFactorLocalSubmodule
    (nestedQubitPathGraph L) (nearestNeighborPathSelfAdjointHamiltonian L p)
    (nearestNeighborPathSelfAdjointHamiltonian_mem_localSubmodule L p)

/-- A maximally projective nonempty nearest-neighbour draw cannot be the zero Hamiltonian. -/
theorem nearestNeighborPathSelfAdjointHamiltonian_ne_zero
    {L : ℕ} (hL : 0 < L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathLocalMaximalSet L) :
    nearestNeighborPathSelfAdjointHamiltonian L p ≠ 0 := by
  intro hzero
  have hmatrix : nearestNeighborPathLocalHamiltonian L p = 0 := by
    exact congrArg Subtype.val hzero
  have heigenzero : ∀ x,
      (nearestNeighborPathLocalHamiltonian_isHermitian L p).eigenvalues x = 0 := by
    intro x
    rw [(nearestNeighborPathLocalHamiltonian_isHermitian L p).eigenvalues_eq]
    have hmul : (nearestNeighborPathLocalHamiltonian L p).mulVec
        ((nearestNeighborPathLocalHamiltonian_isHermitian L p).eigenvectorBasis x).ofLp = 0 := by
      calc
        _ = (0 : Matrix (FiniteQubitConfiguration (PairQubit L))
              (FiniteQubitConfiguration (PairQubit L)) ℂ).mulVec
              ((nearestNeighborPathLocalHamiltonian_isHermitian L p).eigenvectorBasis x).ofLp :=
            congrArg (fun M => M.mulVec
              ((nearestNeighborPathLocalHamiltonian_isHermitian L p).eigenvectorBasis x).ofLp)
              hmatrix
        _ = 0 := by simp
    rw [hmul]
    simp
  let xFalse : FiniteQubitConfiguration (PairQubit L) := fun _ => false
  let xTrue : FiniteQubitConfiguration (PairQubit L) := fun _ => true
  have hne : xFalse ≠ xTrue := by
    intro h
    have hi := congrFun h (⟨0, hL⟩, false)
    simp [xFalse, xTrue] at hi
  apply hne
  exact (maximallyProjectiveEnergy_nearestNeighborPathLocalHamiltonian hp).injective (by
    rw [heigenzero xFalse, heigenzero xTrue])

/-- Two-local product-stabilizer separator entropy is eventually below paired-register Hilbert
dimension. -/
theorem eventually_pairQubit_twoLocalPauli_separator :
    ∀ᶠ L : ℕ in atTop,
      Fintype.card (FiniteQLocalPauliLabel (PairQubit L) 2) * 3 ^ (2 : ℕ) <
        2 ^ Fintype.card (PairQubit L) + 1 := by
  have hbase := eventually_twoLocalPauli_separator
  rw [eventually_atTop] at hbase ⊢
  obtain ⟨N, hN⟩ := hbase
  refine ⟨N, fun L hL => ?_⟩
  have hNL : N ≤ L * 2 := by omega
  have hsep := hN (L * 2) hNL
  rw [card_finiteQLocalPauliLabel_eq_count]
  rw [card_finiteQLocalPauliLabel] at hsep
  simpa [PairQubit, mul_comm] using hsep

/-- At every real time, one fixed two-query product-stabilizer experiment separates the
nearest-neighbour autonomous evolution from the exact inverse-dimension Haar benchmark. -/
def NearestNeighborPathPermanentLocalityHaarSeparation
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) : Prop :=
  ∀ t : ℝ,
    1 / (((2 ^ Fintype.card (PairQubit L) + 1 : ℕ) : ℝ)) <
      productStabilizerTwoQueryProtocolSignal
        (fun P : FiniteQLocalPauliLabel (PairQubit L) 2 => P.1)
        (finiteQLocalPauliTransferMatrix (PairQubit L) 2
          (nearestNeighborPathSelfAdjointHamiltonian L p) t)

theorem nearestNeighborPath_permanentLocalityHaarSeparation
    {L : ℕ} (hL : 0 < L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathLocalMaximalSet L)
    (hsep :
      Fintype.card (FiniteQLocalPauliLabel (PairQubit L) 2) * 3 ^ (2 : ℕ) <
        2 ^ Fintype.card (PairQubit L) + 1) :
    NearestNeighborPathPermanentLocalityHaarSeparation L p := by
  intro t
  exact finiteQLocalAutonomousTransferSignal_gt_haarBenchmark
    (PairQubit L) 2 (nearestNeighborPathSelfAdjointHamiltonian L p)
    (nearestNeighborPathSelfAdjointHamiltonian_ne_zero hL hp)
    (nearestNeighborPathSelfAdjointHamiltonian_hasPauliWeightAtMost_two L p)
    t hsep

/-- **Same-draw complexity/Haar-separation law.** For every finite gate alphabet and polynomial
depth exponent, all sufficiently long ordinary static nearest-neighbour chains admit one draw
which simultaneously has a robust laboratory-time complexity ramp, a literal double-exponential
excursion from the complete padded circuit dictionary, the matching endpoint complexity floor,
and a strict local two-query separation from exact Haar randomness at every real time. -/
theorem eventually_exists_nearestNeighborPath_polynomial_sameDraw_exponentialCircuitExcursion_and_permanentHaarSeparation
    (gate : Type*) [Fintype gate] (k : ℕ) :
    ∀ᶠ L : ℕ in atTop,
      ∀ (target : PaddedCircuitWord gate (L ^ k) →
          EuclideanSpace ℂ
            (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
              Fin (nearestNeighborPathProjectiveDimension L + 1))),
        (∀ w, ‖target w‖ = 1) →
        ∀ identityWord : PaddedCircuitWord gate (L ^ k),
          target identityWord =
            fullUniformPhaseChoiVector (nearestNeighborPathProjectiveDimension L + 1)
              (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
                (0 : Fin (nearestNeighborPathProjectiveDimension L) → UnitAddCircle)) →
          ∃ p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ,
            p ∈ nearestNeighborPathGaussianGrowthMaximalEvent L
              ((1 / 10000 : ℝ) * L) (1 / 10000 : ℝ) ∧
            p ∈ Metric.closedBall (inverseSquarePathLocalCenter L)
              (1 / ((L : ℝ) * (nearestNeighborPathLocalGeneratorMass L + 1))) ∧
            NearestNeighborPathExplicitCircuitExcursionFirstReturnGap
              L (L ^ k) p target (1 / 200 : ℝ)
                ((3 / 2 : ℝ) ^ (4 ^ L)) ∧
            ((⌊((1 / 10000 : ℝ) * L) /
                (256 * Real.pi * (1 / 10000 : ℝ))⌋₊ : ℕ) : ℕ∞) ≤
              operatorTwoGateComplexityTo L (1 / 10000 : ℝ)
                (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p)
                  ((1 / 10000 : ℝ) * L)) ∧
            NearestNeighborPathPermanentLocalityHaarSeparation L p := by
  filter_upwards [
    eventually_exists_nearestNeighborPath_polynomial_sameDraw_exponentialCircuitExcursion gate k,
    eventually_pairQubit_twoLocalPauli_separator,
    Filter.eventually_ge_atTop 1] with L hexists hsep hL
  intro target htarget identityWord hidentity
  obtain ⟨p, hgrowth, hball, hexcursion, hfloor⟩ :=
    hexists target htarget identityWord hidentity
  refine ⟨p, hgrowth, hball, hexcursion, hfloor, ?_⟩
  exact nearestNeighborPath_permanentLocalityHaarSeparation
    (by omega) hgrowth.1 hsep

end

end RHTower
