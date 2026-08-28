import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalLeftCoordinatePeierlsIncidence
import GaloisForLFunctions.RHTower.ThetaCuspHawkingPeierlsOrbitFourRouteNegativeSquareTransmutation

/-!
# Target-independent full-cokernel BM Peierls realization

The fixed global BM Peierls carrier, pairing, quadratic residual, and propagator support a canonical
retarded/advanced response split. Its complete nonlinear cokernel causal cut equals the literal BM
polarized current without divisor-dependent target fitting. The reflected unit-carrier orbit
therefore inherits the exact HB/FZZ-P/PW-B/RBH negative-square laws and RH endpoint.

`[NEW] [FULL COKERNEL] [GLOBAL PEIERLS PRODUCER] [FOUR-ROUTE CURRENT] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Complete nonlinear cokernel cut for the fixed global BM Peierls model, with the causal
propagator as retarded response and zero advanced response in both graded channels. -/
def hbXiPeierlsCanonicalFullCokernelCausalCutAt
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) : ℂ :=
  d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
    (hbXiPeierlsPairing (hbXiPeierlsMinusBranch amplitude q))
    hbXiPeierlsQuadraticResidual 0
    (hbXiPeierlsPropagator n) (hbXiPeierlsPropagator n) 0 0
    (hbXiPeierlsPlusBranch amplitude q)
    (hbXiPeierlsMinusBranch amplitude q)

/-- The canonical full-cokernel response split is exactly the global phase-normalized Peierls
cut; no target-dependent response scaling is used. -/
theorem hbXiPeierlsCanonicalFullCokernelCausalCutAt_eq_phaseNormalized
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) :
    hbXiPeierlsCanonicalFullCokernelCausalCutAt n amplitude q =
      d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut
        hbXiPeierlsPairing hbXiPeierlsQuadraticResidual
        (hbXiPeierlsPropagator n)
        (hbXiPeierlsPlusBranch amplitude q)
        (hbXiPeierlsMinusBranch amplitude q) := by
  unfold hbXiPeierlsCanonicalFullCokernelCausalCutAt
  apply d4GaugeFixedTeukolskyCokernelCausalCut_eq_phaseNormalizedPeierls
  · exact sub_zero (hbXiPeierlsPropagator n)
  · exact sub_zero (hbXiPeierlsPropagator n)

/-- Target-independent full-cokernel realization of the exact BM polarized candidate at the
canonical radial midpoint. -/
theorem hbXiPeierlsCanonicalFullCokernelCausalCutAt_eq_BM_candidate
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) :
    hbXiPeierlsCanonicalFullCokernelCausalCutAt n amplitude q =
      d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate
        n amplitude q (1 / 2) := by
  rw [hbXiPeierlsCanonicalFullCokernelCausalCutAt_eq_phaseNormalized]
  exact hbXiPeierls_phaseNormalizedCubicCut_eq_BM_candidate
    n amplitude q (by norm_num) (by norm_num)

/-- Unit-carrier specialization of the complete cokernel cut. -/
def hbXiPeierlsCanonicalFullCokernelUnitCarrierCutAt
    (n : ℕ) (q : XiZeroCopy) : ℂ :=
  hbXiPeierlsCanonicalFullCokernelCausalCutAt n
    (d4BMXiSecondHarmonicUnitCarrierAmplitude q) q

theorem hbXiPeierlsCanonicalFullCokernelUnitCarrierCutAt_eq
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsCanonicalFullCokernelUnitCarrierCutAt n q =
      d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n q (1 / 2) := by
  rw [hbXiPeierlsCanonicalFullCokernelUnitCarrierCutAt,
    hbXiPeierlsCanonicalFullCokernelCausalCutAt_eq_BM_candidate,
    d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate_unitCarrierAmplitude]

/-- Reflected orbit of the complete target-independent full-cokernel cut. -/
def hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut
    (n : ℕ) (q : XiZeroCopy) : ℂ :=
  hbXiPeierlsCanonicalFullCokernelUnitCarrierCutAt n q +
    hbXiPeierlsCanonicalFullCokernelUnitCarrierCutAt n
      (xiZeroCopyReflectEquiv q)

theorem hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q =
      d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n q := by
  unfold hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut
  rw [hbXiPeierlsCanonicalFullCokernelUnitCarrierCutAt_eq,
    hbXiPeierlsCanonicalFullCokernelUnitCarrierCutAt_eq]

/-- Every tilted Xi fibre makes the complete target-independent cokernel orbit strictly
negative. -/
theorem hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_re_neg_of_tilt
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    (hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q).re < 0 := by
  rw [hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq]
  exact d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_re_neg_of_tilt
    n q htilt

/-- Opposite-convention nonnegative orientation of the complete cokernel orbit occurs exactly on
the critical line. -/
theorem hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_re_nonneg_iff
    (n : ℕ) (q : XiZeroCopy) :
    0 ≤ (hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q).re ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq]
  exact d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_re_nonneg_iff n q

/-- Full-cokernel HB presentation: causal orbit is a negative multiple of canonical optical
power. -/
theorem hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_neg_hbOpticalPower
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q =
      -((d4BMXiHBOpticalPowerToPeierlsOrbitSusceptibility n q *
        hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q : ℝ) : ℂ) := by
  rw [hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq,
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_hbOpticalPower]

/-- Full-cokernel FZZ-P presentation. -/
theorem hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_neg_fzzForce_sq
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q =
      -((d4BMXiFZZInformationForceSquareToPeierlsOrbitSusceptibility n q *
        fzzCigarParityReflectedFermiInformationForce
          (deningerDivisorThetaEigen q).re ^ 2 : ℝ) : ℂ) := by
  rw [hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq,
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_fzzForce_sq]

/-- Full-cokernel every-grade PW-B presentation. -/
theorem hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_neg_pwImbalance_sq
    (n k : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q =
      -((d4BMXiPWImbalanceSquareToPeierlsOrbitSusceptibility n k q *
        schwarzschildParikhWilczekBorelPartnerRealImbalance
          (deningerDivisorThetaEigen q) k ^ 2 : ℝ) : ℂ) := by
  rw [hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq,
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_pwImbalance_sq]

/-- Full-cokernel actual-RBH presentation. -/
theorem hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_neg_rbhImbalance_sq
    (n : ℕ) (rho : XiDivisorSupport) :
    hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n
        (reflectedBiHeatFirstDivisorCopy rho) =
      -((d4BMXiRBHImbalanceSquareToPeierlsOrbitSusceptibility n rho *
        reflectedBiHeatMultiplicityLeadingJetNormImbalance rho ^ 2 : ℝ) : ℂ) := by
  rw [hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq,
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_rbhImbalance_sq]

/-- Universal extinction of one fixed target-independent complete cokernel orbit is RH. -/
theorem forall_hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_zero_iff_rh
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply (forall_d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_zero_iff_rh n).1
    intro q
    rw [← hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq]
    exact h q
  · intro hRH q
    rw [hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq]
    exact (forall_d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_zero_iff_rh n).2
      hRH q

/-- Universal opposite-convention nonnegative orientation of the complete target-independent
cokernel orbit is RH. -/
theorem forall_hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_re_nonneg_iff_rh
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      0 ≤ (hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q).re) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply
      (forall_d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_re_nonneg_iff_rh n).1
    intro q
    rw [← hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq]
    exact h q
  · intro hRH q
    rw [hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq]
    exact
      (forall_d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_re_nonneg_iff_rh n).2
        hRH q

end

end RHTower
