import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFaithfulBranchCovarianceNoGo
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicCarrierNormalizedReflectionObstruction

/-!
# FE--Schwarz orbit trace of the global HB Peierls cut

HC15 forces any source-faithful off-wall continuation beyond two branches into the complete
four-sector FE--Schwarz real closure. This module performs that minimal orbit construction using
the single target-independent HC14 Peierls propagator and canonical sectorwise unit-carrier
sources.

The resulting orbit trace is automatically invariant under functional-equation reflection and
Schwarz conjugation, but it does not cancel. It is the strictly negative real quantity

`-4 * normSq(mixing(q)) * (8n + 5)`

and hence vanishes exactly on the critical wall; universal vanishing is equivalent to RH.
More generally, every reflection-invariant real weighting is classified exactly: it vanishes
either because its two conjugate-pair weights sum to zero, or because the Xi copy is critical.
Thus positive orbit averaging remains an RH detector, while the only unconditional signed
cancellation is a zero-total-weight character that erases the detector.

`[NEW] [FOUR-SECTOR LANDING] [ORBIT COVARIANCE] [WEIGHT CLASSIFICATION] [LEAN-PROVED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Schwarz conjugation preserves the exact squared helicity-mixing amplitude. -/
theorem normSq_d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_conj
    (q : XiZeroCopy) :
    Complex.normSq
        (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient
          (xiZeroCopyConjEquiv q)) =
      Complex.normSq
        (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) := by
  rw [normSq_d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient,
    normSq_d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient,
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_eq,
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_eq,
    xiSpectralPoint_copyConj]
  rw [show (-(starRingEnd ℂ) (xiSpectralPoint q)) ^ (2 : ℕ) =
      (starRingEnd ℂ) (xiSpectralPoint q) ^ (2 : ℕ) by ring]
  simp [pow_two, Complex.mul_im]
  ring

/-- HC14 global Peierls cut with the carrier normalized sectorwise to one. -/
def hbXiPeierlsUnitCarrierCubicCutAt
    (n : ℕ) (q : XiZeroCopy) : ℂ :=
  d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut
    hbXiPeierlsPairing hbXiPeierlsQuadraticResidual
    (hbXiPeierlsPropagator n)
    (hbXiPeierlsPlusBranch (d4BMXiSecondHarmonicUnitCarrierAmplitude q) q)
    (hbXiPeierlsMinusBranch (d4BMXiSecondHarmonicUnitCarrierAmplitude q) q)

theorem hbXiPeierlsUnitCarrierCubicCutAt_eq
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsUnitCarrierCubicCutAt n q =
      d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n q (1 / 2) := by
  rw [hbXiPeierlsUnitCarrierCubicCutAt,
    hbXiPeierls_phaseNormalizedCubicCut_eq_BM_candidate n
      (d4BMXiSecondHarmonicUnitCarrierAmplitude q) q
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1),
    d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate_unitCarrierAmplitude]

/-- Complete multiplicity-exact FE--Schwarz orbit trace of the global cubic cut. -/
def hbXiPeierlsFESchwarzOrbitCubicTrace
    (n : ℕ) (q : XiZeroCopy) : ℂ :=
  hbXiPeierlsUnitCarrierCubicCutAt n q +
    hbXiPeierlsUnitCarrierCubicCutAt n (xiZeroCopyReflectEquiv q) +
    hbXiPeierlsUnitCarrierCubicCutAt n (xiZeroCopyConjEquiv q) +
    hbXiPeierlsUnitCarrierCubicCutAt n
      (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q))

/-- The four sector contributions add with one sign and double the reflected-pair defect. -/
theorem hbXiPeierlsFESchwarzOrbitCubicTrace_eq
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsFESchwarzOrbitCubicTrace n q =
      -4 * (Complex.normSq
        (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) : ℂ) *
          (8 * (n : ℂ) + 5) := by
  rw [hbXiPeierlsFESchwarzOrbitCubicTrace,
    hbXiPeierlsUnitCarrierCubicCutAt_eq,
    hbXiPeierlsUnitCarrierCubicCutAt_eq,
    hbXiPeierlsUnitCarrierCubicCutAt_eq,
    hbXiPeierlsUnitCarrierCubicCutAt_eq]
  have hq :=
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut_reflection_add
      n q (z := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hc :=
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut_reflection_add
      n (xiZeroCopyConjEquiv q) (z := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  rw [show
      d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n q (1 / 2) +
          d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n
            (xiZeroCopyReflectEquiv q) (1 / 2) +
          d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n
            (xiZeroCopyConjEquiv q) (1 / 2) +
          d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n
            (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q)) (1 / 2) =
        (d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n q (1 / 2) +
          d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n
            (xiZeroCopyReflectEquiv q) (1 / 2)) +
        (d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n
            (xiZeroCopyConjEquiv q) (1 / 2) +
          d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n
            (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q)) (1 / 2)) by ring,
    hq, hc, normSq_d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_conj]
  ring

/-- The positive FE--Schwarz orbit trace vanishes exactly on the critical wall. -/
theorem hbXiPeierlsFESchwarzOrbitCubicTrace_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsFESchwarzOrbitCubicTrace n q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPeierlsFESchwarzOrbitCubicTrace_eq]
  have hn : 8 * (n : ℂ) + 5 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hpos : (0 : ℝ) < 8 * (n : ℝ) + 5 := by positivity
    exact hpos.ne' hre
  have hfour : (-4 : ℂ) ≠ 0 := by norm_num
  rw [mul_eq_zero, mul_eq_zero]
  simp only [hfour, false_or, hn, or_false,
    Complex.ofReal_eq_zero, Complex.normSq_eq_zero]
  exact d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q

/-- Orbit landing is automatically functional-equation invariant. -/
theorem hbXiPeierlsFESchwarzOrbitCubicTrace_reflect
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsFESchwarzOrbitCubicTrace n (xiZeroCopyReflectEquiv q) =
      hbXiPeierlsFESchwarzOrbitCubicTrace n q := by
  rw [hbXiPeierlsFESchwarzOrbitCubicTrace_eq,
    hbXiPeierlsFESchwarzOrbitCubicTrace_eq,
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_reflect]

/-- Orbit landing is automatically Schwarz invariant. -/
theorem hbXiPeierlsFESchwarzOrbitCubicTrace_conj
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsFESchwarzOrbitCubicTrace n (xiZeroCopyConjEquiv q) =
      hbXiPeierlsFESchwarzOrbitCubicTrace n q := by
  rw [hbXiPeierlsFESchwarzOrbitCubicTrace_eq,
    hbXiPeierlsFESchwarzOrbitCubicTrace_eq,
    normSq_d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_conj]

/-- Every tilted orbit carries a strictly negative real Peierls trace. -/
theorem hbXiPeierlsFESchwarzOrbitCubicTrace_re_neg_of_tilt
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    (hbXiPeierlsFESchwarzOrbitCubicTrace n q).re < 0 := by
  rw [hbXiPeierlsFESchwarzOrbitCubicTrace_eq]
  have hmix : d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q ≠ 0 :=
    (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).not.mpr htilt
  have hnorm : 0 < Complex.normSq
      (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) :=
    Complex.normSq_pos.mpr hmix
  norm_num
  positivity

/-- Universal four-sector orbit stationarity is equivalent to RH. -/
theorem forall_hbXiPeierlsFESchwarzOrbitCubicTrace_eq_zero_iff_rh
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      hbXiPeierlsFESchwarzOrbitCubicTrace n q = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis
      n).mp
    intro q
    apply (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff n q).mpr
    exact (hbXiPeierlsFESchwarzOrbitCubicTrace_eq_zero_iff n q).mp (h q)
  · intro hRH q
    apply (hbXiPeierlsFESchwarzOrbitCubicTrace_eq_zero_iff n q).mpr
    exact (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH) (q.1 : ℂ)
      (xi_eq_zero_of_mem_divisor_support q.1)

/-- Reflection-invariant weights on the two conjugate reflection pairs. -/
def hbXiPeierlsFESchwarzWeightedOrbitCubicTrace
    (n : ℕ) (q : XiZeroCopy) (a b : ℝ) : ℂ :=
  (a : ℂ) *
      (hbXiPeierlsUnitCarrierCubicCutAt n q +
        hbXiPeierlsUnitCarrierCubicCutAt n (xiZeroCopyReflectEquiv q)) +
    (b : ℂ) *
      (hbXiPeierlsUnitCarrierCubicCutAt n (xiZeroCopyConjEquiv q) +
        hbXiPeierlsUnitCarrierCubicCutAt n
          (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q)))

/-- Exact trace for arbitrary real weights on the two reflection pairs. -/
theorem hbXiPeierlsFESchwarzWeightedOrbitCubicTrace_eq
    (n : ℕ) (q : XiZeroCopy) (a b : ℝ) :
    hbXiPeierlsFESchwarzWeightedOrbitCubicTrace n q a b =
      -2 * (((a + b : ℝ) : ℂ)) *
        (Complex.normSq
          (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) : ℂ) *
        (8 * (n : ℂ) + 5) := by
  rw [hbXiPeierlsFESchwarzWeightedOrbitCubicTrace,
    hbXiPeierlsUnitCarrierCubicCutAt_eq,
    hbXiPeierlsUnitCarrierCubicCutAt_eq,
    hbXiPeierlsUnitCarrierCubicCutAt_eq,
    hbXiPeierlsUnitCarrierCubicCutAt_eq,
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut_reflection_add
      n q (z := (1 / 2 : ℝ)) (by norm_num) (by norm_num),
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut_reflection_add
      n (xiZeroCopyConjEquiv q) (z := (1 / 2 : ℝ)) (by norm_num) (by norm_num),
    normSq_d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_conj]
  push_cast
  ring

/-- Complete zero-locus classification for reflection-invariant real orbit weights. -/
theorem hbXiPeierlsFESchwarzWeightedOrbitCubicTrace_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) (a b : ℝ) :
    hbXiPeierlsFESchwarzWeightedOrbitCubicTrace n q a b = 0 ↔
      a + b = 0 ∨ (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPeierlsFESchwarzWeightedOrbitCubicTrace_eq]
  have hn : 8 * (n : ℂ) + 5 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hpos : (0 : ℝ) < 8 * (n : ℝ) + 5 := by positivity
    exact hpos.ne' hre
  have htwo : (-2 : ℂ) ≠ 0 := by norm_num
  rw [mul_eq_zero, mul_eq_zero, mul_eq_zero]
  simp only [htwo, false_or, hn, or_false, Complex.ofReal_eq_zero,
    Complex.normSq_eq_zero]
  rw [d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff]

/-- Every positive-total-weight orbit average retains the critical-wall detector. -/
theorem hbXiPeierlsFESchwarzWeightedOrbitCubicTrace_eq_zero_iff_of_pos
    (n : ℕ) (q : XiZeroCopy) (a b : ℝ) (hsum : 0 < a + b) :
    hbXiPeierlsFESchwarzWeightedOrbitCubicTrace n q a b = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [hbXiPeierlsFESchwarzWeightedOrbitCubicTrace_eq_zero_iff]
  exact or_iff_right hsum.ne'

/-- Opposite conjugate-pair weights cancel identically and therefore lose all RH information. -/
theorem hbXiPeierlsFESchwarzSignedOrbitCubicTrace_eq_zero
    (n : ℕ) (q : XiZeroCopy) (a : ℝ) :
    hbXiPeierlsFESchwarzWeightedOrbitCubicTrace n q a (-a) = 0 := by
  rw [hbXiPeierlsFESchwarzWeightedOrbitCubicTrace_eq]
  simp

end

end RHTower
