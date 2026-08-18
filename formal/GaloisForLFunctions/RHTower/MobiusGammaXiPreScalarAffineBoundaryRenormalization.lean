import GaloisForLFunctions.RHTower.MobiusGammaXiPreScalarAffinePrimePolarGammaProducer

open Complex Filter Topology Matrix
open scoped ComplexOrder ENNReal InnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions

/-- Actual moving critical source packet at the zero clock. -/
def mobiusGammaXiPreScalarAffineMovingZeroClockPacket (j N : ℕ) :
    MobiusGammaXiPreScalarAffineProducerSpace :=
  mobiusGammaXiPreScalarAffineProducer
    4 2 3 3 (by norm_num) (by norm_num) (by norm_num) N
    (soninMobiusCriticalSigmaSequence j) 0
    (soninMobiusCriticalSigmaSequence_gt_one j) (by norm_num)
    (infiniteMobiusSignedWeightLp (soninMobiusCriticalSigmaSequence j)
      (soninMobiusCriticalSigmaSequence_gt_one j))

/-- Critical-clock normalization of the actual affine zero-mode readout. -/
def mobiusGammaXiPreScalarAffineNormalizedZeroModeReadout (j N : ℕ) : ℂ :=
  mobiusGammaXiPreScalarAffineReadout
      (soninMobiusCriticalSigmaSequence j) 0
      (soninMobiusCriticalSigmaSequence_gt_one j) (by norm_num)
      (mobiusGammaXiPreScalarAffineMovingZeroClockPacket j N) /
    (((soninMobiusCriticalSigmaSequence j - 1 : ℝ) : ℂ))

/-- The normalized zero-mode affine coefficient is the full completed source trace. -/
theorem mobiusGammaXiPreScalarAffineNormalizedZeroModeReadout_eq_transport
    (j N : ℕ) :
    mobiusGammaXiPreScalarAffineNormalizedZeroModeReadout j N =
      eulerPositiveGammaXiWardHilbertTransportAt
        (soninMobiusCriticalSigmaSequence j) 0
        (soninMobiusCriticalSigmaSequence_gt_one j) (by norm_num) := by
  let sigma := soninMobiusCriticalSigmaSequence j
  have hsigma : 1 < sigma := soninMobiusCriticalSigmaSequence_gt_one j
  have heps : (((sigma - 1 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr hsigma.ne')
  have hzeta : riemannZeta (sigma : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hsigma)
  rw [mobiusGammaXiPreScalarAffineNormalizedZeroModeReadout,
    mobiusGammaXiPreScalarAffineMovingZeroClockPacket,
    mobiusGammaXiPreScalarAffineReadout_zeroClock,
    eulerPositivePreScalarGammaXiNumerator_eq_denominator_mul_continued
      hsigma (by norm_num),
    eulerPositiveGammaXiWardHilbertTransportAt_eq_continuedSource
      hsigma (by norm_num)]
  unfold eulerPositivePreScalarGraphDenominator eulerAffineBoundaryOverlap
  simp only [ofReal_zero, zero_mul, add_zero, div_self hzeta, mul_one]
  change (((sigma - 1 : ℝ) : ℂ) *
      continuedPrimeArchSourceRelativeTrace
        (xiWardCenteredCoordinate
          (eulerPositiveCriticalBoundaryParameter sigma 0 : ℂ))) /
      (((sigma - 1 : ℝ) : ℂ)) =
    continuedPrimeArchSourceRelativeTrace
      (xiWardCenteredCoordinate
        (eulerPositiveCriticalBoundaryParameter sigma 0 : ℂ))
  field_simp [heps]

/-- Forced complementary divisor record in the zero-mode boundary chart. -/
def mobiusGammaXiPreScalarAffineBoundaryCorrection (j : ℕ) : ℂ :=
  -2 * I * logDeriv xiNonrightCanonicalProduct
      (I * mobiusGammaXiWardBoundaryNode
        (soninMobiusCriticalSigmaSequence j) 0) +
    xiAntiCausalWardBoundarySelfSymbol

/-- Coefficient-faithful boundary renormalization of the actual affine packet. -/
def mobiusGammaXiPreScalarAffineBoundaryRenormalization (j N : ℕ) : ℂ :=
  -2 * I * mobiusGammaXiPreScalarAffineNormalizedZeroModeReadout j N +
    mobiusGammaXiPreScalarAffineBoundaryCorrection j

/-- Exact finite-depth landing on the continued Ward coefficient. -/
theorem mobiusGammaXiPreScalarAffineBoundaryRenormalization_eq_ward
    (j N : ℕ) :
    mobiusGammaXiPreScalarAffineBoundaryRenormalization j N =
      continuedXiAntiCausalWardResponse
        (mobiusGammaXiWardBoundaryNode
          (soninMobiusCriticalSigmaSequence j) 0) := by
  let sigma := soninMobiusCriticalSigmaSequence j
  have hsigma : 1 < sigma := soninMobiusCriticalSigmaSequence_gt_one j
  have hbridge :=
    continuedXiAntiCausalWardResponse_eq_eulerFisherTransport_sub_complement
      hsigma (by norm_num : (0 : ℝ) ≤ 0)
  dsimp only at hbridge
  rw [mobiusGammaXiPreScalarAffineBoundaryRenormalization,
    mobiusGammaXiPreScalarAffineBoundaryCorrection,
    mobiusGammaXiPreScalarAffineNormalizedZeroModeReadout_eq_transport]
  simpa [sigma, mobiusGammaXiWardBoundaryNode, sub_eq_add_neg,
    add_assoc] using hbridge.symm

/-- Exact coefficient-faithful comparison with the base entry of every actual finite head. -/
theorem mobiusGammaXiPreScalarAffineBoundaryRenormalization_eq_sourceResponse_base
    (j N : ℕ) :
    mobiusGammaXiPreScalarAffineBoundaryRenormalization j N =
      mobiusGammaXiCoupledErrorSourceResponse j N
        (mobiusGammaXiCoupledErrorBaseIndex N) := by
  rw [mobiusGammaXiPreScalarAffineBoundaryRenormalization_eq_ward]
  rw [mobiusGammaXiCoupledErrorSourceResponse]
  simp only [mobiusGammaXiCoupledErrorBaseIndex,
    mobiusGammaXiCoupledErrorHeadNodes, Nat.cast_zero, zero_div,
    ofReal_zero, mobiusCriticalUniversalFisherScore]
  rw [mobiusGammaXiClockNormalizedTrueComplementDefect_eq
    (soninMobiusCriticalSigmaSequence_gt_one j) (by norm_num)]
  simp only [ofReal_zero]
  rw [squarefreeBoundaryOverlap_zeroClock
    (soninMobiusCriticalSigmaSequence_gt_one j)]
  simp

/-- The complementary correction is forced exactly by source-response fidelity. -/
theorem mobiusGammaXiPreScalarAffineBoundaryCorrection_eq_forcedDifference
    (j N : ℕ) :
    mobiusGammaXiPreScalarAffineBoundaryCorrection j =
      mobiusGammaXiCoupledErrorSourceResponse j N
          (mobiusGammaXiCoupledErrorBaseIndex N) -
        (-2 * I *
          mobiusGammaXiPreScalarAffineNormalizedZeroModeReadout j N) := by
  rw [← mobiusGammaXiPreScalarAffineBoundaryRenormalization_eq_sourceResponse_base]
  rw [mobiusGammaXiPreScalarAffineBoundaryRenormalization]
  ring

/-- Every moving affine zero-clock packet retains nonzero charge and zero odd jet. -/
theorem mobiusGammaXiPreScalarAffineMovingZeroClockPacket_provenance
    (j N : ℕ) :
    mobiusGammaXiPreScalarAffineMovingZeroClockPacket j N ≠ 0 ∧
      mobiusGammaXiPreScalarAffineOddJetPort
        (mobiusGammaXiPreScalarAffineMovingZeroClockPacket j N) = 0 := by
  constructor
  · exact mobiusGammaXiPreScalarAffineProducer_zeroClock_ne_zero
      4 2 3 3 (by norm_num) (by norm_num) (by norm_num) N
      (soninMobiusCriticalSigmaSequence j)
      (soninMobiusCriticalSigmaSequence_gt_one j)
      (infiniteMobiusSignedWeightLp (soninMobiusCriticalSigmaSequence j)
        (soninMobiusCriticalSigmaSequence_gt_one j))
  · exact mobiusGammaXiPreScalarAffineProducer_zeroClock_oddJet
      4 2 3 3 (by norm_num) (by norm_num) (by norm_num) N
      (soninMobiusCriticalSigmaSequence j)
      (soninMobiusCriticalSigmaSequence_gt_one j)
      (infiniteMobiusSignedWeightLp (soninMobiusCriticalSigmaSequence j)
        (soninMobiusCriticalSigmaSequence_gt_one j))

/-- Exact RH endpoint: coefficient-faithful fixed-four positivity is available
precisely when the transported radial coefficient vanishes. -/
theorem mobiusGammaXiPreScalarAffineBoundaryRenormalization_fourUnit_iff_rh :
    (∀ {n : ℕ} (u : Fin n → ℂ),
      (∀ i, 0 ≤ (u i).re) →
      (mobiusGammaXiCoupledErrorWallWithBudget u 4).PosSemidef) ↔
      RiemannHypothesis := by
  rw [all_mobiusGammaXiCoupledErrorWallWithBudget_posSemidef_iff]
  constructor
  · intro hbudget
    apply mobiusGammaXiCoupledErrorSingularGraphDebt_eq_zero_iff_rh.mp
    have hnonneg : 0 ≤ mobiusGammaXiCoupledErrorSingularGraphDebt :=
      Complex.normSq_nonneg _
    linarith
  · intro hRH
    have hzero : mobiusGammaXiCoupledErrorSingularGraphDebt = 0 :=
      mobiusGammaXiCoupledErrorSingularGraphDebt_eq_zero_iff_rh.mpr hRH
    rw [hzero]
    norm_num

/-- Premise-free capstone: exact finite comparison, cofinal transport, and RH endpoint. -/
theorem exists_mobiusGammaXiPreScalarAffineCoefficientFaithfulBoundaryRenormalization :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      (∀ N,
        (mobiusGammaXiCoupledErrorSourceCompletion (depth N) N).PosSemidef ∧
        IsSelfAdjoint
          (mobiusGammaXiCoupledErrorSourceOperator (depth N) N)) ∧
      (∀ N,
        mobiusGammaXiPreScalarAffineMovingZeroClockPacket (depth N) N ≠ 0 ∧
        mobiusGammaXiPreScalarAffineOddJetPort
          (mobiusGammaXiPreScalarAffineMovingZeroClockPacket (depth N) N) = 0 ∧
        mobiusGammaXiPreScalarAffineBoundaryRenormalization (depth N) N =
          mobiusGammaXiCoupledErrorSourceResponse (depth N) N
            (mobiusGammaXiCoupledErrorBaseIndex N)) ∧
      Tendsto (fun N =>
        mobiusGammaXiPreScalarAffineBoundaryRenormalization (depth N) N)
        atTop (nhds mobiusGammaXiCoupledErrorCriticalCoefficient) ∧
      (Tendsto (fun N =>
          mobiusGammaXiPreScalarAffineBoundaryRenormalization (depth N) N)
          atTop (nhds 0) ↔ RiemannHypothesis) ∧
      Tendsto (fun N => mobiusGammaXiCoupledErrorSourceBudget (depth N) N)
        atTop (nhds (4 + mobiusGammaXiCoupledErrorSingularGraphDebt)) := by
  obtain ⟨depth, hdepth, hsource, _hop, _hcolumn, _hrate,
      hbase, hbudget, hcritical⟩ :=
    exists_mobiusGammaXiMarkedZeroClockRate_boundaryTransport_debt
  have hcompare : ∀ N,
      mobiusGammaXiPreScalarAffineBoundaryRenormalization (depth N) N =
        mobiusGammaXiCoupledErrorSourceResponse (depth N) N
          (mobiusGammaXiCoupledErrorBaseIndex N) :=
    fun N =>
      mobiusGammaXiPreScalarAffineBoundaryRenormalization_eq_sourceResponse_base
        (depth N) N
  have hrenorm : Tendsto (fun N =>
      mobiusGammaXiPreScalarAffineBoundaryRenormalization (depth N) N)
      atTop (nhds mobiusGammaXiCoupledErrorCriticalCoefficient) := by
    refine hbase.congr' ?_
    exact Filter.Eventually.of_forall fun N => (hcompare N).symm
  have hzero :
      Tendsto (fun N =>
        mobiusGammaXiPreScalarAffineBoundaryRenormalization (depth N) N)
        atTop (nhds 0) ↔ RiemannHypothesis := by
    constructor
    · intro hz
      have hcoeff : mobiusGammaXiCoupledErrorCriticalCoefficient = 0 :=
        tendsto_nhds_unique hrenorm hz
      exact hcritical.mp hcoeff
    · intro hRH
      have hcoeff : mobiusGammaXiCoupledErrorCriticalCoefficient = 0 :=
        hcritical.mpr hRH
      simpa [hcoeff] using hrenorm
  refine ⟨depth, hdepth, hsource, ?_, hrenorm, hzero, hbudget⟩
  intro N
  exact ⟨(mobiusGammaXiPreScalarAffineMovingZeroClockPacket_provenance
      (depth N) N).1,
    (mobiusGammaXiPreScalarAffineMovingZeroClockPacket_provenance
      (depth N) N).2,
    hcompare N⟩

end RHTower
