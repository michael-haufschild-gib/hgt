import GaloisForLFunctions.RHTower.PositiveFieldGlobalConfocalFixedPointUniversalityLaw
import GaloisForLFunctions.RHTower.ScaleCovariantXiTransverseDefectBound
import GaloisForLFunctions.RHTower.XiEndpointCentralMomentBoundaryValue
import GaloisForLFunctions.RHTower.XiSquaredEulerApertureHilbertCorrelation

/-!
# Xi positive-field transverse-bound global-confocal universality

The actual reciprocal-square Xi divisor is an admissible atomic presentation for positive-field
tomography. Local agreement with any second admissible presentation forces a shared global
greatest confocal fixed-point branch, while the intrinsic Xi transverse envelope retains its
unconditional explicit bound.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Xi reciprocal-square atoms have cofinally vanishing HT transverse defect. -/
theorem tendsto_xiZeroCopyReciprocalSquare_transverseDefect_cofinite_zero :
    Tendsto
      (fun q : XiZeroCopy =>
        HTGeometry.transverseDefect (xiZeroCopyReciprocalSquare q))
      cofinite (nhds 0) := by
  have hzero : Tendsto xiZeroCopyReciprocalSquare cofinite (nhds 0) :=
    summable_xiZeroCopyReciprocalSquare.tendsto_cofinite_zero
  have hnorm := hzero.norm
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hzero
  simpa only [HTGeometry.transverseDefect, norm_zero, Complex.zero_re, sub_zero]
    using hnorm.sub hre

/-- The prime--Gamma moments are the exact atomic power moments of the Xi reciprocal-square
source when each atom also carries its own reciprocal-square weight. -/
theorem normalizedPrimeArchMoment_eq_xiReciprocalSquareAtomicPowerMoment
    (n : ℕ) :
    (normalizedPrimeArchMoment n : ℂ) =
      atomicPowerMoment xiZeroCopyReciprocalSquare
        xiZeroCopyReciprocalSquare n := by
  rw [ofReal_normalizedPrimeArchMoment_eq_xiCentralReciprocalMoment,
    atomicPowerMoment]
  rw [← tsum_xiZeroCopyReciprocalSquare_pow n]
  apply tsum_congr
  intro q
  ring

/-- **Xi positive-field transverse-bound global-confocal universality.**

Any admissible atomic presentation locally indistinguishable from the actual Xi moment source
shares its exterior greatest confocal fixed-point branch. Simultaneously, the intrinsic Xi
transverse envelope remains in its unconditional explicit interval. -/
theorem xiPositiveField_transverseBound_sharedGlobalConfocalUniversality
    {J : Type*} (d w : J → ℂ) (m' : ℕ → ℝ)
    (hd : Summable d)
    (htransW : Tendsto (fun j => HTGeometry.transverseDefect (w j))
      cofinite (nhds 0))
    {N a b : ℝ} (hN : 0 ≤ N)
    (hboundW : ∀ j, ‖w j‖ ≤ N)
    (hab : a < b)
    (hrealW : ∀ j, (w j).im = 0 → 0 ≤ (w j).re)
    (hmomentW : ∀ n, (m' n : ℂ) = atomicPowerMoment d w n)
    (hm0' : 0 < m' 0)
    (hobs : LocalPositiveScaleFieldAgrees normalizedPrimeArchMoment m' a b) :
    xiScaleCovariantTransverseDefect ∈ Set.Icc (0 : ℝ) (2 / 1681) ∧
      ∃ M : ℝ, 0 ≤ M ∧
        (∀ q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ≤ M) ∧
        normalizedPrimeArchMoment = m' ∧
        ∀ R ∈ Set.Ioi (max M N),
          HTGeometry.IsGreatestConfocalNullFixedPoint
              (HTGeometry.confocalLorentzLift ''
                Set.range
                  (atomicAggregateNode xiZeroCopyReciprocalSquare
                    xiZeroCopyReciprocalSquare)) R
              (HTGeometry.confocalGlobalDefect
                (HTGeometry.confocalLorentzLift ''
                  Set.range
                    (atomicAggregateNode xiZeroCopyReciprocalSquare
                      xiZeroCopyReciprocalSquare)) R) ∧
            HTGeometry.confocalGlobalDefect
                (HTGeometry.confocalLorentzLift ''
                  Set.range
                    (atomicAggregateNode xiZeroCopyReciprocalSquare
                      xiZeroCopyReciprocalSquare)) R =
              HTGeometry.confocalGlobalDefect
                (HTGeometry.confocalLorentzLift ''
                  Set.range (atomicAggregateNode d w)) R ∧
            HTGeometry.IsGreatestConfocalNullFixedPoint
              (HTGeometry.confocalLorentzLift ''
                Set.range (atomicAggregateNode d w)) R
              (HTGeometry.confocalGlobalDefect
                (HTGeometry.confocalLorentzLift ''
                  Set.range (atomicAggregateNode d w)) R) := by
  refine ⟨xiScaleCovariantTransverseDefect_mem_explicitInterval, ?_⟩
  obtain ⟨M, hM, hbound⟩ := exists_xiZeroCopyReciprocalSquare_norm_bound
  refine ⟨M, zero_le_one.trans hM, hbound, ?_⟩
  exact localPositiveScaleField_sharedGlobalConfocalGreatestFixedPoint
    xiZeroCopyReciprocalSquare xiZeroCopyReciprocalSquare d w
    normalizedPrimeArchMoment m'
    summable_xiZeroCopyReciprocalSquare hd
    tendsto_xiZeroCopyReciprocalSquare_transverseDefect_cofinite_zero htransW
    (zero_le_one.trans hM) hN hbound hboundW hab
    (fun q _ => (xiZeroCopyReciprocalSquare_re_pos q).le) hrealW
    normalizedPrimeArchMoment_eq_xiReciprocalSquareAtomicPowerMoment hmomentW
    normalizedPrimeArchMoment_zero_pos hm0' hobs

end

end RHTower
