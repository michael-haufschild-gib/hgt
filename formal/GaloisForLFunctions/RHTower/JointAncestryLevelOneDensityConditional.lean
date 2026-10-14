import GaloisForLFunctions.RHTower.JointAncestryLevelOneDensityFourier
import GaloisForLFunctions.HTGeometry.TorusConditionalProductL2

/-! # Native finite-coordinate recovery of the signed JAS density -/

namespace RHTower

open MeasureTheory Filter GaloisForLFunctions.HTGeometry
open scoped BigOperators Topology

noncomputable section

theorem torusConditionalL2_jasLevelOneSectorLimit (P : Finset Nat.Primes) (q : XiZeroCopy) :
    torusConditionalL2 P (jasLevelOneSectorLimit q) = jasLevelOneSectorLp q P := by
  have hlim := (torusConditionalL2 P).continuous.tendsto _ |>.comp
    (tendsto_jasLevelOneSectorLp q)
  apply tendsto_nhds_unique hlim
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_subset_jasPrimePrefix P] with N hN
  exact (torusConditionalL2_torusFiniteProduct (jasLevelOneCircle q)
    (integral_jasLevelOneCircle q) hN).symm

theorem torusConditionalL2_jasLevelOneDensity (P : Finset Nat.Primes) :
    torusConditionalL2 P jasLevelOneDensity = jasLevelOneFiniteDensity P := by
  rw [jasLevelOneDensity, (torusConditionalL2 P).map_tsum
    summable_norm_lagWeight_smul_jasLevelOneSectorLimit.of_norm]
  simp only [map_smul, torusConditionalL2_jasLevelOneSectorLimit, jasLevelOneFiniteDensity]

theorem condExp_jasLevelOneDensity (P : Finset Nat.Primes) :
    (torusHaar Nat.Primes)[jasLevelOneDensity | torusCoordinateSigma P]
      =ᵐ[torusHaar Nat.Primes]
        fun x => jasZeroSumDensity (1 / 2) P (fun i => fourier 1 (x i)) := by
  have h := coeFn_torusConditionalL2 P jasLevelOneDensity
  rw [torusConditionalL2_jasLevelOneDensity] at h
  exact h.symm.trans (coeFn_jasLevelOneFiniteDensity P)

end

end RHTower
