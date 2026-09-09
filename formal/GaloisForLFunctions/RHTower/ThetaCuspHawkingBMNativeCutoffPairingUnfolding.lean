import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCutoffLowerAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCutoffUpperAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMHalfRowIntegralInterchange

/-! The original cutoff pairing unfolds in both directions with both absolute interchanges proved. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMGlobalAngularResponse
noncomputable section

/-- The entire lower-product half-row sum is the product of the two original orbit sums. -/
theorem nativeCutoffLowerPair_halfRow_sum (q : XiZeroCopy)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (z : UpperHalfPlane) :
    (∑' v : gammaSetHalf, nativeCutoffLowerPair q P.s (gammaSetMatrix v.1 • z)) =
      periodize (cuspHeightSeed (lowCuspPower P.s)) z * periodize (squareCutoffSeed q) z := by
  have he (v : gammaSetHalf) : nativeCutoffLowerPair q P.s (gammaSetMatrix v.1 • z) =
      lowCuspPower P.s (gammaSetMatrix v.1 • z).im * periodize (squareCutoffSeed q) z := by
    unfold nativeCutoffLowerPair
    congr 1
    exact periodize_invariant _ (QuotientGroup.mk (gammaSetMatrix v.1)) z
  simp_rw [he,tsum_mul_right]
  rw [periodize_cuspHeightSeed_eq_rows_of_rows_summable (lowCuspPower P.s) z (lowCuspPower_rows_summable P z)]

/-- The reverse-product sum preserves every original cutoff row and has the same two factors. -/
theorem nativeCutoffUpperPair_halfRow_sum (q : XiZeroCopy) (s : ℂ) (z : UpperHalfPlane) :
    (∑' v : gammaSetHalf, nativeCutoffUpperPair q s (gammaSetMatrix v.1 • z)) =
      periodize (squareCutoffSeed q) z * periodize (cuspHeightSeed (lowCuspPower s)) z := by
  have he (v : gammaSetHalf) : nativeCutoffUpperPair q s (gammaSetMatrix v.1 • z) =
      nativeSquareCutoffHeight q (gammaSetMatrix v.1 • z).im *
        periodize (cuspHeightSeed (lowCuspPower s)) z := by
    unfold nativeCutoffUpperPair
    congr 1
    exact periodize_invariant _ (QuotientGroup.mk (gammaSetMatrix v.1)) z
  simp_rw [he,tsum_mul_right]
  rw [squareCutoffSeed_periodize_eq_rows]

/-- The two literal source products have the same integral in the original hyperbolic strip measure. -/
theorem nativeCutoffPairing_unfold_both (q : XiZeroCopy) (s : ℂ) (hs : 2 < s.re) :
    (∫ z : UpperHalfPlane in modularStrip, nativeCutoffLowerPair q s z) =
      ∫ z : UpperHalfPlane in modularStrip, nativeCutoffUpperPair q s z := by
  let P : D4BMEisensteinAbsoluteConvergenceParameter := ⟨s,by linarith⟩
  have hl := modularStrip_integral_halfRow_sum (nativeCutoffLowerPair q s)
    (nativeCutoffLowerPair_periodic q s) (nativeCutoffLowerPair_integrable q s hs)
  have hu := modularStrip_integral_halfRow_sum (nativeCutoffUpperPair q s)
    (nativeCutoffUpperPair_periodic q s) (nativeCutoffUpperPair_integrable q s hs)
  have hsum (z : UpperHalfPlane) :
      (∑' v : gammaSetHalf, nativeCutoffLowerPair q s (gammaSetMatrix v.1 • z)) =
      periodize (cuspHeightSeed (lowCuspPower s)) z * periodize (squareCutoffSeed q) z :=
    nativeCutoffLowerPair_halfRow_sum q P z
  simp_rw [hsum] at hl
  simp_rw [nativeCutoffUpperPair_halfRow_sum q s] at hu
  rw [← hl,← hu]
  apply setIntegral_congr_fun isClosed_fd.measurableSet
  intro z _
  exact mul_comm _ _

end
end RHTower.D4BMJointSource
