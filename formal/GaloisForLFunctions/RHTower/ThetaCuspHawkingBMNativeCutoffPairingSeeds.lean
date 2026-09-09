import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStripMeanAdmission

/-! The two unchanged source-dependent strip products for the cutoff Mellin pairing. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMGlobalAngularResponse
noncomputable section

/-- The actual lower-strip Mellin test against the complete original cutoff orbit. -/
def nativeCutoffLowerPair (q : XiZeroCopy) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  lowCuspPower s z.im * periodize (squareCutoffSeed q) z

/-- The original high cutoff profile against the full reverse orbit kernel. -/
def nativeCutoffUpperPair (q : XiZeroCopy) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  nativeSquareCutoffHeight q z.im * periodize (cuspHeightSeed (lowCuspPower s)) z

theorem nativeCutoffLowerPair_periodic (q : XiZeroCopy) (s : ℂ) (n : ℤ) (z : UpperHalfPlane) :
    nativeCutoffLowerPair q s (T^n • z) = nativeCutoffLowerPair q s z := by
  unfold nativeCutoffLowerPair
  rw [ModularGroup.im_T_zpow_smul]
  congr 1
  exact periodize_invariant _ (cuspTranslation n) z

theorem nativeCutoffUpperPair_periodic (q : XiZeroCopy) (s : ℂ) (n : ℤ) (z : UpperHalfPlane) :
    nativeCutoffUpperPair q s (T^n • z) = nativeCutoffUpperPair q s z := by
  unfold nativeCutoffUpperPair
  rw [ModularGroup.im_T_zpow_smul]
  congr 1
  exact periodize_invariant _ (cuspTranslation n) z

theorem nativeCutoffLowerPair_measurable (q : XiZeroCopy)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : Measurable (nativeCutoffLowerPair q P.s) := by
  have hm : Measurable (periodize (squareCutoffSeed q)) := by
    rw [squareCutoffSeed_eq_heightSeed q]
    exact periodize_measurable _ (cuspHeightSeed_measurable _ (nativeSquareCutoffHeight_continuous q).measurable)
  exact ((lowCuspPower_measurable P).comp continuous_im.measurable).mul hm

theorem nativeCutoffUpperPair_measurable (q : XiZeroCopy)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : Measurable (nativeCutoffUpperPair q P.s) :=
  (((nativeSquareCutoffHeight_continuous q).comp continuous_im).measurable).mul
    (lowCuspPower_periodize_measurable P)

theorem nativeCutoffLowerPair_zero (q : XiZeroCopy) (s : ℂ) (z : UpperHalfPlane) (hz : 1/2 < z.im) :
    nativeCutoffLowerPair q s z = 0 := by
  rw [nativeCutoffLowerPair,lowCuspPower,if_neg (not_le.mpr hz),zero_mul]

theorem nativeCutoffUpperPair_zero (q : XiZeroCopy) (s : ℂ) (z : UpperHalfPlane) (hz : z.im ≤ 2) :
    nativeCutoffUpperPair q s z = 0 := by
  rw [nativeCutoffUpperPair,nativeSquareCutoffHeight_zero q z.im hz,zero_mul]

end
end RHTower.D4BMJointSource
