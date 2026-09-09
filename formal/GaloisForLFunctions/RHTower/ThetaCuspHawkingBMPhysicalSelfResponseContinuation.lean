import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalResolventIdentification
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalSelfAngularGaps
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalHorizonDomain

/-! The original complete physical response continues to both fundamental resonances of its own Xi copy. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Source-determined continuation of the original physical response at the same Xi source and target.
The denominator's nonvanishing is proved for every Xi copy, not assumed. -/
def continuedPhysicalSelfResponse (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (t : ℝ) : ℂ :=
  clearedPhysicalGreen q q branch w a t/physicalAngularGapProduct q q

/-- The constructed continuation is the actual physical profile on the original overlap. -/
theorem physicalCuspProfile_eq_continuedPhysicalSelfResponse (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (t : ℝ) (ht : t < 0) :
    physicalCuspProfile q q branch w a hw hd hwi hwr t = continuedPhysicalSelfResponse q branch w a t := by
  apply (eq_div_iff (physicalAngularGapProduct_self_ne_zero q)).mpr
  rw [mul_comm]
  exact physicalCuspProfile_mul_gapProduct q q branch w a hw hd hwi hwr t ht

/-- Identification retains the original Hilbert response class and every source channel. -/
theorem physicalCuspResponse_ae_continuedPhysicalSelfResponse (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    physicalCuspResponse q q branch w a hw hd hwi hwr =ᵐ[radialMeasure]
      continuedPhysicalSelfResponse q branch w a := by
  filter_upwards [physicalCuspProfile_ae q q branch w a hw hd hwi hwr,
    ae_restrict_mem measurableSet_Iio] with t hp ht
  exact hp.symm.trans (physicalCuspProfile_eq_continuedPhysicalSelfResponse q branch w a hw hd hwi hwr t ht)

/-- The literal complete-source endpoint Green integral has this same continuation on the overlap. -/
theorem completePhysicalGreenProfile_self_eq_continued (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) (t : ℝ) (ht : t < 0) :
    completePhysicalGreenProfile q q branch w a t = continuedPhysicalSelfResponse q branch w a t := by
  have hw : 0 < w.re := by linarith
  exact (physicalCuspProfile_eq_completePhysicalGreenProfile q q branch w a hw hd hwi hwr t ht).symm.trans
    (physicalCuspProfile_eq_continuedPhysicalSelfResponse q branch w a hw hd hwi hwr t ht)

/-- The actual same-copy physical response has a meromorphic continuation throughout the nonreal band. -/
theorem continuedPhysicalSelfResponse_meromorphicAt (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (t : ℝ) (ht : t < 0) :
    MeromorphicAt (fun v => continuedPhysicalSelfResponse q branch v a t) w :=
  (clearedPhysicalGreen_meromorphicAt q q branch w a hw hwr t ht).div
    (show AnalyticAt ℂ (fun _ : ℂ => physicalAngularGapProduct q q) w from analyticAt_const).meromorphicAt

/-- Every actual Xi copy has its complete physical response continued to both original fundamental QNMs.
Meromorphy does not assert a nonzero principal part or extinction. -/
theorem allXi_fundamental_physicalSelfResponse_meromorphic (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    ∀ w ∈ ({-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q),
      -Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)} : Set ℂ),
      ∀ t < 0, MeromorphicAt (fun v => continuedPhysicalSelfResponse q branch v a t) w := by
  intro w hw t ht
  have hs := allXi_fundamental_frequency_strip q w hw
  exact continuedPhysicalSelfResponse_meromorphicAt q branch w a hs.1 (abs_lt.mp hs.2).1 t ht

end
end RHTower.D4BMJointSource
