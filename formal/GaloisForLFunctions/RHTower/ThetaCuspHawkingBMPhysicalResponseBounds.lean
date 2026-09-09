import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalResponseEndpoint
import GaloisForLFunctions.HTGeometry.RealSobolevBoundedProfile

/-! Global boundedness of the actual continuous physical response follows from its original Dirichlet domain. -/
open Complex Set Filter MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMJointWave GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The fixed physical representative is the zero extension throughout the nonnegative ray. -/
theorem physicalCuspProfile_nonnegative_zero (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (t : ℝ) (ht : 0 ≤ t) : physicalCuspProfile q r branch w a hw hd hwi hwr t = 0 :=
  (physicalCuspResponse_continuous_zero_trace q r branch w a hw hd hwi hwr).choose_spec.2.2 t ht

/-- The selected physical profile represents the original zero extension in whole-line L². -/
theorem physicalCuspProfile_ae_zeroExtension (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    physicalCuspProfile q r branch w a hw hd hwi hwr =ᵐ[volume]
      negativeZeroExtension (physicalCuspResponse q r branch w a hw hd hwi hwr) := by
  have ha := (ae_restrict_iff' measurableSet_Iio).mp (physicalCuspProfile_ae q r branch w a hw hd hwi hwr)
  filter_upwards [ha,negativeZeroExtension_ae (physicalCuspResponse q r branch w a hw hd hwi hwr)] with t ha he
  rw [he,negativeZeroExtensionFun]
  by_cases ht : t ∈ Iio (0:ℝ)
  · rw [indicator_of_mem ht,ha ht]
  · rw [indicator_of_notMem ht,physicalCuspProfile_nonnegative_zero q r branch w a hw hd hwi hwr t
      (le_of_not_gt ht)]

/-- The actual physical profile has whole-line L² admission, including its fixed zero extension. -/
theorem physicalCuspProfile_memLp (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    MemLp (physicalCuspProfile q r branch w a hw hd hwi hwr) 2 (volume : Measure ℝ) :=
  (Lp.memLp (negativeZeroExtension (physicalCuspResponse q r branch w a hw hd hwi hwr))).ae_eq
    (physicalCuspProfile_ae_zeroExtension q r branch w a hw hd hwi hwr).symm

/-- A uniform spatial bound is derived from the original physical response domain, without an outgoing bound premise. -/
theorem physicalCuspProfile_bounded (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖physicalCuspProfile q r branch w a hw hd hwi hwr t‖ ≤ C := by
  have hS := radialDirichlet_zeroExtension_sobolev
    ⟨_,physicalCuspResponse_radialDirichlet_mem q r branch w a hw hd hwi hwr⟩
  exact continuous_sobolev_bounded _ 1 (by norm_num) hS _
    (physicalCuspProfile_continuous q r branch w a hw hd hwi hwr)
    (physicalCuspProfile_ae_zeroExtension q r branch w a hw hd hwi hwr)

end
end RHTower.D4BMJointSource
