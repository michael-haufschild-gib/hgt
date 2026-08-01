import GaloisForLFunctions.RHTower.SuzukiXiFirstDefectJet
import GaloisForLFunctions.HTGeometry.HyperbolicModulus

/-!
# Prime--Gamma selection of Suzuki's first-defect shift

The exact first anchored Livšic jet of the normalized Xi target is the source-only scalar
`primeArchSuzukiFirstDefectCalibration`.  At a fixed aperture, suppose Suzuki's defect-angle path
is continuous below its spectral floor, tends to its free value at the far-negative end, and tends
to `1` at a simple even ground edge.  If the free value is below the prime--Gamma calibration, the
intermediate value theorem produces a matching shift.

The root need not be unique: even and odd spectra alternate, so no monotonicity of the actual
defect angle is assumed.  Endpoint separation makes the entire root set compactly trapped away
from both ends.  It therefore has a unique greatest member.  Taking the supremum defines this
member canonically from the source path, without selecting an Xi zero or choosing an arbitrary
root.

The free defect `2a / sinh(2a)` tends to zero, whereas the prime--Gamma calibration is strictly
positive.  Hence the required free-end inequality holds at every sufficiently large aperture.
The remaining source gate is precisely continuity plus a cofinal simple-even-ground endpoint;
this file does not assume that gate has been proved for Suzuki's arithmetic operator.
-/

open Filter Set Topology

noncomputable section

namespace RHTower

/-- Admissible shifts at which a defect-angle path matches a prescribed target scalar. -/
def suzukiDefectMatchingShiftSet
    (angle : ℝ → ℝ) (spectralFloor target : ℝ) : Set ℝ :=
  {lambda | lambda < spectralFloor ∧ angle lambda = target}

/-- Endpoint interpolation for a continuous defect path below its spectral floor. -/
theorem exists_suzukiDefectMatchingShift_of_free_and_ground_limits
    {angle : ℝ → ℝ} {spectralFloor free target : ℝ}
    (hcont : ContinuousOn angle (Iio spectralFloor))
    (hfree : Tendsto angle atBot (nhds free))
    (hground : Tendsto angle (nhdsWithin spectralFloor (Iio spectralFloor)) (nhds 1))
    (hfreeTarget : free < target) (htargetOne : target < 1) :
    (suzukiDefectMatchingShiftSet angle spectralFloor target).Nonempty := by
  have hnear : ∀ᶠ y in nhdsWithin spectralFloor (Iio spectralFloor),
      target < angle y :=
    hground.eventually (Ioi_mem_nhds htargetOne)
  have hmem : ∀ᶠ y in nhdsWithin spectralFloor (Iio spectralFloor),
      y ∈ Iio spectralFloor := self_mem_nhdsWithin
  obtain ⟨y, hy, hyFloor⟩ := (hnear.and hmem).exists
  have hlow : ∀ᶠ x in atBot, angle x < target :=
    hfree.eventually (Iio_mem_nhds hfreeTarget)
  obtain ⟨x, hx, hxy⟩ := (hlow.and (Iio_mem_atBot y)).exists
  have hxyFloor : Icc x y ⊆ Iio spectralFloor := by
    intro z hz
    exact lt_of_le_of_lt hz.2 hyFloor
  have himage := intermediate_value_Icc hxy.le (hcont.mono hxyFloor)
    (show target ∈ Icc (angle x) (angle y) by exact ⟨hx.le, hy.le⟩)
  obtain ⟨lambda, hlambda, heq⟩ := himage
  exact ⟨lambda, hxyFloor hlambda, heq⟩

/-- **Canonical greatest-root law.**  Endpoint limits compactly trap every matching shift, so the
matching set has a greatest member without any monotonicity hypothesis on the defect path. -/
theorem exists_isGreatest_suzukiDefectMatchingShiftSet_of_free_and_ground_limits
    {angle : ℝ → ℝ} {spectralFloor free target : ℝ}
    (hcont : ContinuousOn angle (Iio spectralFloor))
    (hfree : Tendsto angle atBot (nhds free))
    (hground : Tendsto angle (nhdsWithin spectralFloor (Iio spectralFloor)) (nhds 1))
    (hfreeTarget : free < target) (htargetOne : target < 1) :
    ∃ lambdaStar,
      IsGreatest (suzukiDefectMatchingShiftSet angle spectralFloor target) lambdaStar := by
  obtain ⟨root, hrootFloor, hrootEq⟩ :=
    exists_suzukiDefectMatchingShift_of_free_and_ground_limits
      hcont hfree hground hfreeTarget htargetOne
  have hlow : {x : ℝ | angle x < target} ∈ atBot :=
    hfree.eventually (Iio_mem_nhds hfreeTarget)
  obtain ⟨lower, hlower⟩ := mem_atBot_sets.mp hlow
  have hnear : {x : ℝ | target < angle x} ∈
      nhdsWithin spectralFloor (Iio spectralFloor) :=
    hground.eventually (Ioi_mem_nhds htargetOne)
  obtain ⟨upper, hupperFloor, hupper⟩ :=
    mem_nhdsLT_iff_exists_Ioo_subset.mp hnear
  have root_lower : lower ≤ root := by
    by_contra h
    have hlt := hlower root (le_of_not_ge h)
    rw [mem_setOf_eq, hrootEq] at hlt
    exact (lt_irrefl target hlt)
  have root_upper : root ≤ upper := by
    by_contra h
    have hlt := hupper ⟨lt_of_not_ge h, hrootFloor⟩
    rw [mem_setOf_eq, hrootEq] at hlt
    exact (lt_irrefl target hlt)
  let trappedRoots : Set ℝ :=
    Icc lower upper ∩ angle ⁻¹' ({target} : Set ℝ)
  have hIccFloor : Icc lower upper ⊆ Iio spectralFloor := by
    intro x hx
    exact lt_of_le_of_lt hx.2 hupperFloor
  have hrootsClosed : IsClosed trappedRoots := by
    exact (hcont.mono hIccFloor).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  have hrootsCompact : IsCompact trappedRoots := by
    exact isCompact_Icc.of_isClosed_subset hrootsClosed inter_subset_left
  have hrootsNonempty : trappedRoots.Nonempty := by
    refine ⟨root, ⟨⟨root_lower, root_upper⟩, ?_⟩⟩
    exact Set.mem_preimage.mpr (by simpa only [Set.mem_singleton_iff] using hrootEq)
  obtain ⟨lambdaStar, hlambdaRoots, hlambdaMax⟩ :=
    hrootsCompact.exists_isMaxOn hrootsNonempty continuousOn_id
  have hlambdaFloor : lambdaStar < spectralFloor :=
    lt_of_le_of_lt hlambdaRoots.1.2 hupperFloor
  have hlambdaEq : angle lambdaStar = target :=
    Set.mem_singleton_iff.mp hlambdaRoots.2
  refine ⟨lambdaStar, ⟨hlambdaFloor, hlambdaEq⟩, ?_⟩
  intro lambda hlambda
  have lambda_lower : lower ≤ lambda := by
    by_contra h
    have hlt := hlower lambda (le_of_not_ge h)
    rw [mem_setOf_eq, hlambda.2] at hlt
    exact (lt_irrefl target hlt)
  have lambda_upper : lambda ≤ upper := by
    by_contra h
    have hlt := hupper ⟨lt_of_not_ge h, hlambda.1⟩
    rw [mem_setOf_eq, hlambda.2] at hlt
    exact (lt_irrefl target hlt)
  have hlambdaRoots : lambda ∈ trappedRoots := by
    exact ⟨⟨lambda_lower, lambda_upper⟩,
      Set.mem_preimage.mpr (by simpa only [Set.mem_singleton_iff] using hlambda.2)⟩
  have hmax : id lambda ≤ id lambdaStar := hlambdaMax hlambdaRoots
  exact hmax

/-- Greatest source shift matching the safe-Euler prime--Gamma Xi calibration.  The supremum is
defined for every path; endpoint laws below prove when it is an attained admissible root. -/
def primeArchSuzukiGreatestDefectShift
    (angle : ℝ → ℝ) (spectralFloor : ℝ) : ℝ :=
  sSup (suzukiDefectMatchingShiftSet
    angle spectralFloor primeArchSuzukiFirstDefectCalibration)

/-- Under the exact free and even-ground endpoint laws, the supremum selector is the attained,
unique greatest admissible shift matching the source-only Xi first-defect calibration. -/
theorem primeArchSuzukiGreatestDefectShift_spec
    {angle : ℝ → ℝ} {spectralFloor free : ℝ}
    (hcont : ContinuousOn angle (Iio spectralFloor))
    (hfree : Tendsto angle atBot (nhds free))
    (hground : Tendsto angle (nhdsWithin spectralFloor (Iio spectralFloor)) (nhds 1))
    (hfreeCalibration : free < primeArchSuzukiFirstDefectCalibration) :
    IsGreatest
      (suzukiDefectMatchingShiftSet
        angle spectralFloor primeArchSuzukiFirstDefectCalibration)
      (primeArchSuzukiGreatestDefectShift angle spectralFloor) := by
  obtain ⟨lambdaStar, hlambdaStar⟩ :=
    exists_isGreatest_suzukiDefectMatchingShiftSet_of_free_and_ground_limits
      hcont hfree hground hfreeCalibration
        primeArchSuzukiFirstDefectCalibration_mem_Ioo.2
  rw [primeArchSuzukiGreatestDefectShift, hlambdaStar.csSup_eq]
  exact hlambdaStar

/-- Cofinal apertures have free defect below the source-only Xi calibration. -/
theorem eventually_freeDefectAngle_lt_primeArchSuzukiFirstDefectCalibration :
    ∀ᶠ a : ℝ in atTop,
      2 * a / Real.sinh (2 * a) < primeArchSuzukiFirstDefectCalibration := by
  have hcalibrationPos : 0 < primeArchSuzukiFirstDefectCalibration :=
    lt_trans (by norm_num)
      primeArchSuzukiFirstDefectCalibration_mem_Ioo.1
  have hscale : Tendsto (fun a : ℝ => 2 * a) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num)).mpr tendsto_id
  have hlimit : Tendsto (fun a : ℝ => 2 * a / Real.sinh (2 * a)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      GaloisForLFunctions.HTGeometry.tendsto_freeDefectAngle_atTop.comp hscale
  exact hlimit.eventually (Iio_mem_nhds hcalibrationPos)

/-- **Cofinal source-selector law.**  If Suzuki's actual aperture-indexed defect paths are
continuous and have the free and simple-even-ground endpoint limits, then every sufficiently large
aperture has a canonical greatest shift matching the exact prime--Gamma Xi first jet. -/
theorem eventually_primeArchSuzukiGreatestDefectShift_spec
    (angle : ℝ → ℝ → ℝ) (spectralFloor : ℝ → ℝ)
    (hcont : ∀ a, ContinuousOn (angle a) (Iio (spectralFloor a)))
    (hfree : ∀ a, Tendsto (angle a) atBot
      (nhds (2 * a / Real.sinh (2 * a))))
    (hground : ∀ᶠ a : ℝ in atTop,
      Tendsto (angle a)
        (nhdsWithin (spectralFloor a) (Iio (spectralFloor a))) (nhds 1)) :
    ∀ᶠ a : ℝ in atTop,
      IsGreatest
        (suzukiDefectMatchingShiftSet
          (angle a) (spectralFloor a) primeArchSuzukiFirstDefectCalibration)
        (primeArchSuzukiGreatestDefectShift (angle a) (spectralFloor a)) := by
  filter_upwards
    [eventually_freeDefectAngle_lt_primeArchSuzukiFirstDefectCalibration, hground]
      with a hfreeCalibration hgroundLimit
  exact primeArchSuzukiGreatestDefectShift_spec
    (hcont a) (hfree a) hgroundLimit hfreeCalibration

end RHTower
