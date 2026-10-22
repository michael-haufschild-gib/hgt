import GaloisForLFunctions.RHTower.Suzuki.SuzukiGroundResiduePolarizationSelection

/-!
# Suzuki interior-excursion shift selection

Ground-residue polarization above the Xi first defect is a strong sufficient mechanism for
Suzuki's canonical shift, but it is not necessary.  If both endpoint angles lie below the target,
the defect path can still rise above it at an interior shift and cross twice.

This module keeps that surviving branch exact.  For a continuous defect path with finite
non-target limits at both ends, one literal matching witness is enough to compactly trap the whole
matching set and produce its greatest member.  If the free endpoint lies below the Xi calibration,
one strict interior overshoot supplies such a witness by the intermediate value theorem.

Thus the complete first-jet alternatives are:

* pole-driven selection from a ground reflection cone; or
* interior-excursion selection from a finite resolvent shift.

No monotonicity, root uniqueness, Riemann-hypothesis assumption, or numerical computation occurs.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-! ## Exact finite-shift balance -/

/-- A finite defect angle matches a target exactly when the two parity energies obey the
cross-multiplied balance law. -/
theorem suzukiDefectAngle_eq_target_iff
    {evenEnergy oddEnergy target : ℝ}
    (hsum : evenEnergy + oddEnergy ≠ 0) :
    GaloisForLFunctions.RHTower.suzukiDefectAngle evenEnergy oddEnergy = target ↔
      (1 + target) * oddEnergy = (1 - target) * evenEnergy := by
  rw [GaloisForLFunctions.RHTower.suzukiDefectAngle, div_eq_iff hsum]
  constructor <;> intro h <;> nlinarith

/-! ## Class-complete greatest-root selector -/

/-- If both endpoint limits avoid the target, any matching witness makes the entire matching set
compactly trapped and hence gives it a greatest member.  Endpoint ordering is irrelevant. -/
theorem exists_isGreatest_suzukiDefectMatchingShiftSet_of_witness
    {angle : ℝ → ℝ} {spectralFloor free ground target : ℝ}
    (hcont : ContinuousOn angle (Iio spectralFloor))
    (hfree : Tendsto angle atBot (nhds free))
    (hground : Tendsto angle
      (nhdsWithin spectralFloor (Iio spectralFloor)) (nhds ground))
    (hfreeNe : free ≠ target) (hgroundNe : ground ≠ target)
    (hwitness : (suzukiDefectMatchingShiftSet angle spectralFloor target).Nonempty) :
    ∃ lambdaStar,
      IsGreatest
        (suzukiDefectMatchingShiftSet angle spectralFloor target)
        lambdaStar := by
  obtain ⟨root, hrootFloor, hrootEq⟩ := hwitness
  have hlow : {x : ℝ | angle x ≠ target} ∈ atBot :=
    hfree.eventually (isOpen_compl_singleton.mem_nhds hfreeNe)
  obtain ⟨lower, hlower⟩ := mem_atBot_sets.mp hlow
  have hnear : {x : ℝ | angle x ≠ target} ∈
      nhdsWithin spectralFloor (Iio spectralFloor) :=
    hground.eventually (isOpen_compl_singleton.mem_nhds hgroundNe)
  obtain ⟨upper, hupperFloor, hupper⟩ :=
    mem_nhdsLT_iff_exists_Ioo_subset.mp hnear
  have root_lower : lower ≤ root := by
    by_contra h
    have hne := hlower root (le_of_not_ge h)
    rw [mem_setOf_eq] at hne
    exact hne hrootEq
  have root_upper : root ≤ upper := by
    by_contra h
    have hne := hupper ⟨lt_of_not_ge h, hrootFloor⟩
    rw [mem_setOf_eq] at hne
    exact hne hrootEq
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
    have hne := hlower lambda (le_of_not_ge h)
    rw [mem_setOf_eq] at hne
    exact hne hlambda.2
  have lambda_upper : lambda ≤ upper := by
    by_contra h
    have hne := hupper ⟨lt_of_not_ge h, hlambda.1⟩
    rw [mem_setOf_eq] at hne
    exact hne hlambda.2
  have hlambdaRoots : lambda ∈ trappedRoots := by
    exact ⟨⟨lambda_lower, lambda_upper⟩,
      Set.mem_preimage.mpr (by simpa only [Set.mem_singleton_iff] using hlambda.2)⟩
  have hmax : id lambda ≤ id lambdaStar := hlambdaMax hlambdaRoots
  exact hmax

/-! ## Interior overshoot branch -/

/-- A strict interior overshoot above a target, together with a free endpoint below it, produces
a literal matching shift.  No ground-end ordering is used. -/
theorem exists_suzukiDefectMatchingShift_of_interior_overshoot
    {angle : ℝ → ℝ} {spectralFloor free target witness : ℝ}
    (hcont : ContinuousOn angle (Iio spectralFloor))
    (hfree : Tendsto angle atBot (nhds free))
    (hfreeTarget : free < target)
    (hwitnessFloor : witness < spectralFloor)
    (hwitness : target < angle witness) :
    (suzukiDefectMatchingShiftSet angle spectralFloor target).Nonempty := by
  have hlow : ∀ᶠ x in atBot, angle x < target :=
    hfree.eventually (Iio_mem_nhds hfreeTarget)
  obtain ⟨x, hx, hxw⟩ := (hlow.and (Iio_mem_atBot witness)).exists
  have hinterval : Icc x witness ⊆ Iio spectralFloor := by
    intro z hz
    exact lt_of_le_of_lt hz.2 hwitnessFloor
  have himage := intermediate_value_Icc hxw.le (hcont.mono hinterval)
    (show target ∈ Icc (angle x) (angle witness) by exact ⟨hx.le, hwitness.le⟩)
  obtain ⟨lambda, hlambda, heq⟩ := himage
  exact ⟨lambda, hinterval hlambda, heq⟩

/-- Prime--Gamma capstone for the surviving interior-excursion branch.  A single strict finite
overshoot and a non-target ground limit make the canonical supremum selector an attained greatest
matching shift. -/
theorem primeArchSuzukiGreatestDefectShift_spec_of_interior_overshoot
    {angle : ℝ → ℝ} {spectralFloor free ground witness : ℝ}
    (hcont : ContinuousOn angle (Iio spectralFloor))
    (hfree : Tendsto angle atBot (nhds free))
    (hground : Tendsto angle
      (nhdsWithin spectralFloor (Iio spectralFloor)) (nhds ground))
    (hfreeCalibration : free < primeArchSuzukiFirstDefectCalibration)
    (hgroundNe : ground ≠ primeArchSuzukiFirstDefectCalibration)
    (hwitnessFloor : witness < spectralFloor)
    (hwitness :
      primeArchSuzukiFirstDefectCalibration < angle witness) :
    IsGreatest
      (suzukiDefectMatchingShiftSet
        angle spectralFloor primeArchSuzukiFirstDefectCalibration)
      (primeArchSuzukiGreatestDefectShift angle spectralFloor) := by
  have hroot :=
    exists_suzukiDefectMatchingShift_of_interior_overshoot
      hcont hfree hfreeCalibration hwitnessFloor hwitness
  obtain ⟨lambdaStar, hlambdaStar⟩ :=
    exists_isGreatest_suzukiDefectMatchingShiftSet_of_witness
      hcont hfree hground (ne_of_lt hfreeCalibration) hgroundNe hroot
  rw [primeArchSuzukiGreatestDefectShift, hlambdaStar.csSup_eq]
  exact hlambdaStar

end

end RHTower
