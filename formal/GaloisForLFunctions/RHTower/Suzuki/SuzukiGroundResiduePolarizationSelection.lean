import GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimeArchDefectShiftSelection
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGroundEdgeCayleyUniversality

/-!
# Suzuki ground-residue polarization selection

The existing canonical first-defect shift selector used a simple even ground edge, which forces
the defect angle to `1`.  Simplicity and pure evenness are stronger than necessary.

If the rescaled even and odd resolvent energies converge at the spectral floor to masses
`mEven,mOdd`, then the ground-edge defect angle converges exactly to

`(mEven-mOdd)/(mEven+mOdd)`.

Consequently the canonical prime--Gamma matching shift still exists whenever

`(1+kappaXi) mOdd < (1-kappaXi) mEven`.

This is the exact bottom-eigenspace polarization threshold.  It permits arbitrary multiplicity
and mixed parity and replaces the simple-even-ground hypothesis by a quantitative source
projection inequality.  The corresponding odd/even threshold is positive and strictly smaller
than `4/81`.

No Riemann-hypothesis assumption or numerical computation occurs.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-! ## Ground-pole residue algebra -/

/-- Defect polarization of the even and odd bottom-eigenspace source residues. -/
def suzukiGroundResidueAngle (evenMass oddMass : ℝ) : ℝ :=
  GaloisForLFunctions.RHTower.suzukiDefectAngle evenMass oddMass

/-- Common rescaling of both parity energies does not change their defect angle. -/
theorem suzukiDefectAngle_common_scale
    {scale evenEnergy oddEnergy : ℝ} (hscale : scale ≠ 0) :
    GaloisForLFunctions.RHTower.suzukiDefectAngle
        (scale * evenEnergy) (scale * oddEnergy) =
      GaloisForLFunctions.RHTower.suzukiDefectAngle
        evenEnergy oddEnergy := by
  rw [GaloisForLFunctions.RHTower.suzukiDefectAngle,
    GaloisForLFunctions.RHTower.suzukiDefectAngle]
  field_simp [hscale]

/-- Rescaled parity-energy convergence transports exactly to ground-residue polarization. -/
theorem tendsto_suzukiDefectAngle_of_rescaled_energy
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (scale evenEnergy oddEnergy : ι → ℝ)
    {evenMass oddMass : ℝ}
    (hscale : ∀ᶠ j in l, scale j ≠ 0)
    (heven : Tendsto (fun j => scale j * evenEnergy j) l (nhds evenMass))
    (hodd : Tendsto (fun j => scale j * oddEnergy j) l (nhds oddMass))
    (hmass : evenMass + oddMass ≠ 0) :
    Tendsto
      (fun j => GaloisForLFunctions.RHTower.suzukiDefectAngle
        (evenEnergy j) (oddEnergy j))
      l (nhds (suzukiGroundResidueAngle evenMass oddMass)) := by
  have hscaled :
      Tendsto
        (fun j => GaloisForLFunctions.RHTower.suzukiDefectAngle
          (scale j * evenEnergy j) (scale j * oddEnergy j))
        l (nhds (suzukiGroundResidueAngle evenMass oddMass)) := by
    rw [suzukiGroundResidueAngle,
      GaloisForLFunctions.RHTower.suzukiDefectAngle]
    change Tendsto
      ((fun j => scale j * evenEnergy j - scale j * oddEnergy j) /
        (fun j => scale j * evenEnergy j + scale j * oddEnergy j))
      l (nhds ((evenMass - oddMass) / (evenMass + oddMass)))
    exact (heven.sub hodd).div (heven.add hodd) hmass
  refine hscaled.congr' ?_
  filter_upwards [hscale] with j hj
  exact suzukiDefectAngle_common_scale
    (scale := scale j) (evenEnergy := evenEnergy j)
    (oddEnergy := oddEnergy j) hj

/-- Exact spectral-floor version with the canonical pole scale `spectralFloor-lambda`. -/
theorem tendsto_suzukiDefectAngle_groundResidues
    (evenEnergy oddEnergy : ℝ → ℝ)
    {spectralFloor evenMass oddMass : ℝ}
    (heven : Tendsto
      (fun lambda => (spectralFloor - lambda) * evenEnergy lambda)
      (nhdsWithin spectralFloor (Iio spectralFloor)) (nhds evenMass))
    (hodd : Tendsto
      (fun lambda => (spectralFloor - lambda) * oddEnergy lambda)
      (nhdsWithin spectralFloor (Iio spectralFloor)) (nhds oddMass))
    (hmass : evenMass + oddMass ≠ 0) :
    Tendsto
      (fun lambda => GaloisForLFunctions.RHTower.suzukiDefectAngle
        (evenEnergy lambda) (oddEnergy lambda))
      (nhdsWithin spectralFloor (Iio spectralFloor))
      (nhds (suzukiGroundResidueAngle evenMass oddMass)) := by
  apply tendsto_suzukiDefectAngle_of_rescaled_energy
    (fun lambda => spectralFloor - lambda) evenEnergy oddEnergy
    _ heven hodd hmass
  filter_upwards [self_mem_nhdsWithin] with lambda hlambda
  exact sub_ne_zero.mpr (ne_of_gt hlambda)

/-! ## Exact target threshold -/

/-- A target lies below a positive-mass ground polarization exactly when the even residue beats
the odd residue by the displayed cross-multiplied threshold. -/
theorem target_lt_suzukiGroundResidueAngle_iff
    {target evenMass oddMass : ℝ}
    (hmass : 0 < evenMass + oddMass) :
    target < suzukiGroundResidueAngle evenMass oddMass ↔
      (1 + target) * oddMass < (1 - target) * evenMass := by
  rw [suzukiGroundResidueAngle,
    GaloisForLFunctions.RHTower.suzukiDefectAngle,
    lt_div_iff₀ hmass]
  constructor <;> intro h <;> nlinarith

/-- Exact odd/even bottom-residue ratio admitted by Xi's first Suzuki jet. -/
def primeArchSuzukiGroundOddEvenThreshold : ℝ :=
  (1 - primeArchSuzukiFirstDefectCalibration) /
    (1 + primeArchSuzukiFirstDefectCalibration)

/-- Xi's bottom-residue threshold is strictly positive and already below `4/81`. -/
theorem primeArchSuzukiGroundOddEvenThreshold_mem_Ioo :
    primeArchSuzukiGroundOddEvenThreshold ∈
      Ioo 0 ((4 : ℝ) / 81) := by
  have hk := primeArchSuzukiFirstDefectCalibration_mem_Ioo
  have hkpos : 0 < primeArchSuzukiFirstDefectCalibration :=
    lt_trans (by norm_num) hk.1
  have hden : 0 < 1 + primeArchSuzukiFirstDefectCalibration := by
    linarith
  constructor
  · rw [primeArchSuzukiGroundOddEvenThreshold]
    exact div_pos (by linarith [hk.2]) hden
  · rw [primeArchSuzukiGroundOddEvenThreshold, div_lt_iff₀ hden]
    nlinarith [hk.1]

/-- Ratio form of the exact Xi ground-residue polarization threshold. -/
theorem primeArchSuzuki_target_lt_groundResidueAngle_iff_ratio
    {evenMass oddMass : ℝ}
    (heven : 0 < evenMass) (hodd : 0 ≤ oddMass) :
    primeArchSuzukiFirstDefectCalibration <
        suzukiGroundResidueAngle evenMass oddMass ↔
      oddMass / evenMass < primeArchSuzukiGroundOddEvenThreshold := by
  have hmass : 0 < evenMass + oddMass := add_pos_of_pos_of_nonneg heven hodd
  rw [target_lt_suzukiGroundResidueAngle_iff hmass,
    primeArchSuzukiGroundOddEvenThreshold]
  have htargetDen :
      0 < 1 + primeArchSuzukiFirstDefectCalibration := by
    have hk := primeArchSuzukiFirstDefectCalibration_mem_Ioo
    have hkpos : 0 < primeArchSuzukiFirstDefectCalibration :=
      lt_trans (by norm_num) hk.1
    linarith
  rw [div_lt_div_iff₀ heven htargetDen]
  constructor <;> intro h <;> nlinarith

/-! ## Canonical matching-shift selection without simple ground parity -/

/-- Endpoint interpolation and greatest-root selection with an arbitrary upper endpoint. -/
theorem exists_isGreatest_suzukiDefectMatchingShiftSet_of_two_limits
    {angle : ℝ → ℝ} {spectralFloor free ground target : ℝ}
    (hcont : ContinuousOn angle (Iio spectralFloor))
    (hfree : Tendsto angle atBot (nhds free))
    (hground : Tendsto angle
      (nhdsWithin spectralFloor (Iio spectralFloor)) (nhds ground))
    (hfreeTarget : free < target) (htargetGround : target < ground) :
    ∃ lambdaStar,
      IsGreatest
        (suzukiDefectMatchingShiftSet angle spectralFloor target)
        lambdaStar := by
  let offset : ℝ := 1 - ground
  let normalizedAngle : ℝ → ℝ := fun lambda => angle lambda + offset
  let normalizedFree : ℝ := free + offset
  let normalizedTarget : ℝ := target + offset
  have hcont' : ContinuousOn normalizedAngle (Iio spectralFloor) := by
    exact hcont.add continuousOn_const
  have hfree' : Tendsto normalizedAngle atBot (nhds normalizedFree) := by
    exact hfree.add tendsto_const_nhds
  have hground' : Tendsto normalizedAngle
      (nhdsWithin spectralFloor (Iio spectralFloor)) (nhds 1) := by
    convert hground.add tendsto_const_nhds using 1 <;>
      simp only [normalizedAngle, offset] <;> ring
  obtain ⟨lambdaStar, hlambdaStar⟩ :=
    exists_isGreatest_suzukiDefectMatchingShiftSet_of_free_and_ground_limits
      (spectralFloor := spectralFloor) (free := normalizedFree)
      (target := normalizedTarget)
      hcont' hfree' hground' (by
        simp only [normalizedFree, normalizedTarget, offset]
        linarith) (by
        simp only [normalizedTarget, offset]
        linarith)
  have hsets :
      suzukiDefectMatchingShiftSet normalizedAngle spectralFloor normalizedTarget =
        suzukiDefectMatchingShiftSet angle spectralFloor target := by
    ext lambda
    simp only [suzukiDefectMatchingShiftSet, mem_setOf_eq,
      normalizedAngle, normalizedTarget, offset]
    constructor
    · intro h
      exact ⟨h.1, by linarith [h.2]⟩
    · intro h
      exact ⟨h.1, by linarith [h.2]⟩
  rw [hsets] at hlambdaStar
  exact ⟨lambdaStar, hlambdaStar⟩

/-- **Mixed-ground source selector.**  Rescaled bottom-eigenspace residues replace the simple-even
ground hypothesis.  The existing greatest-root selector is attained whenever the exact ground
polarization beats Xi's first defect jet. -/
theorem primeArchSuzukiGreatestDefectShift_spec_of_groundResidues
    (evenEnergy oddEnergy : ℝ → ℝ)
    {spectralFloor free evenMass oddMass : ℝ}
    (hcont : ContinuousOn
      (fun lambda => GaloisForLFunctions.RHTower.suzukiDefectAngle
        (evenEnergy lambda) (oddEnergy lambda))
      (Iio spectralFloor))
    (hfree : Tendsto
      (fun lambda => GaloisForLFunctions.RHTower.suzukiDefectAngle
        (evenEnergy lambda) (oddEnergy lambda))
      atBot (nhds free))
    (hevenResidue : Tendsto
      (fun lambda => (spectralFloor - lambda) * evenEnergy lambda)
      (nhdsWithin spectralFloor (Iio spectralFloor)) (nhds evenMass))
    (hoddResidue : Tendsto
      (fun lambda => (spectralFloor - lambda) * oddEnergy lambda)
      (nhdsWithin spectralFloor (Iio spectralFloor)) (nhds oddMass))
    (hmass : 0 < evenMass + oddMass)
    (hfreeCalibration : free < primeArchSuzukiFirstDefectCalibration)
    (hgroundPolarization :
      (1 + primeArchSuzukiFirstDefectCalibration) * oddMass <
        (1 - primeArchSuzukiFirstDefectCalibration) * evenMass) :
    IsGreatest
      (suzukiDefectMatchingShiftSet
        (fun lambda => GaloisForLFunctions.RHTower.suzukiDefectAngle
          (evenEnergy lambda) (oddEnergy lambda))
        spectralFloor primeArchSuzukiFirstDefectCalibration)
      (primeArchSuzukiGreatestDefectShift
        (fun lambda => GaloisForLFunctions.RHTower.suzukiDefectAngle
          (evenEnergy lambda) (oddEnergy lambda))
        spectralFloor) := by
  let angle : ℝ → ℝ := fun lambda =>
    GaloisForLFunctions.RHTower.suzukiDefectAngle
      (evenEnergy lambda) (oddEnergy lambda)
  have hground : Tendsto angle
      (nhdsWithin spectralFloor (Iio spectralFloor))
      (nhds (suzukiGroundResidueAngle evenMass oddMass)) := by
    exact tendsto_suzukiDefectAngle_groundResidues
      evenEnergy oddEnergy hevenResidue hoddResidue hmass.ne'
  have htargetGround :
      primeArchSuzukiFirstDefectCalibration <
        suzukiGroundResidueAngle evenMass oddMass :=
    (target_lt_suzukiGroundResidueAngle_iff hmass).mpr hgroundPolarization
  obtain ⟨lambdaStar, hlambdaStar⟩ :=
    exists_isGreatest_suzukiDefectMatchingShiftSet_of_two_limits
      hcont hfree hground hfreeCalibration htargetGround
  change IsGreatest
    (suzukiDefectMatchingShiftSet
      angle spectralFloor primeArchSuzukiFirstDefectCalibration)
    (primeArchSuzukiGreatestDefectShift angle spectralFloor)
  rw [primeArchSuzukiGreatestDefectShift, hlambdaStar.csSup_eq]
  exact hlambdaStar

end

end RHTower
