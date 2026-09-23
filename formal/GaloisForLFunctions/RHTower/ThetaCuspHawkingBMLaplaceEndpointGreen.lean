import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSourceAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceWronskian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Genuine endpoint Green integrals acting on the original retained profile,
with independent transform frequency and derived integral derivatives. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMLaplaceRadial
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def horizonMoment (w chi s a J K T : ℂ) (z : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..z, horizon w chi t*sourceProfile s w a J K T t/(-connection w chi)

def outerMoment (w chi s a J K T : ℂ) (z : ℝ) : ℂ :=
  ∫ t in z..(1:ℝ), normalizable w chi t*sourceProfile s w a J K T t/(-connection w chi)

/-- The actual normalized Green integrands are integrable on the complete
closed endpoint interval. This justifies both improper endpoint moments. -/
theorem greenIntegrands_intervalIntegrable {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    IntervalIntegrable (fun t => horizon w chi t*sourceProfile s w a J K T t/(-connection w chi)) volume 0 1 ∧
    IntervalIntegrable (fun t => normalizable w chi t*sourceProfile s w a J K T t/(-connection w chi)) volume 0 1 := by
  have hi := sourceIntegrands_integrable h s a J K T
  constructor
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mpr (hi.1.div_const _)
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mpr (hi.2.div_const _)

/-- FTC for both genuine endpoint moments; no artificial interior cutoff or
integrability premise is used. -/
theorem greenMoments_derivatives {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ)
    {z : ℝ} (hz : z ∈ Ioo 0 1) :
    HasDerivAt (horizonMoment w chi s a J K T)
      (horizon w chi z*sourceProfile s w a J K T z/(-connection w chi)) z ∧
    HasDerivAt (outerMoment w chi s a J K T)
      (-(normalizable w chi z*sourceProfile s w a J K T z/(-connection w chi))) z := by
  have hi := greenIntegrands_intervalIntegrable h s a J K T
  have hc := sourceIntegrands_continuousOn h s a J K T
  have hH := hc.1.div_const (-connection w chi)
  have hV := hc.2.div_const (-connection w chi)
  constructor
  · exact intervalIntegral.integral_hasDerivAt_right (hi.1.mono_set (by
      rw [uIcc_of_le hz.1.le,uIcc_of_le (show (0:ℝ)≤1 by norm_num)]
      exact Icc_subset_Icc le_rfl hz.2.le))
      (hH.stronglyMeasurableAtFilter isOpen_Ioo z hz)
      (hH.continuousAt (isOpen_Ioo.mem_nhds hz))
  · exact intervalIntegral.integral_hasDerivAt_left (hi.2.mono_set (by
      rw [uIcc_of_le hz.2.le,uIcc_of_le (show (0:ℝ)≤1 by norm_num)]
      exact Icc_subset_Icc hz.1.le le_rfl))
      (hV.stronglyMeasurableAtFilter isOpen_Ioo z hz)
      (hV.continuousAt (isOpen_Ioo.mem_nhds hz))

def response (w chi s a J K T : ℂ) (z : ℝ) : ℂ :=
  normalizable w chi z*horizonMoment w chi s a J K T z+
    horizon w chi z*outerMoment w chi s a J K T z

def responseFirst (w chi s a J K T : ℂ) (z : ℝ) : ℂ :=
  normalizableFirst w chi z*horizonMoment w chi s a J K T z+
    horizonFirst w chi z*outerMoment w chi s a J K T z

def responseSecond (w chi s a J K T : ℂ) (z : ℝ) : ℂ :=
  normalizableSecond w chi z*horizonMoment w chi s a J K T z+
    horizonSecond w chi z*outerMoment w chi s a J K T z+
      (normalizableFirst w chi z*horizon w chi z-horizonFirst w chi z*normalizable w chi z)*
        sourceProfile s w a J K T z/(-connection w chi)

/-- The displayed full Green jet is the actual first and second derivative of
the retained-source response, including the moving-endpoint source term. -/
theorem response_derivatives {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ)
    {z : ℝ} (hz : z ∈ Ioo 0 1) :
    HasDerivAt (response w chi s a J K T) (responseFirst w chi s a J K T z) z ∧
    HasDerivAt (responseFirst w chi s a J K T) (responseSecond w chi s a J K T z) z := by
  obtain ⟨hA,hB⟩ := greenMoments_derivatives h s a J K T hz
  obtain ⟨hH,hH1⟩ := horizon_derivatives h hz
  obtain ⟨hV,hV1⟩ := normalizable_derivatives h hz
  constructor
  · convert! (hV.mul hA).add (hH.mul hB) using 1
    dsimp [responseFirst]
    ring
  · convert! (hV1.mul hA).add (hH1.mul hB) using 1
    dsimp [responseSecond]
    ring

/-- The genuine full-endpoint inverse solves the original physical radial
master with its exact retained source, not an assigned response jet. -/
theorem response_equation {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ)
    {z : ℝ} (hz : z ∈ Ioo 0 1) :
    D4BMPhysicalMaster.radialJet (Complex.I*w) chi z
      (response w chi s a J K T z) (responseFirst w chi s a J K T z)
      (responseSecond w chi s a J K T z) =
      (Real.sqrt (1-z):ℂ)*sourceProfile s w a J K T z/2 := by
  have hH := horizon_equation h hz
  have hV := normalizable_equation h hz
  have hW := wronskian_eq h hz
  have hc := connection_ne_zero h
  have hs : (Real.sqrt (1-z):ℂ)^(2 : ℕ)=1-(z:ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hz.2.le)
  dsimp [wronskian,integratingFactor] at hW
  rw [power_half_eq_sqrt (sub_nonneg.mpr hz.2.le)] at hW
  dsimp [D4BMPhysicalMaster.radialJet] at hH hV
  calc
    _ = (z:ℂ)*(1-z)*(normalizableFirst w chi z*horizon w chi z-
        horizonFirst w chi z*normalizable w chi z)*sourceProfile s w a J K T z/(-connection w chi) := by
      dsimp [response,responseFirst,responseSecond,D4BMPhysicalMaster.radialJet]
      linear_combination (horizonMoment w chi s a J K T z)*hV+
        (outerMoment w chi s a J K T z)*hH
    _ = (Real.sqrt (1-z):ℂ)*((z:ℂ)*(Real.sqrt (1-z):ℂ)*
        (horizon w chi z*normalizableFirst w chi z-horizonFirst w chi z*normalizable w chi z))*
          sourceProfile s w a J K T z/(-connection w chi) := by
      rw [← hs]
      ring
    _ = (Real.sqrt (1-z):ℂ)*(-connection w chi/2)*sourceProfile s w a J K T z/(-connection w chi) := by rw [hW]
    _ = _ := by field_simp [hc]

end
end RHTower.D4BMLaplaceRadial
