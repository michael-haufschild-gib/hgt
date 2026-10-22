import GaloisForLFunctions.RHTower.Suzuki.SuzukiSmallApertureClosedDecomposition

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- Exact finite-aperture modulus defect on the complete real form domain. -/
theorem exists_suzukiRealFormDomainModulus_with_finiteSignDefect
    (a : SuzukiPrimeFreeSmallAperture)
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hq : q ∈ SuzukiLimitingRealFormDomain) :
    ∃ w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      w ∈ SuzukiLimitingRealFormDomain ∧
      suzukiLimitingLogFormEmbedding w =
        suzukiIntervalL2Modulus (suzukiLimitingLogFormEmbedding q) ∧
      suzukiSmallScaledClosedEnergy a w ≤
        suzukiSmallScaledClosedEnergy a q -
          ((1 / 2 : ℝ) - 4 * a.val * suzukiOriginCurvatureUnitBound) *
            suzukiIntervalPositiveMass (suzukiLimitingLogFormEmbedding q) *
            suzukiIntervalNegativeMass (suzukiLimitingLogFormEmbedding q) := by
  obtain ⟨w, hwreal, hwrep, hwlim⟩ :=
    exists_suzukiRealFormDomainModulus_with_signDefect q hq
  refine ⟨w, hwreal, hwrep, ?_⟩
  let f := suzukiLimitingLogFormEmbedding q
  let Rw := suzukiScaledRemainderClosedQuadratic a
    (suzukiLimitingLogFormEmbedding w)
  let Rq := suzukiScaledRemainderClosedQuadratic a f
  let P := suzukiIntervalPositiveMass f
  let N := suzukiIntervalNegativeMass f
  have him : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume, (f x).im = 0 :=
    suzukiLimitingLogFormEmbedding_im_eq_zero_ae_of_mem_realFormDomain hq
  have hremAbs :
      |suzukiScaledRemainderClosedQuadratic a (suzukiIntervalL2Modulus f) -
          suzukiScaledRemainderClosedQuadratic a f| ≤
        4 * suzukiOriginCurvatureUnitBound * P * N :=
    abs_suzukiScaledRemainderClosedQuadratic_modulus_sub_le a f him
  have hrem : Rq - Rw ≤
      4 * suzukiOriginCurvatureUnitBound * P * N := by
    dsimp only [Rw, Rq]
    rw [hwrep]
    calc
      suzukiScaledRemainderClosedQuadratic a f -
          suzukiScaledRemainderClosedQuadratic a (suzukiIntervalL2Modulus f) =
          -(suzukiScaledRemainderClosedQuadratic a (suzukiIntervalL2Modulus f) -
            suzukiScaledRemainderClosedQuadratic a f) := by ring
      _ ≤ |suzukiScaledRemainderClosedQuadratic a
          (suzukiIntervalL2Modulus f) -
            suzukiScaledRemainderClosedQuadratic a f| := neg_le_abs _
      _ ≤ 4 * suzukiOriginCurvatureUnitBound * P * N := hremAbs
  have hremScaled :
      a.val * (Rq - Rw) ≤
        a.val * (4 * suzukiOriginCurvatureUnitBound * P * N) :=
    mul_le_mul_of_nonneg_left hrem a.pos.le
  have hnorm :
      ‖suzukiLimitingLogFormEmbedding w‖ ^ 2 =
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2 := by
    rw [hwrep, norm_suzukiIntervalL2Modulus]
  rw [suzukiSmallScaledClosedEnergy_eq_limiting_sub_remainder,
    suzukiSmallScaledClosedEnergy_eq_limiting_sub_remainder, hnorm]
  change _ ≤ _ - ((1 / 2 : ℝ) - 4 * a.val *
    suzukiOriginCurvatureUnitBound) * P * N
  change (suzukiLimitingLogClosedForm w w).re ≤
      (suzukiLimitingLogClosedForm q q).re -
        (1 / 2 : ℝ) * P * N at hwlim
  dsimp only [Rq, Rw] at hremScaled ⊢
  nlinarith

def suzukiFiniteSignDefectCoefficient (a : ℝ) : ℝ :=
  (1 / 2 : ℝ) - 4 * a * suzukiOriginCurvatureUnitBound

theorem tendsto_suzukiFiniteSignDefectCoefficient :
    Tendsto suzukiFiniteSignDefectCoefficient (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  change Tendsto suzukiFiniteSignDefectCoefficient
    (𝓝 (0 : ℝ) ⊓ 𝓟 (Ioi 0)) (𝓝 (1 / 2 : ℝ))
  have h0 : Tendsto suzukiFiniteSignDefectCoefficient
      (𝓝 (0 : ℝ)) (𝓝 (suzukiFiniteSignDefectCoefficient 0)) := by
    unfold suzukiFiniteSignDefectCoefficient
    exact (continuous_const.sub
      ((continuous_const.mul continuous_id).mul continuous_const)).tendsto 0
  simpa [suzukiFiniteSignDefectCoefficient] using h0.mono_left inf_le_left

/-- Suzuki's strict finite modulus coefficient is positive throughout a punctured
neighborhood of aperture zero. -/
theorem eventually_suzukiFiniteSignDefectCoefficient_pos :
    ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < suzukiFiniteSignDefectCoefficient a :=
  tendsto_suzukiFiniteSignDefectCoefficient.eventually
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1 / 2))

end RHTower
