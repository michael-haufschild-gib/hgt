import GaloisForLFunctions.RHTower.Suzuki.SuzukiSmallApertureRemainderOperator

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

theorem continuous_suzukiSmallScaledClosedEnergy
    (a : SuzukiPrimeFreeSmallAperture) :
    Continuous (suzukiSmallScaledClosedEnergy a) := by
  exact (continuous_ccmRestrictedWeilSourceQuadratic ⟨a.val, a.pos⟩).comp
    (ccmArchimedeanUnitSmallFormEquiv a).continuous

theorem continuous_suzukiScaledRemainderClosedQuadratic
    (a : SuzukiPrimeFreeSmallAperture) :
    Continuous (suzukiScaledRemainderClosedQuadratic a) := by
  unfold suzukiScaledRemainderClosedQuadratic
  exact Complex.continuous_re.comp
    (((suzukiScaledRemainderOperator a).continuous.comp continuous_id).inner
      continuous_id)

/-- Exact finite-aperture energy decomposition on the complete fixed form domain. -/
theorem suzukiSmallScaledClosedEnergy_eq_limiting_sub_remainder
    (a : SuzukiPrimeFreeSmallAperture)
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiSmallScaledClosedEnergy a q =
      suzukiSmallApertureSpectralShift a.val *
          ‖suzukiLimitingLogFormEmbedding q‖ ^ 2 +
        (suzukiLimitingLogClosedForm q q).re -
          a.val * suzukiScaledRemainderClosedQuadratic a
            (suzukiLimitingLogFormEmbedding q) := by
  exact dense_suzukiLimitingComplexSmoothCore.induction
    (fun q hq => by
      rcases hq with ⟨u, rfl⟩
      rw [suzukiSmallScaledClosedEnergy_complexCore,
        suzukiPrimeFreeScaledForm_eq_limiting_sub_remainder,
        norm_sq_suzukiLimitingLogFormEmbedding_complexCore,
        suzukiLimitingLogClosedForm_complexCore_re_eq,
        suzukiScaledRemainderClosedQuadratic_complexCore])
    (isClosed_eq
      (continuous_suzukiSmallScaledClosedEnergy a)
      (((continuous_const.mul
          ((continuous_norm.comp
            suzukiLimitingLogFormEmbedding.continuous).pow 2)).add
        continuous_suzukiLimitingLogClosedEnergy).sub
          (continuous_const.mul
            ((continuous_suzukiScaledRemainderClosedQuadratic a).comp
              suzukiLimitingLogFormEmbedding.continuous))))
    q

end RHTower
