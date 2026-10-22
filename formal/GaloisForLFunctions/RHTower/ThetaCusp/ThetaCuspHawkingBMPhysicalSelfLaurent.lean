import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalSelfResidue
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! The full physical response has an analytic Laurent remainder, with an exact source-cancellation criterion. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem analytic_laurent_remainder {f : ℂ → ℂ} {w R : ℂ} (hm : MeromorphicAt f w)
    (hR : Tendsto (fun v => (v-w)*f v) (𝓝[≠] w) (𝓝 R)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ f =ᶠ[𝓝[≠] w] (fun v => R/(v-w)+g v) := by
  let F := Function.update (fun v => (v-w)*f v) w R
  have hM : MeromorphicAt F w :=
    ((show AnalyticAt ℂ (fun v : ℂ => v-w) w by fun_prop).meromorphicAt.mul hm).update w R
  have hF : AnalyticAt ℂ F w := hM.analyticAt (continuousAt_update_same.mpr hR)
  have hg : AnalyticAt ℂ (dslope F w) w := by
    obtain ⟨p,hp⟩ := hF
    exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  refine ⟨dslope F w,hg,?_⟩
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hvw : v ≠ w := hv
  rw [dslope_of_ne F hvw,slope_def_field]
  simp only [F,Function.update_of_ne hvw,Function.update_self]
  field_simp [sub_ne_zero.mpr hvw]
  ring

/-- There are no hidden higher poles: subtracting this exact coefficient leaves an analytic germ. -/
theorem continuedPhysicalSelfResponse_laurent_remainder (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (t : ℝ) (ht : t < 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (physicalFundamentalFrequency q side) ∧
      (fun w => continuedPhysicalSelfResponse q branch w a t) =ᶠ[𝓝[≠] physicalFundamentalFrequency q side]
        (fun w => physicalSelfResidueCoefficient q branch side a t/(w-physicalFundamentalFrequency q side)+g w) := by
  have hw := physicalFundamentalFrequency_strip q side
  exact analytic_laurent_remainder
    (continuedPhysicalSelfResponse_meromorphicAt q branch _ a hw.1 (abs_lt.mp hw.2).1 t ht)
    (continuedPhysicalSelfResponse_residue_tendsto q branch side a t ht)

/-- Finite continuation occurs precisely when the complete source Laurent coefficient vanishes. -/
theorem continuedPhysicalSelfResponse_finite_limit_iff (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (t : ℝ) (ht : t < 0) :
    (∃ c : ℂ, Tendsto (fun w => continuedPhysicalSelfResponse q branch w a t)
      (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 c)) ↔ physicalSelfResidueCoefficient q branch side a t = 0 := by
  constructor
  · rintro ⟨c,hc⟩
    have hx : Tendsto (fun w : ℂ => w) (𝓝[≠] physicalFundamentalFrequency q side)
        (𝓝 (physicalFundamentalFrequency q side)) := tendsto_id.mono_left nhdsWithin_le_nhds
    have h := (hx.sub_const (physicalFundamentalFrequency q side)).mul hc
    simp only [sub_self,zero_mul] at h
    exact tendsto_nhds_unique (continuedPhysicalSelfResponse_residue_tendsto q branch side a t ht) h
  · intro hR
    obtain ⟨g,hg,he⟩ := continuedPhysicalSelfResponse_laurent_remainder q branch side a t ht
    simp only [hR,zero_div,zero_add] at he
    exact ⟨g (physicalFundamentalFrequency q side),
      (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm⟩

/-- The remaining nonremovable-pole question is exactly the two retained source factors, with no spectral-denominator premise. -/
theorem continuedPhysicalSelfResponse_nonremovable_iff (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (t : ℝ) (ht : t < 0) :
    (¬ ∃ c : ℂ, Tendsto (fun w => continuedPhysicalSelfResponse q branch w a t)
      (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 c)) ↔
      physicalSelfSourceCoefficient q ≠ 0 ∧
      clearedReducedGreen (physicalFundamentalFrequency q side) (physicalRadialFrequency q)
        (physicalRate q branch) a t ≠ 0 := by
  rw [continuedPhysicalSelfResponse_finite_limit_iff q branch side a t ht,
    physicalSelfResidueCoefficient_zero_iff]
  exact not_or

end
end RHTower.D4BMJointSource
