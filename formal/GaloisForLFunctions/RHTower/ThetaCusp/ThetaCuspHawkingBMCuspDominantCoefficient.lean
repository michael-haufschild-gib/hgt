import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspFluxReconstruction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The dominant cusp coefficient as an actual asymptotic limit of the global response.

The field is the original native energy response. Its identification with
continued retarded propagation and any extinction law remain separate.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMCuspResponse
open D4BMModularCore D4BMCuspProjection D4BMGlobalAngularResponse
noncomputable section

private theorem power_decay {c : ℂ} (hc : c.re < 0) :
    Tendsto (fun y : ℝ => (y:ℂ)^c) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (tendsto_rpow_neg_atTop (neg_pos.mpr hc))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

/-- The coefficient of the larger native cusp power is an actual asymptotic
limit of the original global response, with all compact-region data retained. -/
theorem responseMean_dominant_coefficient (q : XiZeroCopy) (branch : Bool) :
    Tendsto (fun y : ℝ => responseMean q branch y/(y:ℂ)^(root q branch true))
      atTop (𝓝 (limitingCoefficient q branch true)) := by
  have hr : (root q branch false-root q branch true).re < 0 := by
    have hb := (physicalRate_re_bounds q branch).2
    norm_num [root]
    linarith
  have h := ((responseFlux_tendsto q branch false).sub
    ((power_decay hr).mul (responseFlux_tendsto q branch true))).div_const (rootGap q branch)
  have h' : Tendsto (fun y : ℝ =>
      (responseFlux q branch false y-(y:ℂ)^(root q branch false-root q branch true)*
        responseFlux q branch true y)/rootGap q branch) atTop
        (𝓝 (limitingCoefficient q branch true)) := by
    simpa only [zero_mul,sub_zero,limitingCoefficient,if_true] using h
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  rw [responseMean_flux_reconstruction q branch hy,
    Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
  have hp : (y:ℂ)^(root q branch true) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
  field_simp [rootGap_ne_zero q branch,hp]

end
end RHTower.D4BMCuspResponse
