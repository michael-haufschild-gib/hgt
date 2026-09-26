import GaloisForLFunctions.HTGeometry.SchwartzTranslation
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Half-line Schwartz secant energy

Strong Schwartz translation convergence gives convergence of the squared L2
energy of finite secants on the positive half-line.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open scoped SchwartzMap
namespace GaloisForLFunctions.HTGeometry.SchwartzSecantEnergy

local instance : (volume.restrict (Ioi (0:ℝ))).HasTemperateGrowth where
  exists_integrable := ⟨volume.integrablePower,
    (Measure.integrable_pow_neg_integrablePower (volume : Measure ℝ)).integrableOn⟩

lemma schwartz_norm_toL2_sq (f : 𝓢(ℝ, ℂ)) :
    ‖f.toLp 2 (volume.restrict (Ioi (0:ℝ)))‖^2 = ∫ t in Ioi (0:ℝ), ‖f t‖^2 := by
  have h := congrArg (RCLike.re (K := ℂ))
    (SchwartzMap.inner_toL2_toL2_eq f f (volume.restrict (Ioi (0:ℝ))))
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
    integral_ofReal, RCLike.ofReal_re] at h
  convert! h using 1

lemma schwartz_secant_energy_tendsto (f : 𝓢(ℝ, ℂ)) :
    Tendsto (fun h : ℝ => ∫ t in Ioi (0:ℝ), ‖(f (t+h)-f t)/(h:ℂ)‖^2)
      (𝓝[≠] 0) (𝓝 (∫ t in Ioi (0:ℝ), ‖deriv f t‖^2)) := by
  have h := (SchwartzMap.continuous_toLp (p := 2)
    (μ := volume.restrict (Ioi (0:ℝ)))).continuousAt.tendsto.comp
      (SchwartzMap.tendsto_translateDifferenceQuotient f 0)
  have hn := h.norm.pow 2
  simp only [Function.comp_def, SchwartzMap.translateCLM_zero, schwartz_norm_toL2_sq,
    SchwartzMap.derivCLM_apply] at hn
  convert! hn using 1
  ext h
  change (∫ t in Ioi (0:ℝ), ‖(f (t+h)-f t)/(h:ℂ)‖^2) =
    ∫ t in Ioi (0:ℝ), ‖(h⁻¹:ℝ) • (f (t+(0+h))-f (t+0))‖^2
  simp only [zero_add, add_zero, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]

end GaloisForLFunctions.HTGeometry.SchwartzSecantEnergy
