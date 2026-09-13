import GaloisForLFunctions.HTGeometry.CausalGammaHalfLaplace
import GaloisForLFunctions.HTGeometry.PoleClearedHalfKernel

/-!
# The pole-cleared half-kernel as a causal Gamma filter

The complete primitive subtraction in `poleClearedHalfKernel` is the real-rate
Gamma-half filter after exponential damping. This identifies the existing kernel
with an integrable causal source and proves its exact Laplace-square identity.
-/

open MeasureTheory Set Filter Topology
open scoped Convolution

noncomputable section
namespace GaloisForLFunctions.HTGeometry

theorem gammaHalfCausal_two_eq {t : ℝ} (ht : 0 < t) :
    gammaHalfCausal 2 t = (Complex.Gamma (1/2 : ℂ))⁻¹ *
      Complex.exp (-(3*(t : ℂ))) * (poleHalfKernel t : ℂ) := by
  rw [gammaHalfCausal, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht), poleHalfKernel]
  have hq := Complex.ofReal_cpow ht.le (-(1 : ℝ)/2)
  push_cast at hq ⊢
  rw [hq]
  have he : Complex.exp (-(3*(t : ℂ))) * Complex.exp (t : ℂ) =
      Complex.exp (-(2*(t : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    ring_nf
  calc
    _ = (Complex.Gamma (1/2 : ℂ))⁻¹ * Complex.exp (-(2*(t : ℂ))) *
        (t : ℂ)^(-(1/2 : ℂ)) := by ring_nf
    _ = _ := by rw [← he]; ring_nf

theorem causalExpThree_convolution_gammaHalf_two {t : ℝ} (ht : 0 < t) :
    (causalExpThree ⋆[ContinuousLinearMap.mul ℂ ℂ] gammaHalfCausal 2) t =
      (Complex.Gamma (1/2 : ℂ))⁻¹ * Complex.exp (-(3*(t : ℂ))) *
        ((∫ u in (0 : ℝ)..t, poleHalfKernel u) : ℂ) := by
  rw [convolution_eq_swap]
  have heq : (fun u : ℝ => causalExpThree (t-u) * gammaHalfCausal 2 u) =
      (Ioo 0 t).indicator (fun u : ℝ => (Complex.Gamma (1/2 : ℂ))⁻¹ *
        Complex.exp (-(3*(t : ℂ))) * (poleHalfKernel u : ℂ)) := by
    funext u
    by_cases hu : u ∈ Ioo 0 t
    · rw [indicator_of_mem hu, causalExpThree,
        indicator_of_mem (show t-u ∈ Ioi (0 : ℝ) from sub_pos.mpr hu.2),
        gammaHalfCausal_two_eq hu.1]
      have he : Complex.exp (-(3*((t-u : ℝ) : ℂ))) * Complex.exp (-(3*(u : ℂ))) =
          Complex.exp (-(3*(t : ℂ))) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring_nf
      calc
        _ = (Complex.Gamma (1/2 : ℂ))⁻¹ *
          (Complex.exp (-(3*((t-u : ℝ) : ℂ))) * Complex.exp (-(3*(u : ℂ)))) *
          (poleHalfKernel u : ℂ) := by ring_nf
        _ = _ := by rw [he]
    · rw [indicator_of_notMem hu]
      by_cases hu0 : u ≤ 0
      · rw [gammaHalfCausal_nonpos 2 hu0, mul_zero]
      · have htu : t-u ≤ 0 := by
          have hn : ¬ (0 < u ∧ u < t) := hu
          have hut : ¬ u < t := fun h => hn ⟨lt_of_not_ge hu0, h⟩
          linarith
        rw [causalExpThree_nonpos htu, zero_mul]
  change (∫ u : ℝ, causalExpThree (t-u) * gammaHalfCausal 2 u) = _
  rw [heq, integral_indicator measurableSet_Ioo, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
    intervalIntegral.integral_ofReal]

theorem filteredGammaHalf_two_eq_poleCleared {t : ℝ} (ht : 0 < t) :
    filteredGammaHalf 2 t = (Complex.Gamma (1/2 : ℂ))⁻¹ *
      Complex.exp (-(3*(t : ℂ))) * (poleClearedHalfKernel t : ℂ) := by
  rw [filteredGammaHalf, gammaHalfCausal_two_eq ht,
    causalExpThree_convolution_gammaHalf_two ht, poleClearedHalfKernel]
  push_cast
  rw [intervalIntegral.integral_ofReal]
  ring_nf

def dampedPoleHalfCausal : ℝ → ℂ :=
  (Ioi 0).indicator (fun t : ℝ => (Complex.Gamma (1/2 : ℂ))⁻¹ *
    Complex.exp (-(3*(t : ℂ))) * (poleClearedHalfKernel t : ℂ))

theorem dampedPoleHalfCausal_eq_filtered : dampedPoleHalfCausal = filteredGammaHalf 2 := by
  funext t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · rw [dampedPoleHalfCausal, indicator_of_mem ht, filteredGammaHalf_two_eq_poleCleared ht]
  · rw [dampedPoleHalfCausal, indicator_of_notMem ht,
      filteredGammaHalf_nonpos 2 (not_lt.mp ht)]

theorem dampedPoleHalfCausal_integrable : Integrable dampedPoleHalfCausal := by
  rw [dampedPoleHalfCausal_eq_filtered]
  exact filteredGammaHalf_integrable (by norm_num)

theorem dampedPoleHalfCausal_laplace_sq {s : ℂ} (hs : 0 ≤ s.re) :
    causalComplexLaplace s dampedPoleHalfCausal ^ 2 = (s+2)/(s+3)^2 := by
  rw [dampedPoleHalfCausal_eq_filtered]
  exact causalComplexLaplace_filteredGammaHalf_sq hs (by norm_num)

end GaloisForLFunctions.HTGeometry

