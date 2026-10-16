import GaloisForLFunctions.RHTower.PaperThetaUniformCutControl
import GaloisForLFunctions.HTGeometry.CauchySlopeRemainder

/-! # Strong parameter differentiation in the original global BV norm

The actual difference quotient converges to the literal first parameter jet
in point value plus total variation. The common two-tail control pays the
variation of its remainder, including the moving complex charge at the fixed
source cut. This is norm convergence of original functions, before any L²
quotient or arithmetic completion.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex Metric
open scoped ENNReal

namespace RHTower.PaperThetaEndpoint
open GaloisForLFunctions.HTGeometry

/-- Point value plus total variation; finite exactly on the global BV space. -/
def globalBVSize (f : ℝ → ℂ) : ℝ≥0∞ := ENNReal.ofReal ‖f 0‖ + eVariationOn f univ

def cutParameterSlopeRemainder (a : ℝ) (z h : ℂ) (x : ℝ) : ℂ :=
  h⁻¹ * (cutQuotient (z+h) a x - cutQuotient z a x) - cutParameterJet 1 z a x

private theorem jet_one_eq_deriv (a x : ℝ) (z : ℂ) :
    cutParameterJet 1 z a x = deriv (fun w => cutQuotient w a x) z := by
  simp only [cutParameterJet, iteratedDeriv_succ, iteratedDeriv_zero]

theorem cutParameterSlopeRemainder_norm (a : ℝ) (z : ℂ) {h : ℂ}
    (hh : h ≠ 0) (hsmall : ‖h‖ < 1/4) (x : ℝ) :
    ‖cutParameterSlopeRemainder a z h x‖ ≤ 8*(cutControlSize z a+1)*‖h‖ := by
  simpa only [cutParameterSlopeRemainder, jet_one_eq_deriv] using
    norm_cauchySlopeRemainder_le (differentiable_cutQuotient_parameter a x)
      z (cutControlSize z a+1) (fun w hw => cutQuotient_norm_ball z a x hw) hh hsmall

theorem cutParameterSlopeRemainder_increment (a : ℝ) (z : ℂ) {h : ℂ}
    (hh : h ≠ 0) (hsmall : ‖h‖ < 1/4) {x y : ℝ} (hxy : x ≤ y) :
    ‖cutParameterSlopeRemainder a z h y - cutParameterSlopeRemainder a z h x‖ ≤
      (8*‖h‖)*(cutVariationControl z a y-cutVariationControl z a x) := by
  let f : ℂ → ℂ := fun w => cutQuotient w a y - cutQuotient w a x
  have hf : Differentiable ℂ f := (differentiable_cutQuotient_parameter a y).sub
    (differentiable_cutQuotient_parameter a x)
  have hb (w : ℂ) (hw : w ∈ ball z 1) :
      ‖f w‖ ≤ cutVariationControl z a y-cutVariationControl z a x := by
    have he := cutQuotient_difference_ball z a y x hw
    rwa [abs_of_nonneg (sub_nonneg.mpr (monotone_cutVariationControl z a hxy))] at he
  have hd : deriv f z = cutParameterJet 1 z a y - cutParameterJet 1 z a x := by
    rw [jet_one_eq_deriv, jet_one_eq_deriv]
    exact deriv_sub ((differentiable_cutQuotient_parameter a y) z)
      ((differentiable_cutQuotient_parameter a x) z)
  have he := norm_cauchySlopeRemainder_le hf z _ hb hh hsmall
  have hid : h⁻¹*(f (z+h)-f z)-deriv f z =
      cutParameterSlopeRemainder a z h y-cutParameterSlopeRemainder a z h x := by
    rw [hd]
    dsimp [f, cutParameterSlopeRemainder]
    ring
  rw [hid] at he
  convert he using 1; ring

/-- The remainder's entire variation vanishes with the parameter increment. -/
theorem cutParameterSlopeRemainder_variation (a : ℝ) (z : ℂ) {h : ℂ}
    (hh : h ≠ 0) (hsmall : ‖h‖ < 1/4) :
    eVariationOn (cutParameterSlopeRemainder a z h) univ ≤
      ENNReal.ofReal ((8*‖h‖)*(2*cutControlSize z a)) := by
  apply iSup_le
  rintro ⟨N, ⟨u, hu, _⟩⟩
  let W := cutVariationControl z a
  have hinc (i : ℕ) : 0 ≤ W (u (i+1))-W (u i) :=
    sub_nonneg.mpr (monotone_cutVariationControl z a (hu (Nat.le_succ i)))
  calc
    (∑ i ∈ Finset.range N, edist (cutParameterSlopeRemainder a z h (u (i+1)))
        (cutParameterSlopeRemainder a z h (u i))) ≤
      ∑ i ∈ Finset.range N, ENNReal.ofReal ((8*‖h‖)*(W (u (i+1))-W (u i))) := by
        apply Finset.sum_le_sum
        intro i _
        rw [edist_dist, dist_eq_norm]
        exact ENNReal.ofReal_le_ofReal
          (cutParameterSlopeRemainder_increment a z hh hsmall (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal ((8*‖h‖)*(W (u N)-W (u 0))) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i (_ : i ∈ Finset.range N) =>
        mul_nonneg (by positivity) (hinc i)), ← Finset.mul_sum,
        Finset.sum_range_sub (fun i => W (u i)) N]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (sub_le_self _ (cutVariationControl_bounds z a (u 0)).1).trans
        (cutVariationControl_bounds z a (u N)).2

/-- Unconditional strong BV differentiation of the original cut family.
Both point-value error and total-variation error converge to zero. -/
theorem tendsto_cutParameterSlopeRemainder_globalBV (a : ℝ) (z : ℂ) :
    Tendsto (fun h : ℂ => globalBVSize (cutParameterSlopeRemainder a z h))
      (𝓝[≠] 0) (𝓝 0) := by
  have hev : ∀ᶠ h : ℂ in 𝓝[≠] 0, h ≠ 0 ∧ ‖h‖ < 1/4 := by
    have hb : ∀ᶠ h : ℂ in 𝓝 0, ‖h‖ < 1/4 := by
      filter_upwards [ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<1/4)] with h hh
      simpa only [mem_ball, dist_zero_right] using hh
    filter_upwards [self_mem_nhdsWithin, hb.filter_mono nhdsWithin_le_nhds] with h hh hs
    exact ⟨hh, hs⟩
  have hlim (C : ℝ) : Tendsto (fun h : ℂ => ENNReal.ofReal (C*‖h‖))
      (𝓝[≠] 0) (𝓝 0) := by
    have ht : Tendsto (fun h : ℂ => C*‖h‖) (𝓝[≠] 0) (𝓝 (C*‖(0:ℂ)‖)) :=
      ((continuous_const.mul continuous_norm).tendsto (0:ℂ)).mono_left nhdsWithin_le_nhds
    simpa only [norm_zero, mul_zero, ENNReal.ofReal_zero, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto (C*‖(0:ℂ)‖)).comp ht
  have hv : Tendsto (fun h : ℂ => eVariationOn (cutParameterSlopeRemainder a z h) univ)
      (𝓝[≠] 0) (𝓝 0) := by
    have hu : Tendsto (fun h : ℂ => ENNReal.ofReal ((8*‖h‖)*(2*cutControlSize z a)))
        (𝓝[≠] 0) (𝓝 0) := by
      convert hlim (8*(2*cutControlSize z a)) using 1
      funext h
      congr 1
      ring
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (Eventually.of_forall fun _ => bot_le)
      (hev.mono fun h hh => cutParameterSlopeRemainder_variation a z hh.1 hh.2)
  have hp : Tendsto (fun h : ℂ => ENNReal.ofReal ‖cutParameterSlopeRemainder a z h 0‖)
      (𝓝[≠] 0) (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (hlim (8*(cutControlSize z a+1))) (Eventually.of_forall fun _ => bot_le)
      (hev.mono fun h hh => ENNReal.ofReal_le_ofReal
        (cutParameterSlopeRemainder_norm a z hh.1 hh.2 0))
  simpa only [globalBVSize, zero_add] using hp.add hv

end RHTower.PaperThetaEndpoint
