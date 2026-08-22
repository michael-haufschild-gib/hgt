import GaloisForLFunctions.RHTower.MellinHeadHardy
import GaloisForLFunctions.RHTower.FractionalPartZeta

/-!
# The zeta quotient in the Hardy space of the half-plane

Abel summation writes `ζ(s)/s = 1/(s-1) - ∫_1^∞ {t} t^{-s-1} dt` on the right half-plane, and the
tail integrand `{t}/t` is square-integrable on `(1, ∞)`.  So `ζ(s)/s` is `1/(s-1)` plus the Mellin
transform of an `L²(1,∞)` datum, and the renormalised quotient `(s-1)ζ(s)/s²` lies in the Hardy
space of the half-plane.  This is the analytic input of Burnol's Proposition 4.2
(arXiv:math/0203120).

## Main results

* `memLp_two_fractOverId`
* `zeta_div_eq_laplaceRay`
* `isHalfPlaneHardy_zetaCore`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The fractional part divided by the identity: the `L²(1,∞)` datum behind `ζ(s)/s`. -/
def fractOverId : ℝ → ℂ := fun t => ((Int.fract t : ℝ) : ℂ) / ((t : ℝ) : ℂ)

theorem norm_fractOverId_le {t : ℝ} (ht : 1 < t) : ‖fractOverId t‖ ≤ t⁻¹ := by
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
  rw [fractOverId, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos ht0]
  rw [div_le_iff₀ ht0, inv_mul_cancel₀ (ne_of_gt ht0)]
  have h := Int.fract_lt_one t
  have h0 := Int.fract_nonneg t
  rw [abs_of_nonneg h0]
  linarith

theorem measurable_fractOverId : Measurable fractOverId := by
  unfold fractOverId
  exact measurable_fract_complex.div Complex.continuous_ofReal.measurable

theorem memLp_two_fractOverId : MemLp fractOverId 2 (volume.restrict (Ioi (1 : ℝ))) := by
  refine (memLp_two_iff_integrable_sq_norm
    measurable_fractOverId.aestronglyMeasurable).2 ?_
  have hmaj0 : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  have hmaj : IntegrableOn (fun t : ℝ => (t⁻¹) ^ 2) (Ioi (1 : ℝ)) := by
    refine hmaj0.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
    have h1 : (t⁻¹) ^ (2 : ℕ) = (t ^ (2 : ℕ))⁻¹ := by rw [inv_pow]
    rw [h1, ← Real.rpow_natCast t 2, ← Real.rpow_neg ht0.le]
    norm_num
  refine Integrable.mono' hmaj (measurable_fractOverId.norm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : (1 : ℝ) < t := ht
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht1
  have hb := norm_fractOverId_le ht1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

/-- The Mellin transform of the tail datum is the elementary half of Abel summation. -/
theorem mellinTail_fractOverId {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (∫ t in Ioi (1 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * fractOverId t)
      = 1 / (s - 1) - riemannZeta s / s := by
  rw [← integral_Ioi_one_fract_cpow_of_re_pos hs hs1]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht1 : (1 : ℝ) < t := ht
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht1
  have htne : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht0
  have hsplit : ((t : ℝ) : ℂ) ^ (-(s + 1)) = ((t : ℝ) : ℂ) ^ (-s) * (((t : ℝ) : ℂ))⁻¹ := by
    have hneg : (-(s + 1) : ℂ) = -s + (-1 : ℂ) := by ring
    rw [hneg, Complex.cpow_add _ _ htne, Complex.cpow_neg_one]
  rw [hsplit, fractOverId]
  field_simp

/-- **Abel summation in the Hardy chart.** -/
theorem zeta_div_eq_laplaceRay {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s / s = 1 / (s - 1) - laplaceRay (logChart 1 fractOverId) (s - 1 / 2) := by
  have h := mellinTail_fractOverId hs hs1
  rw [mellinTail_eq_laplaceRay one_pos fractOverId s] at h
  have hone : ((1 : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) = 1 := by
    rw [Complex.ofReal_one, Complex.one_cpow]
  rw [hone, one_mul] at h
  linear_combination h

/-- The renormalised zeta quotient, as a function of the half-plane variable `w = s - 1/2`. -/
theorem zetaCore_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hs0 : s ≠ 0) :
    (s - 1) * riemannZeta s / s ^ 2
      = s⁻¹ - ((s - 1) / s) * laplaceRay (logChart 1 fractOverId) (s - 1 / 2) := by
  have h := zeta_div_eq_laplaceRay hs hs1
  have hne : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hmul : (s - 1) * (riemannZeta s / s) / s
      = (s - 1) * (1 / (s - 1) - laplaceRay (logChart 1 fractOverId) (s - 1 / 2)) / s := by
    rw [h]
  have hleft : (s - 1) * (riemannZeta s / s) / s = (s - 1) * riemannZeta s / s ^ 2 := by
    field_simp
  have hright : (s - 1) * (1 / (s - 1) - laplaceRay (logChart 1 fractOverId) (s - 1 / 2)) / s
      = s⁻¹ - ((s - 1) / s) * laplaceRay (logChart 1 fractOverId) (s - 1 / 2) := by
    field_simp
  rw [← hleft, hmul, hright]

/-- **The renormalised zeta quotient lies in the Hardy space of the half-plane.** -/
theorem isHalfPlaneHardy_zetaCore :
    ∃ M : ℝ, IsHalfPlaneHardy
      (fun w => (w + 1 / 2)⁻¹
        + (-1 : ℂ) * ((w - 1 / 2) / (w + 1 / 2) * laplaceRay (logChart 1 fractOverId) w)) M := by
  have hhalf : (0 : ℝ) < ((1 : ℂ) / 2).re := by norm_num
  have h1 := isHalfPlaneHardy_inv_shift hhalf
  have h2 := isHalfPlaneHardy_laplaceRay (memLp_two_logChart one_pos memLp_two_fractOverId)
  have h2' := isHalfPlaneHardy_mul_of_bounded h2 differentiableOn_shift_ratio
    (C := 3) (fun w hw => norm_shift_ratio_le hw)
  have h2'' := isHalfPlaneHardy_const_mul h2' (-1 : ℂ)
  refine ⟨_, (isHalfPlaneHardy_add h1 h2'').congr (fun w _ => ?_)⟩
  ring

end

end RHTower
