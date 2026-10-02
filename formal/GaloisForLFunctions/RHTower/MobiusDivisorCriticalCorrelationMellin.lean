import GaloisForLFunctions.RHTower.MobiusDivisorCriticalCorrelationSource
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalCorrelationRegularity

/-!
# The actual log-source Laplace transform is the source continuation

The exponential change of variable starts from the proved physical Abel
Mellin identity. The lower cutoff is retained using the source's exact zero
on `x ≤ 1`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower

private theorem abel_mellin_lower_cutoff (s : ℂ) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(s + 3 / 2) - 1) *
      (criticalContinuousAbel x : ℂ)) =
    ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-(s + 3 / 2) - 1) *
      (criticalContinuousAbel x : ℂ) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  congr 1
  funext x
  by_cases hx : 1 < x
  · simp [hx, (lt_trans zero_lt_one hx)]
  · have hz := criticalContinuousAbel_eq_zero_le_one (le_of_not_gt hx)
    by_cases hx0 : 0 < x
    · simp [hx, hx0, hz]
    · simp [hx, hx0]

private theorem abel_mellin_exp_integrand (s : ℂ) (t : ℝ) :
    (Real.exp t : ℂ) * ((Real.exp t : ℂ) ^ (-(s + 3 / 2) - 1) *
      (criticalContinuousAbel (Real.exp t) : ℂ)) =
    expRay s t * (criticalAbelLogProfile t : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
    ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]
  unfold expRay criticalAbelLogProfile
  push_cast
  rw [← mul_assoc, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The physical transform agrees with the pole-filled formula in its admitted half-plane. -/
theorem criticalAbelProfileLaplace_eq_continuation {s : ℂ} (hs : 0 < s.re) :
    criticalAbelProfileLaplace s = criticalAbelLaplaceContinuation s := by
  have hm := (hasMellin_criticalContinuousAbel
    (s := s + 3 / 2) (by simp; linarith)).2
  have hc := integral_image_eq_integral_abs_deriv_smul
    (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    (fun a _ b _ hab => Real.exp_injective hab)
    (fun x : ℝ => (x : ℂ) ^ (-(s + 3 / 2) - 1) *
      (criticalContinuousAbel x : ℂ))
  simp only [Real.image_exp_Ioi, Real.exp_zero, abs_of_pos (Real.exp_pos _),
    Complex.real_smul] at hc
  simp_rw [abel_mellin_exp_integrand] at hc
  change (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(s + 3 / 2) - 1) *
    (criticalContinuousAbel x : ℂ)) = _ at hm
  rw [abel_mellin_lower_cutoff, hc] at hm
  change criticalAbelProfileLaplace s = _ at hm
  rw [criticalAbelLaplaceContinuation_eq_step hs]
  simpa only [show s + 3 / 2 - 1 / 2 = 1 + s by ring,
    show 2 * (s + 3 / 2) = 3 + 2 * s by ring] using hm

/-- Boundary equality follows from admitted right limits, not from assuming a new moment. -/
theorem criticalAbelProfileLaplace_eq_continuation_boundary {s : ℂ}
    (hs : s.re = 0) (hL : ContinuousAt criticalAbelLaplaceContinuation s) :
    criticalAbelProfileLaplace s = criticalAbelLaplaceContinuation s := by
  have hx : Tendsto (fun ε : ℝ => s + (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 s) := by
    have hh : Continuous (fun ε : ℝ => s + (ε : ℂ)) :=
      continuous_const.add Complex.continuous_ofReal
    simpa only [Complex.ofReal_zero, add_zero] using (hh.tendsto (0 : ℝ)).mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hxR : Tendsto (fun ε : ℝ => s + (ε : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝[{z : ℂ | 0 ≤ z.re}] s) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hx, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [hs] using (le_of_lt hε : 0 ≤ ε)
  have hQ := (continuousOn_criticalAbelProfileLaplace s (by simp [hs])).tendsto.comp hxR
  have hLa := hL.tendsto.comp hx
  apply tendsto_nhds_unique hQ
  apply hLa.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (criticalAbelProfileLaplace_eq_continuation (by simpa [hs] using hε)).symm

end RHTower
