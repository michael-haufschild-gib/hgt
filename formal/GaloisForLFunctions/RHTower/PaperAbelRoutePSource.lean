import GaloisForLFunctions.RHTower.CriticalAbelRoutePAsymptoticBridge
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalCorrelationRegularity
import GaloisForLFunctions.HTGeometry.PaperCayleySourceBounds

/-!
# Full Abel and Route-P sources as continuous rays

The literal completed Abel moment and Route-P ray differ by a strictly
positive exponentially decaying correction. Their proven cofinal signed
excursions supply a common real interval in the image of every physical tail.
-/

namespace RHTower
noncomputable section
open Set Filter
open scoped Topology NNReal
open GaloisForLFunctions.HTGeometry

/-- The full completed Abel moment, with the native critical normalization. -/
def paperCompletedAbelRay (t : ℝ) : ℝ :=
  2 * Real.exp (-t) * criticalContinuousAbel (Real.exp t)

theorem paperCompletedAbelRay_eq_logProfile (t : ℝ) :
    paperCompletedAbelRay t = 2 * Real.exp (t / 2) * criticalAbelLogProfile t := by
  unfold paperCompletedAbelRay criticalAbelLogProfile
  rw [← mul_assoc, mul_assoc (2 : ℝ) (Real.exp (t / 2))
    (Real.exp (-(3 / 2 : ℝ) * t)), ← Real.exp_add]
  congr 3
  ring

theorem continuous_paperCompletedAbelRay : Continuous paperCompletedAbelRay := by
  have heq : paperCompletedAbelRay = fun t =>
      2 * Real.exp (t / 2) * criticalAbelLogProfile t :=
    funext paperCompletedAbelRay_eq_logProfile
  rw [heq]
  exact (continuous_const.mul (Real.continuous_exp.comp
    (continuous_id.div_const 2))).mul continuous_criticalAbelLogProfile

/-- Both full sources bundled as continuous maps, with no source-bound premise. -/
def paperCompletedAbelSource : C(ℝ, ℝ) :=
  ⟨paperCompletedAbelRay, continuous_paperCompletedAbelRay⟩

def paperRoutePSource : C(ℝ, ℝ) :=
  ⟨routePSourceRay,
    GaloisForLFunctions.RHTower.continuous_criticalMellinChebyshevResolventRayRepresentative⟩

theorem paperAbelRouteP_source_difference (t : ℝ≥0) :
    0 < paperCompletedAbelSource t - paperRoutePSource t ∧
      paperCompletedAbelSource t - paperRoutePSource t ≤
        (20 / 3) * Real.exp (-(t : ℝ) / 2) :=
  criticalAbel_routeP_difference_le t.2

private theorem tail_interval_of_oscillation {F : ℝ → ℝ} (hF : Continuous F)
    {δ : ℝ} (h : ∀ T : ℝ, (∃ t, T < t ∧ δ < F t) ∧ (∃ t, T < t ∧ F t < -δ))
    (T : ℝ) : Icc (-δ) δ ⊆ F '' Ioi T := by
  obtain ⟨⟨p, hp, hFp⟩, ⟨n, hn, hFn⟩⟩ := h T
  intro y hy
  exact isPreconnected_Ioi.intermediate_value hn hp hF.continuousOn
    ⟨hFn.le.trans hy.1, hy.2.trans hFp.le⟩

/-- A fixed nontrivial interval survives in both complete source images on every tail. -/
theorem paperAbelRouteP_common_tail_interval :
    ∃ δ : ℝ, 0 < δ ∧ ∀ T : ℝ,
      Icc (-δ) δ ⊆ paperCompletedAbelSource '' Ioi T ∧
      Icc (-δ) δ ⊆ paperRoutePSource '' Ioi T := by
  obtain ⟨a, ha, hA⟩ := criticalContinuousAbel_fixed_amplitude_two_sided
  obtain ⟨r, hr, hR⟩ := exists_routePSource_fixed_amplitude_two_sided
  refine ⟨min a r, lt_min ha hr, fun T => ⟨?_, ?_⟩⟩
  · apply Subset.trans _ (tail_interval_of_oscillation continuous_paperCompletedAbelRay hA T)
    intro y hy
    exact ⟨by linarith [hy.1, min_le_left a r], hy.2.trans (min_le_left a r)⟩
  · apply Subset.trans _ (tail_interval_of_oscillation paperRoutePSource.continuous hR T)
    intro y hy
    exact ⟨by linarith [hy.1, min_le_right a r], hy.2.trans (min_le_right a r)⟩

/-- The bounded encoding retains every signed value of the original sources. -/
theorem paperAbelRouteP_cayley_recovery (t : ℝ) :
    paperRealCayleyInverse (realCayley (paperCompletedAbelSource t)) =
      paperCompletedAbelSource t ∧
    paperRealCayleyInverse (realCayley (paperRoutePSource t)) = paperRoutePSource t :=
  ⟨paperRealCayleyInverse_apply _, paperRealCayleyInverse_apply _⟩

end
end RHTower
