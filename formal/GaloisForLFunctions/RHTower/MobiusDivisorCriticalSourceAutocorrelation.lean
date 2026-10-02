import GaloisForLFunctions.RHTower.MobiusDivisorCriticalLogProfileTail
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exact signed autocorrelation balance of the actual Abel source

The literal boundary log profile has zero mass and a nonzero first moment.
Its full two-source autocorrelation therefore has a strictly negative second
signed moment. Absolute product admission and translation preserve both source
coordinates. In particular some positive lag has negative correlation.

This is a boundary correlation invariant. It does not bound correlations with
the critical exponential weight, or the cumulative original-cutoff action.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

private theorem profile_zero {t : ℝ} (ht : t ≤ 0) :
    criticalAbelLogProfile t = 0 := by
  have hx : Real.exp t ≤ 1 := by simpa using Real.exp_le_exp.mpr ht
  simp only [criticalAbelLogProfile, criticalContinuousAbel_eq_zero_le_one hx, mul_zero]

private theorem profile_weight_indicator (w : ℝ → ℝ) :
    (Ioi (0 : ℝ)).indicator (fun t => w t * criticalAbelLogProfile t) =
      fun t => w t * criticalAbelLogProfile t := by
  funext t
  by_cases ht : 0 < t
  · simp only [Set.indicator_apply, mem_Ioi, if_pos ht]
  · simp only [Set.indicator_apply, mem_Ioi, if_neg ht,
      profile_zero (le_of_not_gt ht), mul_zero]

private theorem profile_quadratic_integrable :
    Integrable (fun t : ℝ => (1 + t ^ (2 : ℕ)) * criticalAbelLogProfile t) := by
  rw [← profile_weight_indicator (fun t => 1 + t ^ (2 : ℕ))]
  exact (integrable_indicator_iff measurableSet_Ioi).mpr
    integrableOn_criticalAbelLogProfile_quadratic

private theorem profile_integrable : Integrable criticalAbelLogProfile := by
  apply profile_quadratic_integrable.norm.mono'
    measurable_criticalAbelLogProfile.aestronglyMeasurable
  filter_upwards with t
  simp only [norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 1 + t ^ (2 : ℕ))]
  nlinarith [abs_nonneg (criticalAbelLogProfile t), sq_nonneg t]

private theorem profile_first_integrable :
    Integrable (fun t : ℝ => t * criticalAbelLogProfile t) := by
  apply profile_quadratic_integrable.norm.mono'
    (measurable_id.mul measurable_criticalAbelLogProfile).aestronglyMeasurable
  filter_upwards with t
  dsimp only [Pi.mul_apply, id_eq]
  simp only [norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 1 + t ^ (2 : ℕ))]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  nlinarith [sq_nonneg (|t| - 1), sq_abs t, abs_nonneg t]

private theorem profile_second_integrable :
    Integrable (fun t : ℝ => t ^ (2 : ℕ) * criticalAbelLogProfile t) := by
  apply (profile_quadratic_integrable.sub profile_integrable).congr
  filter_upwards with t
  dsimp only [Pi.sub_apply]
  ring

private theorem profile_mass : (∫ t : ℝ, criticalAbelLogProfile t) = 0 := by
  have h := integral_indicator (μ := volume) (s := Ioi (0 : ℝ))
    (f := fun t : ℝ => 1 * criticalAbelLogProfile t) measurableSet_Ioi
  rw [profile_weight_indicator] at h
  simpa only [one_mul, criticalAbelLogProfile_mass_zero] using h

private theorem profile_first :
    (∫ t : ℝ, t * criticalAbelLogProfile t) = -(divisorHarmonicBoundary / 3) := by
  have h := integral_indicator (μ := volume) (s := Ioi (0 : ℝ))
    (f := fun t : ℝ => t * criticalAbelLogProfile t) measurableSet_Ioi
  rw [profile_weight_indicator, criticalAbelLogProfile_first_moment] at h
  exact h

private theorem profile_bounded (t : ℝ) :
    |criticalAbelLogProfile t| ≤
      ∫ u in Ioi (0 : ℝ), |criticalAbelLogVelocity u| := by
  by_cases ht : 0 ≤ t
  · rw [criticalAbelLogProfile_eq_velocity_tail ht, abs_neg]
    calc
      _ ≤ ∫ u in Ioi t, |criticalAbelLogVelocity u| := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := volume.restrict (Ioi t))
            criticalAbelLogVelocity
      _ ≤ _ := by
        apply setIntegral_mono_set integrableOn_criticalAbelLogVelocity.norm
        · exact Filter.Eventually.of_forall (fun _ => abs_nonneg _)
        · exact Filter.Eventually.of_forall (fun _ hx => (Ioi_subset_Ioi ht) hx)
  · rw [profile_zero (le_of_not_ge ht), abs_zero]
    exact integral_nonneg (fun _ => abs_nonneg _)

/-- The full translated signed product is admitted at every real lag. -/
theorem integrable_criticalAbelLogProfile_translated_product (lag : ℝ) :
    Integrable (fun t : ℝ =>
      criticalAbelLogProfile (t + lag) * criticalAbelLogProfile t) := by
  apply (profile_integrable.norm.const_mul
    (∫ u in Ioi (0 : ℝ), |criticalAbelLogVelocity u|)).mono'
    ((measurable_criticalAbelLogProfile.comp (measurable_id.add_const lag)).mul
      measurable_criticalAbelLogProfile).aestronglyMeasurable
  filter_upwards with t
  dsimp only [Pi.mul_apply, Function.comp_apply, id_eq]
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (profile_bounded (t + lag)) (abs_nonneg _)

/-- Autocorrelation of the literal critical Abel boundary log profile. -/
def criticalAbelLogAutocorrelation (lag : ℝ) : ℝ :=
  ∫ t : ℝ, criticalAbelLogProfile (t + lag) * criticalAbelLogProfile t

private theorem pair_second_integrable :
    Integrable (fun z : ℝ × ℝ =>
      (z.1 - z.2) ^ (2 : ℕ) * criticalAbelLogProfile z.1 * criticalAbelLogProfile z.2)
      (volume.prod volume) := by
  apply (((profile_second_integrable.mul_prod profile_integrable).sub
    ((profile_first_integrable.mul_prod profile_first_integrable).const_mul 2)).add
      (profile_integrable.mul_prod profile_second_integrable)).congr
  filter_upwards with z
  dsimp only [Pi.sub_apply, Pi.add_apply]
  ring

private theorem lag_pair_second_integrable :
    Integrable (fun z : ℝ × ℝ =>
      z.1 ^ (2 : ℕ) * (criticalAbelLogProfile (z.2 + z.1) * criticalAbelLogProfile z.2))
      (volume.prod volume) := by
  have h := (measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)).integrable_comp_of_integrable
    pair_second_integrable
  apply h.congr
  filter_upwards with z
  dsimp only [Function.comp_apply]
  rw [add_sub_cancel_right, add_comm z.1 z.2]
  ring

/-- Absolute admission of the complete quadratic lag moment. -/
theorem integrable_criticalAbelLogAutocorrelation_second :
    Integrable (fun u : ℝ => u ^ (2 : ℕ) * criticalAbelLogAutocorrelation u) := by
  have h := lag_pair_second_integrable.integral_prod_left
  simpa only [criticalAbelLogAutocorrelation, integral_const_mul] using h

private theorem translated_profile_second (t : ℝ) :
    (∫ u : ℝ, u ^ (2 : ℕ) * criticalAbelLogProfile (t + u)) =
      (∫ s : ℝ, s ^ (2 : ℕ) * criticalAbelLogProfile s) +
        2 * t * (divisorHarmonicBoundary / 3) := by
  have hshift := integral_add_left_eq_self (μ := volume)
    (fun s : ℝ => (s - t) ^ (2 : ℕ) * criticalAbelLogProfile s) t
  simp only [add_sub_cancel_left] at hshift
  rw [hshift]
  have hfun : (fun s : ℝ => (s - t) ^ (2 : ℕ) * criticalAbelLogProfile s) =
      fun s => s ^ (2 : ℕ) * criticalAbelLogProfile s -
        (2 * t) * (s * criticalAbelLogProfile s) +
          t ^ (2 : ℕ) * criticalAbelLogProfile s := by funext s; ring
  have hs : Integrable (fun s : ℝ => s ^ (2 : ℕ) * criticalAbelLogProfile s -
      (2 * t) * (s * criticalAbelLogProfile s)) :=
    profile_second_integrable.sub (profile_first_integrable.const_mul (2 * t))
  rw [hfun, integral_add hs
    (profile_integrable.const_mul (t ^ (2 : ℕ))),
    integral_sub profile_second_integrable (profile_first_integrable.const_mul (2 * t)),
    integral_const_mul, integral_const_mul, profile_mass, profile_first]
  ring

/-- Exact bilinear source sum rule: no absolute value or signed coordinate
is discarded, and the constant is the square of the actual first moment. -/
theorem criticalAbelLogAutocorrelation_second_moment :
    (∫ u : ℝ, u ^ (2 : ℕ) * criticalAbelLogAutocorrelation u) =
      -2 * (divisorHarmonicBoundary / 3) ^ (2 : ℕ) := by
  have hswap := integral_integral_swap
    (f := fun u t : ℝ => u ^ (2 : ℕ) *
      (criticalAbelLogProfile (t + u) * criticalAbelLogProfile t))
    lag_pair_second_integrable
  simp only [integral_const_mul] at hswap
  change (∫ u : ℝ, u ^ (2 : ℕ) *
    (∫ t : ℝ, criticalAbelLogProfile (t + u) * criticalAbelLogProfile t)) = _
  rw [hswap]
  have hinner (t : ℝ) :
      (∫ u : ℝ, u ^ (2 : ℕ) *
        (criticalAbelLogProfile (t + u) * criticalAbelLogProfile t)) =
      ((∫ s : ℝ, s ^ (2 : ℕ) * criticalAbelLogProfile s) +
        2 * t * (divisorHarmonicBoundary / 3)) * criticalAbelLogProfile t := by
    simp_rw [← mul_assoc]
    rw [integral_mul_const, translated_profile_second]
  simp_rw [hinner]
  have hfun : (fun t : ℝ =>
      ((∫ s : ℝ, s ^ (2 : ℕ) * criticalAbelLogProfile s) +
        2 * t * (divisorHarmonicBoundary / 3)) * criticalAbelLogProfile t) =
      fun t => (∫ s : ℝ, s ^ (2 : ℕ) * criticalAbelLogProfile s) *
        criticalAbelLogProfile t +
        (2 * (divisorHarmonicBoundary / 3)) * (t * criticalAbelLogProfile t) := by
    funext t
    ring
  rw [hfun, integral_add (profile_integrable.const_mul _)
    (profile_first_integrable.const_mul _), integral_const_mul, integral_const_mul,
    profile_mass, profile_first]
  ring

/-- Signed autocorrelation is even, by exact translation of both heads. -/
theorem criticalAbelLogAutocorrelation_neg (u : ℝ) :
    criticalAbelLogAutocorrelation (-u) = criticalAbelLogAutocorrelation u := by
  have h := integral_add_right_eq_self (μ := volume)
    (fun t : ℝ => criticalAbelLogProfile (t + -u) * criticalAbelLogProfile t) u
  simp only [add_neg_cancel_right] at h
  rw [criticalAbelLogAutocorrelation, criticalAbelLogAutocorrelation, ← h]
  apply integral_congr_ae
  filter_upwards with t
  ring

/-- The actual source necessarily has a negative signed correlation at a
positive lag. Pointwise correlation positivity is therefore unavailable. -/
theorem exists_criticalAbelLogAutocorrelation_negative :
    ∃ u : ℝ, 0 < u ∧ criticalAbelLogAutocorrelation u < 0 := by
  have hneg : ∃ u : ℝ, criticalAbelLogAutocorrelation u < 0 := by
    by_contra h
    have hnonneg : ∀ u : ℝ, 0 ≤ criticalAbelLogAutocorrelation u := by
      simpa only [not_exists, not_lt] using h
    have hi := integral_nonneg (μ := volume)
      (f := fun u : ℝ => u ^ (2 : ℕ) * criticalAbelLogAutocorrelation u) (fun u : ℝ =>
      mul_nonneg (sq_nonneg u) (hnonneg u))
    rw [criticalAbelLogAutocorrelation_second_moment] at hi
    have hpos : 0 < (divisorHarmonicBoundary / 3) ^ (2 : ℕ) := by
      exact pow_pos (div_pos divisorHarmonicBoundary_pos (by norm_num)) 2
    linarith
  obtain ⟨u, hu⟩ := hneg
  have hzero : 0 ≤ criticalAbelLogAutocorrelation 0 := by
    unfold criticalAbelLogAutocorrelation
    apply integral_nonneg
    intro t
    change 0 ≤ criticalAbelLogProfile (t + 0) * criticalAbelLogProfile t
    simpa only [add_zero, ← sq] using sq_nonneg (criticalAbelLogProfile t)
  rcases lt_trichotomy u 0 with h | h | h
  · refine ⟨-u, neg_pos.mpr h, ?_⟩
    rwa [criticalAbelLogAutocorrelation_neg]
  · subst u
    exact (not_lt_of_ge hzero hu).elim
  · exact ⟨u, h, hu⟩

end RHTower
