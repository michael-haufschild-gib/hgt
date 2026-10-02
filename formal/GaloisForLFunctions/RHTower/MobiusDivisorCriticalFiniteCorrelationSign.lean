import GaloisForLFunctions.RHTower.MobiusDivisorCriticalSourceAutocorrelation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Negative correlation at an original finite source cutoff

An exact finite integration-by-parts balance transfers the actual negative
boundary autocorrelation to a negative critically weighted finite prefix.
The endpoint term is retained. No improper critical-energy admission or
decay premise is used. Thus pointwise positivity cannot replace cumulative
signed-correlation control in route SZ.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

private theorem source_zero {t : ℝ} (ht : t ≤ 0) :
    criticalAbelLogProfile t = 0 := by
  have hx : Real.exp t ≤ 1 := by simpa using Real.exp_le_exp.mpr ht
  simp only [criticalAbelLogProfile, criticalContinuousAbel_eq_zero_le_one hx, mul_zero]

private theorem source_continuous : Continuous criticalAbelLogProfile := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  let T : ℝ := max 0 t + 1
  have hT : 0 ≤ T := by dsimp [T]; linarith [le_max_left (0 : ℝ) t]
  have htT : t < T := by dsimp [T]; linarith [le_max_right (0 : ℝ) t]
  have hz : ContinuousOn criticalAbelLogProfile (Iic (0 : ℝ)) :=
    (continuousOn_congr (fun y hy => source_zero hy)).mpr continuousOn_const
  have hc := hz.union_of_isClosed (continuousOn_criticalAbelLogProfile hT)
    isClosed_Iic isClosed_Icc
  have hsub : Iio T ⊆ Iic (0 : ℝ) ∪ Icc 0 T := by
    intro y hy
    by_cases hy0 : y ≤ 0
    · exact Or.inl hy0
    · exact Or.inr ⟨(lt_of_not_ge hy0).le, hy.le⟩
  exact (hc t (hsub htT)).continuousAt
    (Filter.mem_of_superset (Iio_mem_nhds htT) hsub)

/-- Critically weighted prefix of the actual boundary source product. -/
def criticalAbelExponentialCorrelationPrefix (lag cutoff : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..cutoff,
    Real.exp t * (criticalAbelLogProfile (t + lag) * criticalAbelLogProfile t)

private theorem kernel_continuous (lag : ℝ) :
    Continuous (fun t : ℝ =>
      Real.exp t * (criticalAbelLogProfile (t + lag) * criticalAbelLogProfile t)) :=
  Real.continuous_exp.mul
    ((source_continuous.comp (continuous_id.add_const lag)).mul source_continuous)

private theorem prefix_deriv (lag t : ℝ) :
    HasDerivAt (criticalAbelExponentialCorrelationPrefix lag)
      (Real.exp t * (criticalAbelLogProfile (t + lag) * criticalAbelLogProfile t)) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((kernel_continuous lag).intervalIntegrable 0 t)
    (kernel_continuous lag).aestronglyMeasurable.stronglyMeasurableAtFilter
    (kernel_continuous lag).continuousAt

/-- Exact finite balance, retaining the original cutoff and endpoint. -/
theorem criticalAbelCorrelationPrefix_boundary_balance (lag cutoff : ℝ) :
    (∫ t in (0 : ℝ)..cutoff,
      criticalAbelLogProfile (t + lag) * criticalAbelLogProfile t) =
      Real.exp (-cutoff) * criticalAbelExponentialCorrelationPrefix lag cutoff +
        ∫ t in (0 : ℝ)..cutoff,
          Real.exp (-t) * criticalAbelExponentialCorrelationPrefix lag t := by
  have he (t : ℝ) : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t := by
    simpa using ((hasDerivAt_id t).neg.exp)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := cutoff) (fun t _ => he t) (fun t _ => prefix_deriv lag t)
    (((Real.continuous_exp.comp continuous_id.neg).neg).intervalIntegrable 0 cutoff)
    ((kernel_continuous lag).intervalIntegrable 0 cutoff)
  have hcancel (t : ℝ) : Real.exp (-t) *
      (Real.exp t * (criticalAbelLogProfile (t + lag) * criticalAbelLogProfile t)) =
        criticalAbelLogProfile (t + lag) * criticalAbelLogProfile t := by
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have hzero : criticalAbelExponentialCorrelationPrefix lag 0 = 0 := by
    simp only [criticalAbelExponentialCorrelationPrefix, intervalIntegral.integral_same]
  simpa only [hcancel, hzero, mul_zero, sub_zero, neg_mul,
    intervalIntegral.integral_neg, sub_neg_eq_add] using h

/-- A finite critically weighted source correlation is strictly negative.
The proof uses the admitted boundary correlation, not a critical tail limit. -/
theorem exists_criticalAbelExponentialCorrelationPrefix_negative :
    ∃ lag cutoff : ℝ, 0 < lag ∧ 0 < cutoff ∧
      criticalAbelExponentialCorrelationPrefix lag cutoff < 0 := by
  obtain ⟨lag, hlag, hnegative⟩ := exists_criticalAbelLogAutocorrelation_negative
  by_contra h
  have hprefix : ∀ T : ℝ, 0 ≤ T →
      0 ≤ criticalAbelExponentialCorrelationPrefix lag T := by
    intro T hT
    by_cases hT0 : T = 0
    · subst T
      simp only [criticalAbelExponentialCorrelationPrefix, intervalIntegral.integral_same, le_refl]
    · by_contra hn
      exact h ⟨lag, T, hlag, lt_of_le_of_ne hT (Ne.symm hT0), lt_of_not_ge hn⟩
  have hnonneg (T : ℝ) (hT : 0 ≤ T) :
      0 ≤ ∫ t in (0 : ℝ)..T,
        criticalAbelLogProfile (t + lag) * criticalAbelLogProfile t := by
    rw [criticalAbelCorrelationPrefix_boundary_balance]
    apply add_nonneg (mul_nonneg (Real.exp_pos _).le (hprefix T hT))
    apply intervalIntegral.integral_nonneg hT
    intro t ht
    exact mul_nonneg (Real.exp_pos _).le (hprefix t ht.1)
  have hlim := intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    (integrable_criticalAbelLogProfile_translated_product lag).integrableOn tendsto_id
  have hfull : (∫ t in Ioi (0 : ℝ),
      criticalAbelLogProfile (t + lag) * criticalAbelLogProfile t) =
        criticalAbelLogAutocorrelation lag := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have ht0 : t ≤ 0 := le_of_not_gt ht
    rw [source_zero ht0, mul_zero]
  rw [hfull] at hlim
  have hnon : 0 ≤ criticalAbelLogAutocorrelation lag := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact hnonneg T hT
  exact (not_lt_of_ge hnon hnegative)

/-- Literal complete source pairing at the original finite logarithmic cutoff. -/
def criticalAbelCompleteClockPairing (lag cutoff : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..cutoff,
    (criticalContinuousAbel (Real.exp (t + lag)) / Real.exp (t + lag)) *
      (criticalContinuousAbel (Real.exp t) / Real.exp t)

private theorem original_head_eq_profile (t : ℝ) :
    criticalContinuousAbel (Real.exp t) / Real.exp t =
      Real.exp (t / 2) * criticalAbelLogProfile t := by
  rw [criticalAbelLogProfile, ← mul_assoc, ← Real.exp_add,
    show t / 2 + -(3 / 2 : ℝ) * t = -t by ring, Real.exp_neg]
  ring

/-- Exact change of normalization; no cutoff is moved. -/
theorem criticalAbelCompleteClockPairing_eq_prefix (lag cutoff : ℝ) :
    criticalAbelCompleteClockPairing lag cutoff =
      Real.exp (lag / 2) * criticalAbelExponentialCorrelationPrefix lag cutoff := by
  unfold criticalAbelCompleteClockPairing criticalAbelExponentialCorrelationPrefix
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [original_head_eq_profile, original_head_eq_profile]
  have he : Real.exp ((t + lag) / 2) * Real.exp (t / 2) =
      Real.exp (lag / 2) * Real.exp t := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp ((t + lag) / 2) * Real.exp (t / 2)) *
        (criticalAbelLogProfile (t + lag) * criticalAbelLogProfile t) := by ring
    _ = _ := by rw [he]; ring

/-- Original finite-cutoff correlations of the complete actual Abel source
cannot all be nonnegative. Cumulative signed control is still required. -/
theorem exists_criticalAbelCompleteClockPairing_negative :
    ∃ lag cutoff : ℝ, 0 < lag ∧ 0 < cutoff ∧
      criticalAbelCompleteClockPairing lag cutoff < 0 := by
  obtain ⟨lag, cutoff, hlag, hcutoff, h⟩ :=
    exists_criticalAbelExponentialCorrelationPrefix_negative
  refine ⟨lag, cutoff, hlag, hcutoff, ?_⟩
  rw [criticalAbelCompleteClockPairing_eq_prefix]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) h

end RHTower
